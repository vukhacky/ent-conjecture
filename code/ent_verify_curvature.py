"""Exact spline certificate for entropy maximization of cube projections.

Default claim: (-log q_n)'''(x) >= 7*x/n for 7 <= n <= 255 and
0 < x < sqrt(n), where q_n is the density of n**(-1/2) sum U_i,
with independent U_i uniform on [-1, 1].

All sign decisions use integers. No sampling, optimization, or floating-point
arithmetic is used. The JSON output is deterministic for a fixed range.
Requires python-flint; run `python3 ent_verify_curvature.py --help`.
"""

import argparse
import hashlib
import json
from math import comb
from pathlib import Path

from flint import fmpz_poly


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def bernstein_numerators(polynomial):
    """Return binom(d,j) times the degree-d Bernstein coefficients."""
    degree = polynomial.degree()
    require(degree >= 0, "The zero polynomial requires separate handling")
    reverse = fmpz_poly([polynomial[degree-j] for j in range(degree+1)])
    shifted = reverse(fmpz_poly([1, 1]))
    return [int(shifted[degree-j]) for j in range(degree+1)]


def direct_piece(n, k):
    """Independent truncated-power construction, for small-n cross-checks."""
    return sum(((-1)**j * comb(n, j) * fmpz_poly([k-j, 1])**(n-1)
                for j in range(k+1)), fmpz_poly([]))


def crosscheck_basis(polynomial, numerators):
    """Check the fast basis transform against its defining binomial sums."""
    degree = polynomial.degree()
    direct = [sum(comb(degree-i, j-i)*int(polynomial[i])
                  for i in range(j+1)) for j in range(degree+1)]
    require(direct == numerators, "Independent Bernstein transform failed")


def summarize_ranges(rows):
    summaries = []
    for label, lo, hi in [('core_with_overlap', 7, 150),
                          ('quantitative_extension', 151, 255)]:
        selected = [row for row in rows if lo <= row['n'] <= hi]
        if selected:
            summaries.append(dict(
                label=label, first=selected[0]['n'], last=selected[-1]['n'],
                cells=sum(row['cells'] for row in selected),
                coefficients=sum(row['coefficients'] for row in selected),
                zero_coefficients=sum(row['zero_coefficients'] for row in selected),
                passed=all(row['passed'] for row in selected),
            ))
    return summaries


def certify(first=7, last=255, constant=7):
    require(7 <= first <= last, "Require 7 <= first <= last")
    require(constant > 0, "The curvature constant must be positive")
    digest = hashlib.sha256()
    cells = coefficients = zero_coefficients = crosschecked_cells = 0
    maximum_degree = 0
    rows = []
    for n in range(first, last+1):
        degree = n-1
        piece = fmpz_poly([0]*degree+[1])
        row_cells = row_coefficients = row_zeros = 0
        for k in range((n+1)//2):
            if n <= 12:
                require(piece == direct_piece(n, k),
                        f"Independent spline construction failed: n={n}, k={k}")
            p1 = piece.derivative()
            p2 = p1.derivative()
            p3 = p2.derivative()
            numerator = piece*piece*p3-3*piece*p1*p2+2*p1**3
            target = (n**3*numerator
                      -8*constant*fmpz_poly([n-2*k, -2])*piece**3)
            if n % 2 and k == n//2:
                # Positive multiple of target(s/2), on the last half cell.
                d = target.degree()
                target = fmpz_poly([target[j]*2**(d-j) for j in range(d+1)])
            values = bernstein_numerators(target)
            require(min(values) >= 0 and max(values) > 0,
                    f"Bernstein certificate failed: n={n}, k={k}")
            if n <= 12:
                crosscheck_basis(target, values)
                crosschecked_cells += 1
            digest.update((str(n)+':'+str(k)+':'+','.join(map(str, values))+'\n').encode())
            row_cells += 1
            row_coefficients += len(values)
            row_zeros += values.count(0)
            maximum_degree = max(maximum_degree, target.degree())
            # P_{n,k+1}(s)=P_{n,k}(s+1)+(-1)^(k+1) binom(n,k+1) s^(n-1).
            piece = (piece(fmpz_poly([1, 1]))
                     + fmpz_poly([0]*degree+[(-1)**(k+1)*comb(n, k+1)]))
        cells += row_cells
        coefficients += row_coefficients
        zero_coefficients += row_zeros
        rows.append(dict(n=n, cells=row_cells, coefficients=row_coefficients,
                         zero_coefficients=row_zeros, passed=True))
    return dict(
        claim="(-log q_n)'''(x) >= constant*x/n on 0<x<sqrt(n)",
        normalization="U_i uniform on [-1,1]; q_n is the density of sum(U_i)/sqrt(n)",
        arithmetic="exact integers; Bernstein numerators multiplied by positive binomial coefficients",
        first=first, last=last, constant=constant, cells=cells,
        coefficients=coefficients, zero_coefficients=zero_coefficients,
        positive_coefficients=coefficients-zero_coefficients,
        maximum_degree=maximum_degree,
        independent_crosscheck_cells=crosschecked_cells,
        certificate_sha256=digest.hexdigest(), passed=True,
        ranges=summarize_ranges(rows), dimensions=rows,
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--first', type=int, default=7)
    parser.add_argument('--last', type=int, default=255)
    parser.add_argument('--constant', type=int, default=7)
    parser.add_argument('--output', type=Path, default=Path('curvature_results.json'))
    args = parser.parse_args()
    result = certify(args.first, args.last, args.constant)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    summary = {k:v for k,v in result.items() if k != 'dimensions'}
    print(json.dumps(summary, indent=2, sort_keys=True), flush=True)


if __name__ == '__main__':
    main()
