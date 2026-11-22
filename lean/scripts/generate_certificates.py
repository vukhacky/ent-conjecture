#!/usr/bin/env python3
"""Generate the exact integer coefficients and Lean sources for the finite spline cells."""

import argparse
import csv
import hashlib
import io
from functools import lru_cache
from math import comb
from pathlib import Path
from string import Template
from tempfile import NamedTemporaryFile

from flint import fmpz_poly


PROJECT = Path(__file__).resolve().parents[1]
CERTIFICATES = PROJECT / "certificates"
MANIFEST = CERTIFICATES / "modules.tsv"
SHIFT = fmpz_poly([1, 1])
FIELDS = ("family", "module", "n", "first_k", "last_k", "blank_lines_before_end", "sha256")


@lru_cache(maxsize=1)
def spline_pieces(n):
    """Return the truncated-power splines Pₙ,ₖ(s) on the positive half of the support."""
    degree = n - 1
    monomial = fmpz_poly([0] * degree + [1])
    pieces = [monomial]
    for k in range(1, (n + 1) // 2):
        pieces.append(pieces[-1](SHIFT) + (-1)**k * comb(n, k) * monomial)
    return pieces


def bernstein_numerators(poly):
    """Coefficients of (1+t)^d poly(t/(1+t)), in increasing powers of t."""
    degree = poly.degree()
    reverse = fmpz_poly(list(reversed(poly.coeffs())))
    shifted_reverse = reverse(SHIFT)
    return [shifted_reverse[degree - j] for j in range(degree + 1)]


def cell_values(n, k, family):
    p = spline_pieces(n)[k]
    p1 = p.derivative()
    p2 = p1.derivative()
    p3 = p2.derivative()
    r = n**3 * (p**2 * p3 - 3 * p * p1 * p2 + 2 * p1**3) - 56 * fmpz_poly([n-2*k, -2]) * p**3
    degree = r.degree()
    half = 2*k + 1 == n
    # On the last half cell, q(s) = 2^d r(s/2).
    q = fmpz_poly([r[j] << (degree-j) for j in range(degree+1)]) if half else r
    b = bernstein_numerators(q)
    if degree != 3*n - 2 or min(b) < 0 or max(b) <= 0:
        raise ArithmeticError(f"Degree or Bernstein sign check failed at n={n}, k={k}")

    p_norm = sum(map(abs, p))
    d = len(p)
    # Bounds for the packed evaluation identities in the corresponding Lean structures.
    curvature_bound = (3*d+1) * (2*d+1) * p_norm**3 * (6*n**3*d**3 + 56*(n+2*k) + 112)
    bernstein_bound = sum(map(abs, b)) << degree
    values = dict(tag=f"n{n}k{k}", n=n, k=k, degree=degree, half=str(half).lower(),
                  pCoeffs=", ".join(map(str, p)), bernsteinNumerators=", ".join(map(str, b)))
    if family in ("KroneckerSplineData", "KroneckerDirectData"):
        p_bound = p_norm + (k+1)**n * 2**(2*n-1)
        values["PBaseBits"] = p_bound.bit_length()
    if family == "KroneckerDirectData":
        q_bound = curvature_bound << (degree if half else 0)
        evaluation_bound = (degree+1) * q_bound + bernstein_bound
        values["UBits"] = evaluation_bound.bit_length() - int(half)
    else:
        values["rCoeffs"] = ", ".join(map(str, r))
        values["transformedCoeffs"] = values["rCoeffs"] if q is r else ", ".join(map(str, q))
        values["RBaseBits"] = (sum(map(abs, r)) + curvature_bound).bit_length()
        values["BBaseBits"] = (sum(map(abs, q)) + bernstein_bound).bit_length()
    return values


@lru_cache(maxsize=4)
def load_template(family):
    text = (CERTIFICATES / f"{family}.lean.in").read_text(encoding="utf-8")
    header, rest = text.split("-- BEGIN CELL\n")
    cell, footer = rest.split("-- END CELL\n")
    return header, Template(cell), footer


def module_bytes(row):
    n = int(row["n"])
    first, last = int(row["first_k"]), int(row["last_k"])
    family = row["family"]
    if not 0 <= first <= last < (n+1)//2:
        raise ValueError(f"Invalid cell range for {row['module']}")
    header, template, footer = load_template(family)
    gap = "\n" * (2 if family == "KroneckerDirectData" else 3)
    cells = [template.substitute(cell_values(n, k, family)) for k in range(first, last+1)]
    trailing_gap = "\n" * int(row["blank_lines_before_end"])
    return (header + gap.join(cells) + trailing_gap + footer).encode("utf-8")


def digest(data):
    return hashlib.sha256(data).hexdigest()


def write_atomic(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    with NamedTemporaryFile(dir=path.parent, prefix=path.name + ".", delete=False) as out:
        temporary = Path(out.name)
        try:
            out.write(data)
            out.close()
            temporary.chmod(0o644)
            temporary.replace(path)
        finally:
            temporary.unlink(missing_ok=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=PROJECT, help="Lean project directory to populate")
    parser.add_argument("--dimension", type=int, help="generate a single dimension from the manifest")
    parser.add_argument("--verify-only", action="store_true",
                        help="recompute and compare every selected module with its SHA-256, without writing")
    parser.add_argument("--new-manifest", type=Path,
                        help="write proposed replacement hashes to a new TSV without changing any Lean sources")
    args = parser.parse_args()
    if args.new_manifest and (args.verify_only or args.dimension is not None):
        parser.error("--new-manifest requires the full set of modules")
    if args.new_manifest and args.new_manifest.exists():
        parser.error("--new-manifest requires a new file for review")
    with MANIFEST.open(encoding="utf-8", newline="") as file:
        reader = csv.DictReader(file, delimiter="\t")
        if tuple(reader.fieldnames) != FIELDS:
            raise ValueError(f"Unexpected column headings in {MANIFEST}")
        rows = [row for row in reader if args.dimension is None or int(row["n"]) == args.dimension]
    if not rows:
        parser.error("the specified dimension has no modules in the manifest")
    total_bytes = total_cells = 0
    for row in sorted(rows, key=lambda record: (int(record["n"]), record["module"], record["family"])):
        relative = Path("ENT", "Pilot", row["family"], row["module"] + ".lean")
        path = args.output / relative
        data = module_bytes(row)
        generated_hash = digest(data)
        if args.new_manifest:
            row["sha256"] = generated_hash
        elif generated_hash != row["sha256"]:
            raise ValueError(f"Generated SHA-256 mismatch: {relative}")
        if not (args.verify_only or args.new_manifest):
            if path.exists():
                if digest(path.read_bytes()) != row["sha256"]:
                    raise ValueError(f"Existing file differs: {path}. Move it aside before regenerating.")
            else:
                write_atomic(path, data)
        total_bytes += len(data)
        total_cells += int(row["last_k"]) - int(row["first_k"]) + 1
    if args.new_manifest:
        proposed = io.StringIO()
        writer = csv.DictWriter(proposed, fieldnames=FIELDS, delimiter="\t", lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)
        write_atomic(args.new_manifest, proposed.getvalue().encode("utf-8"))
        print(f"Proposed SHA-256 manifest written to {args.new_manifest}.")
    else:
        print(f"Verified {len(rows)} modules, {total_cells} cells, {total_bytes} bytes.")


if __name__ == "__main__":
    main()
