"""Octic entropy duals and averaged local bounds for ENT dimensions 5 and 6.

All decimal inputs are exact rationals. Algebraic inequalities use Fraction;
integrals use outward-rounded Arb balls. No mesh samples are treated as proofs:
the averaged derivative bound encloses every point of every integration cell.
"""
from fractions import Fraction as Q
from math import factorial
from pathlib import Path
import json
import sympy as s
from flint import arb, fmpq, fmpz_poly
from small_integrals import piece, ev, moment, entropy_standard, partition, hessian

PARAMETERS = {
    5: dict(cs=['.43346', '.01535', '-.001769', '.00017206'],
            lam=Q(1,100), slack=Q(1,200000), delta=Q(7,12500),
            radius=Q(29,1000), gamma=Q(29,500), M=Q(77,10), kappa=Q(27,1000)),
    6: dict(cs=['.44749', '.01001', '-.0006493', '.00007284'],
            lam=Q(19,2000), slack=Q(7,5000000), delta=Q(1,6000),
            radius=Q(7,400), gamma=Q(1,25), M=Q(13,2), kappa=Q(17,1000))
}


def averaged_bound(n, gamma, bits=11, subdivisions=32):
    """Enclose the upper Riemann integral M_n(gamma) defined in the manuscript."""
    g = fmpq(str(gamma)); mesh = 2**bits
    P = [piece(n,k) for k in range((n+1)//2)]
    N = []
    for cs in P:
        p = fmpz_poly(cs)
        p1 = p.derivative(); p2 = p1.derivative(); p3 = p2.derivative()
        N.append(list(p*p*p3-3*p*p1*p2+2*p1**3))

    def supremum(lo,hi):
        hi = min(hi,fmpq(n,2)); value = arb(0)
        if lo < 1:
            value = 2*(n-1)/arb(lo)**3
        for k in range(1,len(P)):
            a = max(lo,fmpq(k)); b = min(hi,fmpq(k+1),fmpq(n,2))
            if a >= b:
                continue
            width = (b-a)/subdivisions
            for j in range(subdivisions):
                x = arb(a+(j+fmpq(1,2))*width,width/2)-k
                p = ev(P[k],x)
                assert p > 0
                # Dividing by a point lower endpoint avoids unnecessary
                # interval dependency in the cube of a wide positive ball.
                upper = ev(N[k],x).abs_upper()/p.lower()**3
                value = value.max(upper)
        assert value.is_finite()
        return value.upper()

    # On [0,1/2], (1+gamma)t<1, so the entire contribution is exact.
    assert 0 <= g < 1
    result = 4*(n-1)/(arb(1)-arb(g))**3/(n*factorial(n-1)*arb(2)**n)
    for j in range(mesh//2,n*mesh//2):
        a = fmpq(j,mesh); b = fmpq(j+1,mesh)
        t = arb((a+b)/2,(b-a)/2)
        density = ev(P[j//mesh],t-j//mesh)/factorial(n-1)
        assert density > 0
        result += 2*density*t**3*supremum((1-g)*a,(1+g)*b)/mesh
    assert result.is_finite()
    return result


def certificate(n):
    par = PARAMETERS[n]
    c1,c2,c3,c4 = map(Q,par['cs'])
    A = 6*c2/5+18*c3+252*c4
    B = 48*c3/7+192*c4
    C = 252*c4/5
    D = 432*c4/5
    assert C > 0 and 0 < D < 2*C
    schur_margin = 2*(A-par['lam'])-max(4*C,3*B+4*C-4*D)
    assert schur_margin > 0
    f0 = sum(s.Rational(c)*moment(n,k+1,[s.Rational(1,n)]*n)
             for k,c in enumerate(par['cs']))
    entropy = entropy_standard(n)
    Z = partition(par['cs'])
    slack = Z.log()+arb(str(f0))-entropy
    assert slack < arb(str(par['slack']))
    exterior_margin = (par['lam']-Q(1,1000))*par['delta']-par['slack']
    assert exterior_margin > 0
    curv = hessian(n,bits=12)
    assert curv > arb(str(par['kappa']))
    average = averaged_bound(n,par['gamma'])
    assert average < arb(str(par['M']))
    r,g = par['radius'],par['gamma']
    assert g*g >= (n-1)*r*r and g < 1
    delta_ratio = Q(4,n)+2*r+r*r
    local_margin = par['kappa']/2-r*r/4-g*par['M']/(6*(n+1))-delta_ratio/1000
    assert local_margin > 0
    assert par['delta'] < Q(1,16*n*n)
    zbound = (1-3*n*par['delta']/20)**-2-1
    assert zbound < r*r
    return dict(n=n,potential=par['cs'],lambda_value=str(par['lam']),
                schur_margin=str(schur_margin),slack_ball=str(slack),
                slack_upper=str(par['slack']),delta_threshold=str(par['delta']),
                exterior_margin=str(exterior_margin),radius=str(r),gamma=str(g),
                average_ball=str(average),average_upper=str(par['M']),
                hessian_ball=str(curv),hessian_lower=str(par['kappa']),
                local_margin=str(local_margin),overlap_z_upper=str(zbound),
                pass_all=True)


if __name__ == '__main__':
    rows = []
    for n in [5,6]:
        row = certificate(n)
        rows.append(row)
        print(json.dumps(row),flush=True)
    Path('small56_results.json').write_text(json.dumps(rows,indent=2)+'\n')
