"""Exact arithmetic for the tilted-variance lemma and large-n Fourier closure.

The finite checks verify the displayed polynomial coefficients, the scalar
base at degree 21, and the Fourier closure at n=256. The accompanying proof
supplies the monotonicity arguments extending these checks to all larger
indices and dimensions. No floating-point number enters a sign decision.
"""
from fractions import Fraction as Q
from math import factorial
from pathlib import Path
import json
import sympy as sp

if not __debug__:
    raise RuntimeError("The certificate requires Python assertions. Run without -O.")


def langevin_certificate():
    # Coefficients of 32G(t), listed as (power of t, coefficient),
    # multiplying sinh(bt) for even powers and cosh(bt) for odd powers.
    terms = {
        7: [(4,5),(0,27),(1,-27)],
        5: [(4,-35),(2,-324),(0,-189),(7,-20),(3,324),(1,135)],
        3: [(4,1401),(2,1620),(0,567),(7,60),(5,-1296),(3,-972),(1,-243)],
        1: [(6,-1728),(4,-4063),(2,-3240),(0,-945),(7,1688),(5,1296),(3,648),(1,135)]}
    # Independently verify the hyperbolic identity as a Laurent polynomial.
    t, z = sp.symbols('t z')
    sh = (z-1/z)/2; ch = (z+1/z)/2
    G = 10*t**4*sh**4*(sh**3-t**3*ch)-54*(t*ch-sh)*(sh**2-t**2)**3
    rhs = sum(co*t**k*((z**b-z**(-b))/2 if k%2==0 else (z**b+z**(-b))/2)
              for b, ts in terms.items() for k,co in ts)
    assert sp.expand(32*G-rhs) == 0
    def fall(N, k):
        return factorial(N)//factorial(N-k) if N >= k else 0
    def coef(N):
        return sum(c*fall(N,k)*b**(N-k) for b, ts in terms.items()
                   for k,c in ts if N >= k)
    assert all(coef(N) == 0 for N in range(1, 16, 2))
    assert coef(17) > 0 and coef(19) > 0
    N = 21
    leading = Q(5,2)*fall(N,4)*7**(N-4)
    negative = sum(-c*fall(N,k)*b**(N-k) for b, ts in terms.items()
                   for k,c in ts if c < 0 and b < 7)
    assert leading > negative
    # For odd N>=21 each negative/leading ratio decreases under N->N+2.
    assert Q(25,49)*Q((N-2)*(N-3), (N-5)*(N-6)) < 1
    # The 7^N coefficient exceeds (5/2)*(N)_4*7^(N-4) for N>=17.
    # Shift N=17+z: all coefficients of the difference polynomial are positive.
    x = sp.Symbol('x')
    shifted_n = 17 + x
    difference = sum(c * sp.FallingFactorial(shifted_n, k) * 7**(4-k)
                     for k, c in terms[7])
    difference -= sp.Rational(5,2) * sp.FallingFactorial(shifted_n, 4)
    polynomial = sp.Poly(difference, x)
    shift = [polynomial.nth(k) for k in range(polynomial.degree()+1)]
    assert shift == [50190, 27784, sp.Rational(7195,2), 155, sp.Rational(5,2)]
    assert all(v > 0 for v in shift)
    return {'hyperbolic_identity': True, 'coeff_17': coef(17), 'coeff_19': coef(19),
            'shift_coefficients': [str(v) for v in shift],
            'tail_margin_at_21': str(leading-negative), 'pass': True}


def fourier_certificate():
    n = 256; c = Q(31,10); pi_lower = Q(157,50)
    # Machin's formula and alternating arctangent bounds imply this pi bound.
    assert 16*(Q(1,5)-Q(1,375))-4*Q(1,239) > pi_lower
    m = {0: Q(2*n-3, 2*(n-3))}
    for k in range(1,7):
        m[2*k] = Q((2*k-1)*n,n-2*k-2)*m[2*k-2]
    T0=Q(64,n**3)*(15+m[6]); T4=Q(256,n**4)*(10395+m[12])
    T6=Q(64,n**3)*(10395+m[12])
    A=1-Q(3,7*n)-m[6]/(12*n)-T0
    B=Q(1,2)-Q(21,4*n)-m[10]/(216*n)-T4/6
    C=3*m[2]/A+Q(8,n)*(m[4]/(6*A))**2
    assert A > 0 and B > 0 and C < c and n > 4*c
    I=Q(2,5); correction=Q(11,10)
    assert I**2 > 2*c**7/(105**2*pi_lower)
    rb=sum(co*2*c**((j+2)//2)/((j+1)*(j+3))
           for j,co in [(6,Q(11,60)),(8,Q(1,42)),(10,Q(1,216))])
    assert correction**2 > rb**2*2*c/pi_lower
    x=(c/2+c*c/4)/n
    assert 0 < x < 1
    R=sum(x**j/factorial(j) for j in range(1,5))+x**5/factorial(5)/(1-x/6)
    H=(167-21*c)/4+m[12]/216*(1-c*Q(n-14,11*n))+correction
    F=(5-c)/2-I*R-H/n-T6/6
    curvature=Q(54,5)*F/m[0]
    assert F > 0 and curvature > 7
    return {'threshold':n, 'comparison_c':str(c), 'A':str(A), 'B':str(B),
            'C':str(C), 'F':str(F), 'curvature_lower_bound':str(curvature),
            'curvature_display':float(curvature), 'pass':True}



if __name__ == '__main__':
    result = {'langevin': langevin_certificate(), 'fourier': fourier_certificate()}
    Path('large_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
