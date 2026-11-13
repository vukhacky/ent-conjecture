"""Exact moments and certified one-dimensional integration for the entropy proof."""
from fractions import Fraction as Q
from math import comb, factorial, prod
import sympy as s
from flint import arb, ctx
ctx.prec=192

def compositions(total,n):
    if n==1:
        yield (total,)
    else:
        for k in range(total+1):
            for rest in compositions(total-k,n-1):
                yield (k,)+rest

def moment(n,k,w):
    return s.Add(*(s.Rational(3**k*factorial(2*k),
                    prod(factorial(2*a+1) for a in ex))
                  *s.prod(z**a for z,a in zip(w,ex))
                  for ex in compositions(k,n)))

def piece(n,k):
    d=n-1
    return [sum((-1)**j*comb(n,j)*comb(d,i)*(k-j)**(d-i)
                for j in range(k+1)) for i in range(d+1)]

def der(p): return [j*p[j] for j in range(1,len(p))]

def ev(p,x):
    z=arb(0)
    for c in reversed(p):z=z*x+c
    return z

def entropy_standard(n,bits=15):
    m=2**bits;den=factorial(n-1)
    value=2*(arb(n-1)/(n*n)+arb(den).log()/n)/den
    for k in range(1,(n+1)//2):
        p=piece(n,k);p1=der(p);p2=der(p1)
        cells=m//2 if n%2 and k==n//2 else m
        for j in range(cells):
            x=arb(2*j+1,1)/(2*m);mid=arb(2*j+1)/(2*m)
            f=ev(p,x)/den; f1=ev(p1,x)/den; f2=ev(p2,x)/den
            assert f>0
            gpp=-f2*(f.log()+1)-f1*f1/f
            fm=ev(p,mid)/den
            value+=2*(-fm*fm.log()/m+arb(0,1)*gpp.abs_upper()/(24*m**3))
    return value+(arb(12)/n).log()/2

def partition(cs,bits=17,R=8):
    d=len(cs);c=list(map(arb,cs));p=[arb(0)]*(2*d+1)
    for j,v in enumerate(c):p[2*j+2]=v
    p1=der(p);p2=der(p1)
    tail=(2*d)*(2*d-1)*c[-1]*R**(2*d-2)
    for j,v in enumerate(c[:-1]):
        if Q(cs[j])<0:tail+=(2*j+2)*(2*j+1)*v*R**(2*j)
    assert tail>0 and ev(p1,arb(R))>0 and c[-1]>0
    m=2**bits;step=arb(R)/m;value=arb(0)
    for j in range(m):
        x=arb(2*j+1,1)*R/(2*m);mid=arb(2*j+1)*R/(2*m)
        phi=ev(p,x);d1=ev(p1,x);d2=ev(p2,x)
        gpp=(d1*d1-d2)*(-phi).exp()
        value+=2*((-ev(p,mid)).exp()*step+arb(0,1)*gpp.abs_upper()*step**3/24)
    return value+arb(1,1)*(-ev(p,arb(R))).exp()/ev(p1,arb(R))

def hessian(n,bits=14):
    m=2**bits;df=factorial(n-1);dg=factorial(n-3)
    total=2*(arb(n-1)/(n*n)+arb(df).log()/n)/df
    for k in range(1,(n+1)//2):
        p=piece(n,k);g=piece(n-2,k-1)
        p1=der(p);p2=der(p1);g1=der(g);g2=der(g1)
        cells=m//2 if n%2 and k==n//2 else m
        for j in range(cells):
            x=arb(2*j+1,1)/(2*m);mid=arb(2*j+1)/(2*m)
            f=ev(p,x)/df;f1=ev(p1,x)/df;f2=ev(p2,x)/df
            a=ev(g,x)/dg-f;a1=ev(g1,x)/dg-f1;a2=ev(g2,x)/dg-f2
            assert f>0
            second=a2*f.log()+2*a1*f1/f+a*(f2/f-(f1/f)**2)
            fm=ev(p,mid)/df;am=ev(g,mid)/dg-fm
            total+=2*(am*fm.log()/m+arb(0,1)*second.abs_upper()/(24*m**3))
    return 1-n*total
