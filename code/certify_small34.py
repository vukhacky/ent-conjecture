"""Exact rational and 192-bit Arb certificates for the octic entropy duals in dimensions 3 and 4."""
from fractions import Fraction as Q
from math import comb
from pathlib import Path
import hashlib
import json
import sympy as s
from flint import arb
from small_integrals import moment, entropy_standard, partition

PARAMETERS = {
    3: ['0.345', '0.081', '-0.0226', '0.00221'],
    4: ['0.4065', '0.0301', '-0.00563', '0.000518'],
}
SLOPES = {3: Q(1,100), 4: Q(11,1000)}
SLACK_BOUNDS = {3: Q(9,100000), 4: Q(1,50000)}
THRESHOLDS = {3: Q(1,100), 4: Q(1,500)}


def polynomial_certificate(n):
    cs=PARAMETERS[n]; d=4; y=s.symbols('y:'+str(n))
    w=[sum(y[i:]) for i in range(n)]; S=sum(w)
    f0=sum(s.Rational(c)*moment(n,k+1,[s.Rational(1,n)]*n)
           for k,c in enumerate(cs))
    F=sum(s.Rational(c)*moment(n,k+1,w)*S**(d-k-1)
          for k,c in enumerate(cs))
    lam=s.Rational(str(SLOPES[n]))
    G=s.Poly(f0*S**d-F-lam*(sum(z*z for z in w)-S*S/n)*S**(d-2),y)
    assert all(c>0 for c in G.coeffs())
    assert len(G.terms())==comb(d+n-1,n-1)-n
    records=[{'powers':list(ex),'coefficient':str(co)} for ex,co in G.terms()]
    digest=hashlib.sha256(json.dumps(records,sort_keys=True).encode()).hexdigest()
    return f0, {'potential_degree':8,'homogeneous_weight_degree':d,'positive_coefficients':len(records),
                'minimum_coefficient':str(min(G.coeffs())),
                'sha256':digest,'coefficients':records}


def schur_certificate_four():
    c1,c2,c3,c4=map(Q,PARAMETERS[4])
    A=Q(6,5)*c2+18*c3+252*c4
    B=Q(48,7)*c3+192*c4
    C=Q(252,5)*c4
    D=Q(432,5)*c4
    lam=SLOPES[4]
    assert 0<D<2*C
    assert 2*(A-lam)>=max(4*C,3*B+4*C-4*D)
    # Independently verify the power-sum formula on the simplex.
    w=s.symbols('w:4'); S=sum(w)
    p=lambda k:sum(z**k for z in w)
    const=c1+3*c2+15*c3+105*c4
    expected=const*S**4-s.Rational(str(A))*p(2)*S**2 \
             +s.Rational(str(B))*p(3)*S+s.Rational(str(C))*p(2)**2 \
             -s.Rational(str(D))*p(4)
    actual=sum(s.Rational(c)*moment(4,k+1,w)*S**(3-k)
               for k,c in enumerate(PARAMETERS[4]))
    assert s.Poly(expected-actual,w).is_zero
    return {'method':'Schur concavity; two rational endpoint checks',
            'A':str(A),'B':str(B),'C':str(C),'D':str(D),
            'endpoint_zero_margin':str(2*(A-lam)-4*C),
            'endpoint_one_margin':str(2*(A-lam)-(3*B+4*C-4*D))}


def check_margins(checks):
    result={}
    for label,margin in checks:
        assert margin>0, (label,str(margin))
        result[label]=str(margin)
    return result


def local_three():
    r=1/arb(3).sqrt(); v=(4/arb(3).sqrt()).log()
    at=((1+r)/(1-r)).log()/2
    h=arb(7)/6+2*arb(2).log()-arb(3).log()/2-arb(3).sqrt()*at
    J=r*v+2*r-2*at; F2=J+2*r*(v+2)
    B=-2*r*h+2*J; C=12*r*h+arb(3)/2*J-arb(9)/2*F2
    e=h-v; K=4*h+v/2
    constants=check_margins([
        ('B+2r/3>.03',B+2*r/3-arb(3)/100),
        ('C>-10',C+10), ('C<0',-C), ('e>0',e),
        ('e<.027',arb(27)/1000-e), ('K>0',K), ('K<4',4-K)])
    rho=Q(1,10)
    # |d|<=.3u; 2|z_i|<=5rho/3; coefficient of p is in (0,.13).
    assert arb(3)/10-r/(1+(1-arb(str(rho*rho))).sqrt())>0
    assert Q(5,3)+Q(3,10)*rho<Q(17,10)
    assert 4*Q(27,1000)+4*Q(7,4)*Q(3,10)*rho*rho<Q(13,100)
    fourth=8+Q(144,35)*rho+Q(54,25)*rho**2+Q(243,10000)*rho**4
    assert fourth<9
    margin=Q(3,100)-Q(9,10)*rho**2-Q(27,250)*rho**4 \
           -Q(13,700)*rho-Q(153,200)*rho**3-Q(1,60)
    assert margin>0
    # delta<=.01 gives a_i>.48 and r>.52, hence rho²<=delta.
    assert Q(1,3)-Q(1,10)>Q(12,25)**2
    assert Q(1,3)>Q(13,25)**2
    # delta<=3rho²; entropy gap>=rho²/240.
    assert Q(1,720)>Q(1,1000)
    return {'radius':'1/10','local_delta':'1/100','primitive_slope':'1/60',
            'local_stability':'1/720','rational_margin':str(margin),
            'constant_margins':constants}


def local_four():
    # Interval integration on each complete cell; no unbounded endpoint is
    # integrated numerically. The outer entropy integral is explicit.
    M=2**16; J2=arb(0); J3=arb(0); hc=arb(0)
    for j in range(M):
        x=arb(2*j+1,1)/(2*M)
        q=arb(2)/3-x*x+x*x*x/2
        assert q>0
        V=-q.log(); J2+=(1-x)*V; J3+=V; hc+=2*q*V
    J2/=M; J3/=M; hc/=M
    v=arb(6).log(); h=hc+(v/4+arb(3)/16)/3
    alpha=arb(1)/4-h+2*J2
    C=12*h+8*J2-8*(J2+J3+v/2+arb(3)/4)
    e=h-J3; K=16*h+arb(16)/3*J3; p4=arb(2)/3*v-2*h
    V01=-(arb(2)/3-arb(1)/100+arb(1)/2000).log()
    constants=check_margins([
        ('alpha>.011',alpha-arb(11)/1000), ('C>-10',C+10),
        ('C<0',-C), ('e>0',e), ('e<.013',arb(13)/1000-e),
        ('K>0',K), ('K<19',19-K), ('v>h',v-h),
        ('8(v-h)/3<2.5',arb(5)/2-arb(8)/3*(v-h)),
        ('h>.86',h-arb(86)/100), ('p4>-.54',p4+arb(54)/100),
        ('p4<0',-p4), ('V(.1)<.421',arb(421)/1000-V01)])
    rho=Q(1,20); d=Q(13,50)
    assert arb(str(d))-arb(1)/(2*(1+(1-arb(str(rho*rho))).sqrt()))>0
    assert Q(4,3)*Q(13,1000)+Q(5,2)*d*rho**2<Q(1,50)
    assert 2+2*d*rho<Q(21,10)
    assert 16+64*d*rho+96*d*d*rho**2+64*d**4*rho**4<17
    assert Q(21,10)*17/30<Q(6,5)
    assert 10*d*d+Q(11,100)<=Q(393,500)
    assert 19*d**3<Q(167,500)
    margin=Q(11,1000)-Q(393,500)*rho**2-Q(167,500)*rho**4 \
           -Q(1,50)*rho-Q(6,5)*rho**3-Q(1,200)
    assert margin>0
    assert Q(1,500)<Q(1,20)**2
    assert Q(100,81)/500<Q(1,400)
    # 8 product a_i <=1/2, delta<=9rho²/4.
    assert Q(1,225)>Q(1,1000)
    return {'radius':'1/20','local_delta':'1/500','primitive_slope':'1/200',
            'local_stability':'1/225','rational_margin':str(margin),
            'constant_margins':constants}


if __name__=='__main__':
    rows=[]
    for n in [3,4]:
        f0,polynomial=polynomial_certificate(n)
        if n==4:
            polynomial['primary_proof']=schur_certificate_four()
        h=entropy_standard(n,bits=13); Z=partition(PARAMETERS[n],bits=15)
        slack=Z.log()+arb(str(f0))-h
        assert slack<arb(str(SLACK_BOUNDS[n]))
        assert SLACK_BOUNDS[n]<=(SLOPES[n]-Q(1,1000))*THRESHOLDS[n]
        local=local_three() if n==3 else local_four()
        row={'n':n,'potential':PARAMETERS[n],'slope':str(SLOPES[n]),
             'diagonal_expectation':str(f0),'polynomial':polynomial,
             'entropy_standard_ball':str(h),'partition_ball':str(Z),
             'slack_ball':str(slack),'slack_bound':str(SLACK_BOUNDS[n]),
             'threshold':str(THRESHOLDS[n]),'local':local,'pass':True}
        rows.append(row)
        print(json.dumps({k:v for k,v in row.items() if k not in ['polynomial','local']}),flush=True)
    result={'arithmetic':'exact rational polynomials; Arb 192-bit outward rounding',
            'global_stability':'1/1000','all_pass':True,
            'results':rows}
    Path('small34_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'all_pass':True}))
