"""Reproduce the density comparison used in the ENT manuscript.

The diagonal density is evaluated as a cardinal B-spline, without an
alternating-sum evaluation near its right endpoint. The entropy values are
independently checked by 80-digit piecewise integration of the exact
truncated-power polynomial. This figure is illustrative; these numerical
integrals are not used in a proof certificate.

Dependencies: numpy, scipy, matplotlib, mpmath.
Outputs are written beside this script, or to --output-dir.
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np
from scipy.integrate import quad
from scipy.interpolate import BSpline


def density(n: int, x):
    """Density of n^(-1/2) sum_{j=1}^n U_j, U_j ~ Unif[-1,1]."""
    x = np.asarray(x, dtype=float)
    t = (math.sqrt(n) * x + n) / 2
    # Symmetry avoids evaluating the near-right-boundary spline separately.
    t = np.minimum(t, n - t)
    spline = BSpline.basis_element(np.arange(n + 1, dtype=float),
                                   extrapolate=False)
    inside = (t >= 0) & (t <= n / 2)
    result = np.zeros_like(t)
    result[inside] = math.sqrt(n) / 2 * spline(t[inside])
    return float(result) if result.ndim == 0 else result


def stats(n: int):
    edges = [(2*k-n)/math.sqrt(n) for k in range(n+1)]
    def integrate(fn):
        vals = [quad(fn, a, b, epsabs=1e-13, epsrel=1e-13, limit=200)
                for a,b in zip(edges[:-1], edges[1:])]
        return sum(v for v,_ in vals), sum(e for _,e in vals)
    def entropy_integrand(x):
        y = density(n,x)
        return -y*math.log(y) if y > 0 else 0.0
    entropy, error = integrate(entropy_integrand)
    mass, _ = integrate(lambda x:density(n,x))
    variance, _ = integrate(lambda x:x*x*density(n,x))
    assert abs(mass-1) < 1e-12
    assert abs(variance-1/3) < 1e-12
    peak = density(n,0)
    return dict(n=n, density_at_zero=peak, entropy_nats=entropy,
                min_entropy_nats=-math.log(peak), mass=mass,
                variance=variance, quadrature_error_estimate=error)


def high_precision_entropy(n: int):
    mp.mp.dps = 80
    def f(t):
        t = min(t,n-t)
        if t <= 0:
            return mp.mpf(0)
        k = int(mp.floor(t))
        return sum((-1)**j * math.comb(n,j) * (t-j)**(n-1)
                   for j in range(k+1)) / math.factorial(n-1)
    def integrand(t):
        y=f(t)
        return -y*mp.log(y) if y>0 else mp.mpf(0)
    h_irwin = 2*sum(mp.quad(integrand,[k,k+1]) for k in range(n//2))
    if n%2:
        h_irwin += 2*mp.quad(integrand,[n//2,mp.mpf(n)/2])
    return h_irwin + mp.log(2/mp.sqrt(n))


def main():
    if not __debug__:
        raise RuntimeError("The figure checks require Python assertions. Run without -O.")
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir',type=Path,default=Path(__file__).resolve().parent)
    args=parser.parse_args()
    out=args.output_dir;out.mkdir(parents=True,exist_ok=True)

    rows=[stats(n) for n in (2,8)]
    for row in rows:
        hp=high_precision_entropy(row['n'])
        row['entropy_80_digit_quadrature']=mp.nstr(hp,65)
        row['independent_entropy_discrepancy']=abs(float(hp)-row['entropy_nats'])
        assert row['independent_entropy_discrepancy'] < 1e-12
    assert abs(rows[0]['entropy_nats']-(1+math.log(2))/2) < 1e-13
    assert abs(rows[1]['density_at_zero']-151*math.sqrt(2)/315) < 1e-13
    assert rows[0]['density_at_zero'] > rows[1]['density_at_zero']
    assert rows[0]['entropy_nats'] < rows[1]['entropy_nats']

    plt.rcParams.update({
        'font.family':'serif','font.serif':['DejaVu Serif'],
        'mathtext.fontset':'dejavuserif','font.size':9,
        'axes.labelsize':9,'axes.titlesize':10,'legend.fontsize':8.5,
        'xtick.labelsize':8,'ytick.labelsize':8,
        'axes.spines.top':False,'axes.spines.right':False,
        'axes.linewidth':.65,'xtick.major.width':.6,'ytick.major.width':.6,
        'pdf.fonttype':42,'ps.fonttype':42,'savefig.transparent':False,
    })
    blue='#205B8E';orange='#C15B21';gray='#777777'
    fig,(ax,lower)=plt.subplots(2,1,figsize=(6.6,4.35),sharex=True,
        gridspec_kw={'height_ratios':[3.3,1.25],'hspace':.12})
    fig.subplots_adjust(left=.095,right=.98,bottom=.11,top=.97)
    x=np.linspace(-3.05,3.05,2401)
    p2=density(2,x);p8=density(8,x)
    normal=math.sqrt(3/(2*math.pi))*np.exp(-1.5*x*x)
    ax.plot(x,p2,color=blue,lw=1.8,label=r'Two coordinates: $T_2$')
    ax.plot(x,p8,color=orange,lw=1.9,label=r'Full diagonal: $T_8$')
    ax.plot(x,normal,color=gray,lw=1.05,ls=(0,(3,2)),
            label=r'Gaussian, variance $1/3$',zorder=1)
    ax.set_ylabel('Density')
    ax.set_ylim(0,.77);ax.set_xlim(-3.05,3.05)
    ax.set_yticks([0,.2,.4,.6])
    ax.legend(loc='upper left',frameon=False,handlelength=2.2,
              borderaxespad=.25,labelspacing=.55)
    ax.grid(axis='y',color='#e6e6e6',lw=.55,zorder=0)
    ax.text(.985,.95,'Central density / Shannon entropy',
            transform=ax.transAxes,ha='right',va='top',fontsize=8)
    for row, y, color in zip(rows, (.84, .74), (blue, orange)):
        label = (rf"$T_{row['n']}$:  " +
                 rf"${row['density_at_zero']:.6f}\;/\;{row['entropy_nats']:.6f}$")
        ax.text(.985, y, label, transform=ax.transAxes, ha='right', va='top',
                color=color, fontsize=8.5)
    difference=p8-p2
    lower.axhline(0,color='#777777',lw=.7)
    lower.fill_between(x,0,difference,where=difference>=0,
                       color=orange,alpha=.24,linewidth=0)
    lower.fill_between(x,0,difference,where=difference<0,
                       color=blue,alpha=.20,linewidth=0)
    lower.plot(x,difference,color='#3b3b3b',lw=1)
    lower.set_ylabel(r'$q_8-q_2$')
    lower.set_xlabel(r'Projection coordinate $x$')
    lower.set_xticks([-3,-2,-1,0,1,2,3])
    lower.set_yticks([-.04,0,.04])
    lower.set_ylim(-.053,.048)
    lower.grid(axis='y',color='#e6e6e6',lw=.55,zorder=0)
    fig.savefig(out/'projection_density.pdf',bbox_inches='tight',
                metadata={'Title':'Two-coordinate and diagonal cube projections',
                          'Author':'Vu Khac Ky',
                          'Subject':'Illustration for the ENT conjecture'})
    fig.savefig(out/'projection_density.png',dpi=240,bbox_inches='tight')
    plt.close(fig)
    result={
        'ambient_dimension':8,'uniform_support':[-1,1],
        'two_coordinate_vector':'(1/sqrt(2),1/sqrt(2),0,...,0)',
        'diagonal_vector':'(1/sqrt(8),...,1/sqrt(8))',
        'density_formula':'q_n(x)=sqrt(n)/2 f_n((sqrt(n)*x+n)/2)',
        'evaluation':'cardinal B-spline, evaluated with scipy.interpolate.BSpline',
        'entropy_integration':'piecewise scipy QUADPACK; independent mpmath 80-digit integration of exact polynomial pieces',
        'numerical_status':'Illustrative numerical values; quadrature error estimates are not rigorous interval certificates and no proof depends on this figure.',
        'peak_exact':{'n2':'1/sqrt(2)','n8':'151*sqrt(2)/315'},
        'entropy_n2_exact':'(1+log(2))/2',
        'statistics':rows,
        'min_entropy_convention':'h_infinity=-log(sup_x q(x)); maximizing central density minimizes h_infinity',
    }
    (out/'figure_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
