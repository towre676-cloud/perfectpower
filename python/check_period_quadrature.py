"""Optional SciPy diagnostics for period bridges; never an identity proof.

Run from the repository root:
    python python/check_period_quadrature.py
SciPy is optional for the engine; this independent numerical check requires it.
"""
import argparse
from fractions import Fraction
import json
from math import exp, factorial, log, pi, sin
from pathlib import Path
import platform
import sys


def diagnostics():
    try:
        import scipy
        from scipy.integrate import quad
        from scipy.special import zeta
    except ImportError as error:
        raise SystemExit("Optional diagnostic requires SciPy; the exact engines do not.") from error
    from perfectpower.e8_periods import (
        PHI30, combined_log_mellin_coefficients, combined_pi_coefficient,
    )
    from perfectpower.raghava_periods import (
        cancellation_partial, evaluate_sine_pole, sine_pole,
        two_order_cancellation,
    )

    def kernel(x):
        polynomial = sum(a*x**i for i, a in enumerate(PHI30))
        derivative = sum(i*a*x**(i-1) for i, a in enumerate(PHI30) if i)
        return 240*x**29/(1-x**30)-derivative/polynomial

    def integrate_mellin(s, log_weight=False):
        cutoff = 50

        def integrand(t):
            if not t:
                return 0.
            x = exp(-t)
            value = t**(s-1)*x*kernel(x)
            return value*log(t) if log_weight else value

        near, near_error = quad(integrand, 0, 1, epsabs=1e-11, epsrel=1e-11)
        far, far_error = quad(integrand, 1, cutoff, epsabs=1e-11, epsrel=1e-11)
        normalization = factorial(s-1)
        # For t>=50, x=e^-t<1/2. Spectral kernel is bounded by
        # 8/(1-x)<=16, and root-permutation kernel by
        # 240*x^29/(1-x^30)<1. Thus |combined_kernel|<17.
        if log_weight:
            # log(t)<=t; this branch is only the s=2 diagnostic.
            tail_bound = 17*exp(-cutoff)*(cutoff**2+2*cutoff+2)
        else:
            tail_bound = 17*exp(-cutoff)*sum(cutoff**j/factorial(j) for j in range(s))
        return ((near+far)/normalization,
                (near_error+far_error)/normalization, tail_bound, cutoff)

    mellin = []
    for s in (2, 4, 6):
        value, error, tail, cutoff = integrate_mellin(s)
        expected = float(combined_pi_coefficient(s))*pi**s
        mellin.append(dict(s=s, numerical_integral=value, predicted_value=expected,
                           absolute_difference=abs(value-expected),
                           quadrature_error_estimate=error,
                           analytic_absolute_truncation_bound_binary64=tail,
                           transformed_cutoff=cutoff,
                           normalization="divide by Gamma(s)=(s-1)!",
                           domain="integer s>=2; original integral on 0<x<1",
                           transform="x=exp(-t); integrand=t^(s-1)*exp(-t)*K(exp(-t))"))
    value, error, tail, cutoff = integrate_mellin(2, log_weight=True)
    expected = pi*pi*sum(float(c)*log(p) for p, c in combined_log_mellin_coefficients().items())
    log_moment = dict(numerical_integral=value, predicted_value=expected,
                      absolute_difference=abs(value-expected),
                      quadrature_error_estimate=error,
                      analytic_absolute_truncation_bound_binary64=tail,
                      transformed_cutoff=cutoff,
                      integrand="(-log(x))*log(-log(x))*K(x)",
                      normalization="Gamma(2)=1; Gamma derivative term vanishes because F(2)=0",
                      tail_reason="for t>=50, |K(exp(-t))|<17 and log(t)<=t")

    sine = []
    radius = 500
    for k, a, b in ((2, Fraction(2,3), Fraction(5,4)),
                    (3, Fraction(3,2), Fraction(2,3)),
                    (4, Fraction(2), Fraction(3,4))):
        def integrand(x):
            return (sin(float(a)*x)/(x-1j*float(b)))**k

        value = 0j
        quadrature_error = 0.
        for start in range(-radius, radius, 10):
            re, re_error = quad(lambda x: integrand(x).real, start, start+10, epsabs=1e-11)
            im, im_error = quad(lambda x: integrand(x).imag, start, start+10, epsabs=1e-11)
            value += re+1j*im
            quadrature_error += re_error+im_error
        expected = evaluate_sine_pole(sine_pole(k,a,b))['value']
        exact_tail = Fraction(2, (k-1)*radius**(k-1))
        sine.append(dict(k=k, a=str(a), b=str(b), radius=radius,
                         numerical_integral=dict(real=value.real, imaginary=value.imag),
                         predicted_real_value=expected, absolute_difference=abs(value-expected),
                         quadrature_error_estimate=quadrature_error,
                         analytic_absolute_tail_bound=str(exact_tail),
                         within_tail_plus_error=abs(value-expected)<=float(exact_tail)+quadrature_error,
                         domain="integer k>=2; positive rational a,b; absolutely integrable",
                         tail_reason="|sin(a*x)|<=1 and |x-i*b|>=|x|; tails<=2*R^(1-k)/(k-1)"))

    cancellations = []
    for r, s in ((1,2), (1,3), (2,3), (2,4)):
        receipt = two_order_cancellation(r,s)
        partial = cancellation_partial(receipt,60)
        lhs = sum(float(Fraction(row['coefficient']))*pi**row['pi_power']
                  for row in partial['pi_coefficients'])
        rhs = sum(float(Fraction(row['coefficient']))*pi**row['pi_power']*zeta(row['zeta_order'],1)
                  for row in receipt['zeta_coefficients'])
        cancellations.append(dict(r=r,s=s,terms=60,numerical_partial=lhs,numerical_zeta_side=rhs,
                                  absolute_difference=abs(lhs-rhs),
                                  exact_analytic_series_tail=partial['tail_absolute'],
                                  caution="binary64 conversion error dominates this tiny exact tail; comparison is not an enclosure"))

    return dict(schema="pp-independent-period-quadrature/1",
                arithmetic="binary64 numerical diagnostics, not proof certificates",
                runtime=dict(python=platform.python_version(), executable=sys.executable,
                             scipy=scipy.__version__),
                normalization_audit="Mellin integrals divide by Gamma(s); logarithmic derivative at s=2 needs no digamma correction because F(2)=0",
                analytic_tail_audit=dict(
                    arcsine_kernel="|c_n|<=3*u^2*3^ceil(2u^2)/(n*4^n); sum geometric tail with n>=terms+1",
                    arcsine_moment="e_r(n)<=2^r/r! and binom(2n,n)>=4^n/(2n+1) give stated positive tail",
                    two_order="|H_2n+A*H_n-D/(2n)|<=(2+A+D/2)*n; signed E bounded absolutely; geometric sum yields bound/4^terms"),
                combined_e8_mellin=mellin,combined_e8_log_mellin=log_moment,
                scaled_sine_pole=sine,two_order_cancellation=cancellations,
                audit_result="no substantive mathematical/domain bug found in reviewed modules",
                limitation="SciPy quadrature error estimates and binary64 predictions are not rigorous numerical enclosures")


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',default='receipts/period_bridge/independent_quadrature.json')
    args=parser.parse_args()
    result=diagnostics()
    destination=Path(args.output)
    destination.parent.mkdir(parents=True,exist_ok=True)
    destination.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(dict(output=str(destination),audit_result=result['audit_result'])))


if __name__ == '__main__':
    main()
