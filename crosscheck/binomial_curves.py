"""Integral points of the two elliptic curves behind the binomial scan-only rows.

  C(n,2) = m^3  <=>  Y^2 = X^3 + 1      with X = 2m,     Y = 2n - 1
  C(n,3) = m^2  <=>  Y^2 = X^3 - 36X    with X = 6(n-1), Y = 36m

Run: /opt/sagevenv/bin/python crosscheck/binomial_curves.py  -> receipts/binomial_curves.json
The integral-point lists are Sage's (rank proved, saturated generators, elliptic-logarithm sieving)
and become the explicit hypotheses of the Lean theorems in PerfectPower/Binomial.lean.
"""
import json
from pathlib import Path

from sage.all__sagemath_schemes import EllipticCurve
import sage.all__sagemath_eclib  # noqa: F401
import sage.all__sagemath_symbolics  # noqa: F401
import sage.version

out = {}
for name, ainv in (('Y^2 = X^3 + 1', [0, 0, 0, 0, 1]), ('Y^2 = X^3 - 36X', [0, 0, 0, -36, 0])):
    E = EllipticCurve(ainv)
    rank = int(E.rank(proof=True))
    gens = E.gens(proof=True)
    sat = int(E.saturation(gens)[1]) if gens else 1
    pts = sorted({(int(P[0]), int(P[1])) for P in E.integral_points(mw_base=gens, both_signs=True)})
    out[name] = {'a_invariants': ainv, 'rank': rank, 'rank_method': 'mwrank (proof=True)',
                 'generators': [[str(c) for c in P.xy()] for P in gens], 'saturation_index': sat,
                 'torsion': [[str(c) for c in P.xy()] for P in E.torsion_points() if not P.is_zero()],
                 'conductor': int(E.conductor()), 'integral_points': pts,
                 'x_coordinates': sorted({x for x, _ in pts}),
                 'engine': f'passagemath {sage.version.version}: integral_points(mw_base=gens, both_signs=True)'}
Path('receipts/binomial_curves.json').write_text(json.dumps(out, indent=1) + '\n')
for k, v in out.items():
    print(k, 'rank', v['rank'], 'sat', v['saturation_index'], 'x:', v['x_coordinates'])
