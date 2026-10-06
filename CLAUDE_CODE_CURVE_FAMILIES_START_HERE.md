# Curve family compiler handoff

Read docs/CURVE_FAMILIES_MONOGRAPH.md. CurveFamily accepts ascending x coefficients, each an ascending rational t polynomial, for y^2=P(x,t). Monic x degrees 3, 5 and 7 and parameter degree at most four are supported. Exact algebra needs only the standard library; numerical periods use python/requirements-analytic.txt.

```python
from perfectpower.curve_families import CurveFamily
family = CurveFamily({'coefficients': [[0,1],[-1],[0],[0],[0],[1]]})
connection = family.evidence()
operator = family.observable()
result = family.period_path([0,'1/5'],
    {'center':'1/2','radius':'13/20'}, mode='scalar')
```

The generic genus-two case derives four exact reduction identities and an order-four observable. The isotrivial family x^5+t reduces its first observable from four coordinates to order one. Matrix continuation remains available at smooth points singular for a scalar representation. Exact real/imaginary polynomial pullbacks and Sturm counts exclude poles on entire rational straight parameter segments. Numerical accuracy remains a separate estimate.

```sh
export PYTHONPATH=python
python python/develop_curve_families.py --output /tmp/families
python -m unittest discover -s python/tests -p test_curve_families.py
python -m perfectpower service --database /tmp/families.sqlite < receipts/curve_families/service_requests.jsonl
make test
```

Open receipts/curve_families/family_workbench.html for recorded trajectories. The slider selects samples, rather than running new continuation. Eleven persistent kinds include curve_family. Restart reconstructs the exact object from its stored specification; methods are allowlisted.

Preserve ascending coefficients, de Rham versus holomorphic forms, endpoint cycle marks, genuine versus additional scalar singularities, and bounded versus global arithmetic claims. Numerical roots, quadrature and ODE propagation are not certified enclosures. General cyclic families, local degeneration execution, exact integral homology monodromy and new Lean proofs remain further work. Every push must include the full uncapped source ZIP and monograph.
