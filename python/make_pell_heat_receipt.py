"""Theorem T2 receipt: two-term heat asymptotics for Pell-type families, checked numerically.

For each family: kappa, the constant C0, the log-periods of the phase functions, the peak-to-peak
amplitude of the log-periodic term over one period, and, for tau = 1e-4 .. 1e-12,
  shifted model (factor e^{tau B/(2A)}):  |K - prediction| / tau            (claimed bounded)
  unshifted two-term form:                |K - prediction| / (tau log(1/tau)) (claimed bounded)
The unshifted residual divided by tau alone grows when B != 0; it is recorded too, as the failure
mode of the original statement.  Finally the model with every O(tau) term (the Gamma pole at
s = -1, i.e. lam/(E - 1) per class, the orbit corrections delta_j and the boundary sum) is compared
at tau = 1e-2 .. 1e-6: |K - prediction| / (tau^2 log(1/tau)) should stay bounded.  K(tau) is summed in exact order with math.fsum over all hits up to
1e40.  Writes receipts/pell_heat.json.
"""
import json
import math
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from perfectpower.atlas import quadratic_square_hits
from perfectpower.pell_heat import (EULER_GAMMA, pell_heat_model, pell_heat_prediction,
                                    pell_heat_prediction_first_order, phi)

root = Path(__file__).resolve().parents[1]
FAMILIES = [('2n^2+1', (2, 0, 1)), ('3n^2+1', (3, 0, 1)), ('2n^2-7', (2, 0, -7)),
            ('5n^2+n+3', (5, 1, 3)), ('2n^2+n', (2, 1, 0)), ('6n^2-2', (6, 0, -2)),
            ('2n^2+2n (4 x triangular)', (2, 2, 0))]
MATCH = 10 ** 6
rows = []
for name, (A, B, C) in FAMILIES:
    classes, ms, msum = pell_heat_model(A, B, C, match=MATCH)
    hits = sorted(quadratic_square_hits(A, B, C, 10 ** 40))
    hs = sum(1 for h in hits if h <= MATCH)
    hsum = sum(h for h in hits if h <= MATCH)
    kappa = sum(1 / c['logE'] for c in classes)
    C0 = sum((-math.log(c['alpha']) - EULER_GAMMA) / c['logE'] + 0.5 for c in classes) + (hs - ms)
    period = max(c['logE'] for c in classes)
    samples = [sum(phi(u + math.log(c['alpha']), c['logE']) for c in classes)
               for u in [-30 - period * i / 400 for i in range(400)]]
    sh, un, un_tau = {}, {}, {}
    for tau in (1e-4, 1e-6, 1e-8, 1e-10, 1e-12):
        K = math.fsum(math.exp(-tau * h) for h in hits)
        p, _ = pell_heat_prediction(A, B, C, tau, hs, classes, ms, shift=True)
        q, _ = pell_heat_prediction(A, B, C, tau, hs, classes, ms, shift=False)
        key = f'{tau:.0e}'
        sh[key] = float(f'{abs(K - p) / tau:.3e}')
        un[key] = float(f'{abs(K - q) / (tau * math.log(1 / tau)):.3e}')
        un_tau[key] = float(f'{abs(K - q) / tau:.3e}')
    fo = {}
    for tau in (1e-2, 1e-3, 1e-4, 1e-5, 1e-6):
        K = math.fsum(math.exp(-tau * h) for h in hits)
        q = pell_heat_prediction_first_order(A, B, tau, hs, hsum, classes, ms, msum)
        fo[f'{tau:.0e}'] = float(f'{abs(K - q) / (tau * tau * math.log(1 / tau)):.3e}')
    rows.append({'family': name, 'A_B_C': [A, B, C], 'classes': len(classes),
                 'kappa': round(kappa, 10), 'C0': round(C0, 10),
                 'log_periods': sorted({round(c['logE'], 10) for c in classes}),
                 'periodic_peak_to_peak': float(f'{max(samples) - min(samples):.4e}'),
                 'shift_beta': -B / (2 * A),
                 'shifted_residual_over_tau': sh,
                 'unshifted_residual_over_tau_log': un,
                 'unshifted_residual_over_tau': un_tau,
                 'first_order_residual_over_tau2_log': fo})
out = {'statement': 'K(tau) = e^{tau B/(2A)} sum_classes [(log(1/(tau alpha)) - gamma)/log E + 1/2 '
                    '+ Phi_E(log(tau alpha))] + (integer correction) + O(tau); equivalently '
                    'kappa log(1/tau) + C0 + sum Phi_E + O(tau log(1/tau)), and O(tau) if B = 0',
       'status': 'PAPER_PROOF (Mellin) + NUMERICAL check (double precision; residuals near 1e-16 '
                 'relative are rounding, so the ratio at tau = 1e-12 carries about 1e-4 absolute noise)',
       'families': rows}
(root / 'receipts' / 'pell_heat.json').write_text(json.dumps(out, indent=1) + '\n')
for r in rows:
    print(f"{r['family']:26} kappa={r['kappa']:.6f} C0={r['C0']:+.6f} amp={r['periodic_peak_to_peak']:.2e} "
          f"shifted r/tau={list(r['shifted_residual_over_tau'].values())} "
          f"unshifted r/tau={list(r['unshifted_residual_over_tau'].values())} "
          f"first-order r/(tau^2 log)={list(r['first_order_residual_over_tau2_log'].values())}")
