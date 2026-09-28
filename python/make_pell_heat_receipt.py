"""Theorem T2 receipt: two-term heat asymptotics for Pell-type families, checked numerically.

For each family: kappa, the constant C0, the log-periods of the phase functions, the peak-to-peak
amplitude of the log-periodic term over one period, and |K(tau) - prediction| for
tau = 1e-4 .. 1e-12 (should be O(tau)).  Writes receipts/pell_heat.json.
"""
import json
import math
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from perfectpower.atlas import quadratic_square_hits
from perfectpower.pell_heat import EULER_GAMMA, pell_heat_model, pell_heat_prediction, phi

root = Path(__file__).resolve().parents[1]
FAMILIES = [('2n^2+1', (2, 0, 1)), ('3n^2+1', (3, 0, 1)), ('2n^2-7', (2, 0, -7)),
            ('5n^2+n+3', (5, 1, 3)), ('2n^2+n', (2, 1, 0)), ('6n^2-2', (6, 0, -2)),
            ('2n^2+2n (4 x triangular)', (2, 2, 0))]
MATCH = 10 ** 6
rows = []
for name, (A, B, C) in FAMILIES:
    classes, ms = pell_heat_model(A, B, C, match=MATCH)
    hits = sorted(quadratic_square_hits(A, B, C, 10 ** 40))
    hs = sum(1 for h in hits if h <= MATCH)
    kappa = sum(1 / c['logE'] for c in classes)
    C0 = sum((-math.log(c['alpha']) - EULER_GAMMA) / c['logE'] + 0.5 for c in classes) + (hs - ms)
    period = max(c['logE'] for c in classes)
    samples = [sum(phi(u + math.log(c['alpha']), c['logE']) for c in classes)
               for u in [-30 - period * i / 400 for i in range(400)]]
    resid = {}
    for tau in (1e-4, 1e-6, 1e-8, 1e-10, 1e-12):
        K = sum(math.exp(-tau * h) for h in hits)
        p, _ = pell_heat_prediction(A, B, C, tau, hs, classes, ms)
        resid[f'{tau:.0e}'] = float(f'{abs(K - p):.2e}')
    rows.append({'family': name, 'A_B_C': [A, B, C], 'classes': len(classes),
                 'kappa': round(kappa, 10), 'C0': round(C0, 10),
                 'log_periods': sorted({round(c['logE'], 10) for c in classes}),
                 'periodic_peak_to_peak': float(f'{max(samples) - min(samples):.4e}'),
                 'abs_residual_after_two_terms': resid})
out = {'statement': 'K(tau) = kappa log(1/tau) + C0 + sum_classes Phi_E(log(tau alpha)) + O(tau)',
       'status': 'PAPER_PROOF (Mellin) + EXACT/NUMERICAL check; floats, residuals should scale like tau',
       'families': rows}
(root / 'receipts' / 'pell_heat.json').write_text(json.dumps(out, indent=1) + '\n')
for r in rows:
    print(f"{r['family']:26} kappa={r['kappa']:.6f} C0={r['C0']:+.6f} amp={r['periodic_peak_to_peak']:.2e} "
          f"resid@1e-12={r['abs_residual_after_two_terms']['1e-12']}")
