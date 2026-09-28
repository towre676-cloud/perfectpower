"""Adversarial test of the complete Runge enumeration: planted hits far beyond any scan.

F = G^d + (x - n0)(x - n1) H with deg((x - n0)(x - n1) H) < (d - 1) deg G, so F is rigid with the
same truncated root G (when the perturbation is small enough) and F(n0) = G(n0)^d, F(n1) = G(n1)^d
are hits.  The enumerator must return every planted hit, every returned n must be a genuine hit,
and below 2*10^4 the list must agree with a direct scan.  Writes receipts/adversarial_runge.json.
"""
import json
import random
import sys
import time
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from perfectpower.core import hit_indices, integer_power_root, mul, normalize, power
from perfectpower.runge import runge_enumerate

root = Path(__file__).resolve().parents[1]
rng = random.Random(20260928)
rows, failures, times = [], [], []
t_start = time.time()
for trial in range(int(sys.argv[1]) if len(sys.argv) > 1 else 300):
    d = rng.choice([2, 2, 3, 4])
    q = rng.choice([2, 3]) if d == 2 else 2
    b = rng.choice([1, 2, 3])
    G = [rng.randrange(-9, 10) for _ in range(q)] + [b]
    n0 = rng.choice([rng.randrange(10 ** 3, 10 ** 5), rng.randrange(10 ** 6, 10 ** 9)])
    n1 = rng.randrange(1, 10 ** 4)
    hdeg = (d - 1) * q - 3                  # total perturbation degree (d-1)q - 1
    if hdeg < 0:
        continue
    H = [rng.randrange(-5, 6) for _ in range(hdeg)] + [rng.choice([-1, 1])]
    pert = mul(mul(normalize([-n0, 1]), normalize([-n1, 1])), normalize(H))
    Gd = power(normalize(G), d)
    F = [int(x) for x in normalize([(Gd[i] if i < len(Gd) else 0) + (pert[i] if i < len(pert) else 0)
                                    for i in range(max(len(Gd), len(pert)))])]
    t0 = time.time()
    e = runge_enumerate(F, d)
    dt = time.time() - t0
    got = [n for n, _ in e.hits]
    planted = sorted({n0, n1})
    fi = F
    genuine = all(integer_power_root(sum(c * n ** i for i, c in enumerate(fi)), d) is not None for n in got)
    scan = [n for n, _ in hit_indices(F, d, 0, 20000)]
    ok = set(planted) <= set(got) and genuine and [n for n in got if n <= 20000] == scan
    row = {'F': F, 'd': d, 'planted': planted, 'found': got, 'ok': ok}
    times.append(dt)
    rows.append(row)
    if not ok:
        failures.append(row)
summary = {'trials': len(rows), 'failures': len(failures),
           'max_planted_found': max(max(r['planted']) for r in rows),
           'extra_hits_found': sum(len(set(r['found']) - set(r['planted'])) for r in rows)}
(root / 'receipts' / 'adversarial_runge.json').write_text(
    json.dumps({'summary': summary, 'failures': failures, 'rows': rows}, indent=1) + '\n')
print(json.dumps(summary, indent=1))
print(f'max {max(times):.3f}s per trial, total {time.time() - t_start:.1f}s (not recorded)')
sys.exit(1 if failures else 0)
