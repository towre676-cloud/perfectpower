"""Host solver alone vs. host solver after the PerfectPower adapter (`perfectpower.smt_adapter`).

**The instances are constructed, not an independent workload.**  Each is a QF_NIA problem
`m^2 = (r n + s)^3 + k  and  side(n, m, w)` with a random affine disguise and a side constraint
coupling a third variable.  The groups are:
- `sat`: a curve with points, and a side constraint one of the points satisfies;
- `unsat_side`: a curve with points, and a side constraint that excludes every point;
- `no_points`: a curve proved to have no integral points;
- `unsupported`: a control with a cubic that is not a solved curve (y^2 = x^3 + k with k outside
  every registry), so the adapter only adds recognition overhead.

For every instance, times are wall clock:
- host alone: z3 on the original problem, with a fixed timeout;
- adapter + host: the recognition and replacement time plus z3 on the reduced problem.

The answers are compared whenever both finish.  What this measures is whether replacing a solved
conjunct removes the host's work.  It does not show that such conjuncts occur in real workloads:
that needs independently sourced problems.

Run: PYTHONPATH=<dir with z3-solver> python3 python/host_adapter_bench.py [timeout_s]
Writes receipts/host_adapter_bench.json.
"""
import json
import random
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'python'))

import z3  # noqa: E402

from perfectpower.compiler import mordell_complete  # noqa: E402
from perfectpower.smt_adapter import reduce_assertions  # noqa: E402


def cubic(n, r, s):
    x = r * n + s
    return x * x * x


def run(assertions, timeout_ms):
    s = z3.Solver()
    s.set('timeout', timeout_ms)
    s.add(assertions)
    t = time.perf_counter()
    res = s.check()
    return str(res), time.perf_counter() - t


def instances(rng):
    reg = json.loads((ROOT / 'receipts' / 'mordell_registry.json').read_text())['curves']
    with_pts = [c for c in reg if c['points']]
    empty = [c for c in reg if not c['points']]
    out = []
    n, m, w = z3.Ints('n m w')
    for i in range(12):
        c = rng.choice(with_pts)
        x0, y0 = rng.choice(c['points'])
        r = rng.choice([1, 1, 2, 3])
        s = x0 - r * rng.randint(-3, 3)
        n0 = (x0 - s) // r
        eq = m * m == cubic(n, r, s) - c['D']
        out.append(('sat', c['D'], [eq, w * w + n * w == n0 * n0 + n0 + m * m - y0 * y0 + 0 * w, w >= 1]))
    for i in range(12):
        c = rng.choice(with_pts)
        r, s = rng.choice([1, 2, 3]), rng.randint(-20, 20)
        eq = m * m == cubic(n, r, s) - c['D']
        big = max(abs(y) for _, y in c['points']) + 1
        out.append(('unsat_side', c['D'], [eq, m * m > big * big, w * w == n + m * m]))
    for i in range(12):
        c = rng.choice(empty)
        r, s = rng.choice([1, 2, 3]), rng.randint(-20, 20)
        eq = m * m == cubic(n, r, s) - c['D']
        out.append(('no_points', c['D'], [eq, w * w + w == n]))
    unsolved = [k for k in range(-100, 0) if mordell_complete(k) is None]
    for i in range(12):
        k = rng.choice(unsolved)
        r, s = rng.choice([1, 2]), rng.randint(-10, 10)
        eq = m * m == cubic(n, r, s) + k
        out.append(('unsupported', -k, [eq, w * w + w == n, n <= 50, n >= -50]))
    return out


def main():
    timeout = int(float(sys.argv[1]) * 1000) if len(sys.argv) > 1 else 10000
    rng = random.Random(20261001)
    rows = []
    for group, D, asserts in instances(rng):
        host, th = run(asserts, timeout)
        t = time.perf_counter()
        red = reduce_assertions(asserts)
        tr = time.perf_counter() - t
        after, ta = run(red.assertions, timeout)
        agree = None if 'unknown' in (host, after) else host == after
        if agree is False:
            raise SystemExit(f'answer mismatch on {group} D={D}: host {host}, reduced {after}')
        rows.append({'group': group, 'D': D, 'host': host, 'host_s': round(th, 4),
                     'reduced': after, 'recognition_s': round(tr, 4), 'reduced_host_s': round(ta, 4),
                     'replaced': len(red.replacements),
                     'lean': red.replacements[0].lean[0] if red.replacements else None})
        print(f"{group:12s} D={D:3d} host {host:7s} {th:7.3f}s | adapter {tr:.4f}s + {after:7s} {ta:7.3f}s")
    summary = {}
    for g in ('sat', 'unsat_side', 'no_points', 'unsupported'):
        rs = [r for r in rows if r['group'] == g]
        summary[g] = {'instances': len(rs),
                      'host_solved': sum(r['host'] != 'unknown' for r in rs),
                      'adapter_solved': sum(r['reduced'] != 'unknown' for r in rs),
                      'host_total_s': round(sum(r['host_s'] for r in rs), 3),
                      'adapter_total_s': round(sum(r['recognition_s'] + r['reduced_host_s'] for r in rs), 3),
                      'replaced': sum(r['replaced'] for r in rs)}
    out = {'label': 'CONSTRUCTED instances (affine disguises of solved curves plus side constraints); '
                    'not an independent workload', 'host': f'z3 {z3.get_version_string()}',
           'timeout_s': timeout / 1000, 'summary': summary, 'rows': rows}
    (ROOT / 'receipts' / 'host_adapter_bench.json').write_text(json.dumps(out, indent=1) + '\n')
    print(json.dumps(summary, indent=1))


if __name__ == '__main__':
    main()
