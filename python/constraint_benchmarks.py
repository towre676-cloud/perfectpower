"""Runtime of structural plans against the brute-force loops they replace (timings vary by machine;
not part of `make verify`; run with `make bench`).

For each specialized demo of python/constraint_demos.py: the preprocessing cost (classification,
Pell unit, orbit seeds, Runge enumeration, code generation), the specialized run time and the
brute-force run time at increasing N, and the observed crossover: the least measured N at which
preprocessing plus the specialized run beats the loop.  Brute force is measured up to 10^5 only;
larger N are specialized-only.  Writes receipts/constraint_benchmarks.json.
"""
import json
import platform
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from constraint_demos import DEMOS  # noqa: E402
from perfectpower.specialize import specialize, _exec  # noqa: E402

root = Path(__file__).resolve().parents[1]
BRUTE = [10 ** 3, 10 ** 4, 10 ** 5]
LARGE = [10 ** 6, 10 ** 9, 10 ** 12, 10 ** 18, 10 ** 30]


def best(f, reps=3):
    out = None
    for _ in range(reps):
        t = time.perf_counter()
        r = f()
        dt = time.perf_counter() - t
        out = dt if out is None else min(out, dt)
    return out, r


def main():
    rows = []
    for key, title, prog in DEMOS:
        t0 = time.perf_counter()
        specialize(prog)
        t_first = time.perf_counter() - t0
        t_pre, sp = best(lambda: specialize(prog))
        if sp.source is None:
            rows.append({'demo': key, 'status': sp.plan.status, 'specialized': False,
                         'preprocessing_s': t_pre})
            continue
        orig, spec = _exec(sp.original), _exec(sp.source)
        series = []
        for N in BRUTE:
            tb, rb = best(lambda: orig(N), 1 if N >= 10 ** 5 else 3)
            ts, rs = best(lambda: spec(N))
            assert rb == rs, (key, N)
            series.append({'N': N, 'brute_s': tb, 'specialized_s': ts, 'hits': len(rs),
                           'preprocessing_plus_specialized_s': t_pre + ts})
        large = []
        for N in LARGE:
            if sp.plan.method == 'radical parametrization' and N > 10 ** 9:
                continue
            ts, rs = best(lambda: spec(N), 1)
            large.append({'N': N, 'specialized_s': ts, 'hits': len(rs)})
        cross = next((r['N'] for r in series if r['preprocessing_plus_specialized_s'] < r['brute_s']), None)
        rows.append({'demo': key, 'status': sp.plan.status, 'method': sp.plan.method,
                     'specialized': True, 'preprocessing_s': t_pre,
                     'preprocessing_first_call_s': t_first, 'brute_vs_specialized': series,
                     'specialized_only': large, 'observed_crossover_N': cross})
        print(key, 'crossover', cross, 'pre', round(t_pre, 4))
    out = {'machine': platform.platform(), 'python': platform.python_version(),
           'note': 'timings vary by machine; brute force measured to 1e5 only', 'rows': rows}
    path = root / 'receipts' / 'constraint_benchmarks.json'
    path.write_text(json.dumps(out, indent=1) + '\n')
    print('->', path.relative_to(root))


if __name__ == '__main__':
    main()
