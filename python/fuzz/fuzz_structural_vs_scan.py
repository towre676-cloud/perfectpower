"""structural_hits / structural_count against a brute-force scan to N (exit status 1 on any
disagreement or exception)."""
import random
import sys

from perfectpower.atlas import classify, structural_count, structural_hits
from perfectpower.core import integer_power_root


def ev(f, n):
    r = 0
    for c in reversed(f):
        r = r * n + c
    return r


def run(seed, trials, N=4000):
    rng = random.Random(seed)
    bad, err, kinds, tot = [], [], {}, 0
    for _ in range(trials):
        deg = rng.choice([1, 2, 2, 3, 3, 4, 4, 5, 6])
        d = rng.choice([2, 2, 2, 3, 3, 4, 5, 6])
        f = [rng.randint(-6, 6) for _ in range(deg)] + [rng.choice([1, 1, 2, 3, 4, -1, -2, 8, 9])]
        if rng.random() < 0.25:                  # plant (x - a)^j (x - b)^k structure
            a, b = rng.randint(-3, 6), rng.randint(-3, 6)
            j, k = rng.randint(1, 4), rng.randint(0, 3)
            p = [1]
            for root, m in ((a, j), (b, k)):
                for _ in range(m):
                    q = [0] * (len(p) + 1)
                    for i, c in enumerate(p):
                        q[i] -= root * c
                        q[i + 1] += c
                    p = q
            cc = rng.choice([1, 2, 3, 4, -1, 8])
            f = [cc * c for c in p]
        if all(c == 0 for c in f):
            continue
        try:
            cl = classify(f, d)
        except Exception as e:                   # noqa: BLE001
            err.append((f, d, 'classify', repr(e)))
            continue
        kinds[cl.kind] = kinds.get(cl.kind, 0) + 1
        if not (cl.kind in ('radical', 'pell', 'power', 'constant') or cl.effective):
            continue
        tot += 1
        try:
            s, sc = structural_hits(f, d, N), structural_count(f, d, N)
        except Exception as e:                   # noqa: BLE001
            err.append((f, d, cl.kind, repr(e)))
            continue
        b = [n for n in range(1, N + 1) if integer_power_root(ev(f, n), d) is not None]
        if list(s) != b or sc != len(b):
            bad.append((f, d, cl.kind, sorted(set(s) ^ set(b))[:8]))
    return {'kinds': kinds, 'tested': tot, 'disagreements': bad, 'errors': err}


if __name__ == '__main__':
    r = run(int(sys.argv[1]) if len(sys.argv) > 1 else 1, int(sys.argv[2]) if len(sys.argv) > 2 else 1500)
    print('kinds', r['kinds'], 'tested', r['tested'], 'disagree', len(r['disagreements']), 'errors', len(r['errors']))
    for x in (r['disagreements'] + r['errors'])[:15]:
        print(x)
    sys.exit(1 if r['disagreements'] or r['errors'] else 0)
