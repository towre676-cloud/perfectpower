"""quadratic_square_hits against a scan to N on random quadratics with large units."""
import random
import sys
from math import isqrt

from perfectpower.atlas import quadratic_square_hits

AS = [2, 3, 5, 6, 7, 8, 10, 11, 13, 14, 15, 17, 19, 21, 22, 23, 29, 31, 37, 41, 43, 46, 53, 61, 67,
      73, 97, 109]


def run(seed, trials, N=300000):
    rng = random.Random(seed)
    bad, tot = [], 0
    for _ in range(trials):
        A = rng.choice(AS)
        if rng.random() < 0.3:
            A *= rng.choice([4, 9])
        B, C = rng.randint(-60, 60), rng.randint(-80, 200)
        if B * B - 4 * A * C == 0:
            continue
        try:
            h = sorted(quadratic_square_hits(A, B, C, N))
        except Exception as e:                   # noqa: BLE001
            bad.append((A, B, C, repr(e)))
            continue
        s = [n for n in range(1, N + 1) for v in (A * n * n + B * n + C,) if v >= 0 and isqrt(v) ** 2 == v]
        tot += 1
        if h != s:
            bad.append((A, B, C, sorted(set(h) ^ set(s))[:6]))
    return {'tested': tot, 'bad': bad}


if __name__ == '__main__':
    r = run(int(sys.argv[1]) if len(sys.argv) > 1 else 7, int(sys.argv[2]) if len(sys.argv) > 2 else 400)
    print('tested', r['tested'], 'bad', len(r['bad']))
    for x in r['bad'][:10]:
        print(x)
    sys.exit(1 if r['bad'] else 0)
