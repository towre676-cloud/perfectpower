"""Finite-type polynomials scanned exactly (sieve) to SCAN; reports hits beyond 5000.

This measures how badly a short scan can miss sporadic hits.  Late hits are evidence, not a
failure of the classifier (finite type only claims finitely many hits)."""
import json
import random
import sys

from perfectpower.atlas import classify
from perfectpower.sieve import sieve_hits


def run(seed, trials, scan=150000):
    rng = random.Random(seed)
    late, cnt = [], 0
    for _ in range(trials):
        deg = rng.choice([2, 3, 3, 4, 4, 5, 6])
        d = rng.choice([2, 2, 2, 3])
        f = [rng.randint(-5, 5) for _ in range(deg)] + [rng.choice([1, 1, 2, 3, -1, 4])]
        if rng.random() < 0.4:                   # plant repeated roots
            a, b = rng.randint(-2, 5), rng.randint(-2, 5)
            p = [1]
            for root in ((a, a, b, b) if rng.random() < .5 else (a, b, b, a, a)):
                q = [0] * (len(p) + 1)
                for i, c in enumerate(p):
                    q[i] -= root * c
                    q[i + 1] += c
                p = q
            f = [rng.choice([1, 2, 3]) * c for c in p]
        cl = classify(f, d)
        if cl.kind != 'finite':
            continue
        cnt += 1
        hits = sieve_hits(f, d, scan + 1)
        if any(n > 5000 for n in hits):
            late.append({'F_low_to_high': f, 'd': d, 'genus': cl.curve['genus'], 'hits': hits})
    return {'finite_tested': cnt, 'scan': scan, 'late': late}


if __name__ == '__main__':
    a = sys.argv[1:]
    r = run(int(a[0]) if a else 11, int(a[1]) if len(a) > 1 else 1500, int(a[2]) if len(a) > 2 else 150000)
    print('finite-kind tested', r['finite_tested'], 'scan', r['scan'], 'with hits beyond 5000:', len(r['late']))
    for s in r['late']:
        print(json.dumps(s))
