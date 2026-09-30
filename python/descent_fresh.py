"""The descent gate: an input the compiler has never seen, proved end to end.

Pick a curve y^2 = x^3 - D outside the handwritten registry whose descent certificate passes and
whose point list is nonempty, disguise it by a random affine substitution t = r n + s, expand
the cubic, and hand only the expanded polynomial to the compiler.  The compiler must recognise
the cube, discover the descent data, and emit a standalone Lean file; Lean must check it with
the standard axioms only.  One empty-list curve is run the same way.  The emitted files go to
a temporary directory, never into the repository.

    python3 python/descent_fresh.py [--seed S]
"""
import argparse
import random
import subprocess
import sys
import tempfile
from math import isqrt
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'python'))

from perfectpower.compiler import (COMPLETE_FINITE, PowerConstraint, compile_constraint,  # noqa: E402
                                   mordell_complete)
from perfectpower.descent import certificate, point_list  # noqa: E402


def expand(r, s, D):
    a, b, c, e = r ** 3, 3 * r * r * s, 3 * r * s * s, s ** 3 - D
    return (e, c, b, a), f'{a}*n**3 + ({b})*n**2 + ({c})*n + ({e})'


def run(D, rng, tmp, tag):
    x0 = sorted({x for x, _ in point_list(D)})
    r = rng.randint(1, 6)
    n0 = rng.randint(1, 60)
    s = (x0[0] - r * n0) if x0 else rng.randint(-50, 50)
    F, text = expand(r, s, D)
    plan = compile_constraint(PowerConstraint(F, 2))
    assert plan.status == COMPLETE_FINITE and plan.data.get('descent'), (text, plan.method)
    hits = plan.all_hits()
    # independent check of the claimed list, by brute force
    brute = [n for n in range(1, 20000)
             if (v := sum(c * n ** i for i, c in enumerate(F))) >= 0 and isqrt(v) ** 2 == v]
    assert sorted(brute) == sorted(n for n, _ in hits), (text, brute, hits)
    name = f'fresh_{tag}'
    out = subprocess.run([sys.executable, '-m', 'perfectpower', 'prove', '--expr', text, '--name', name],
                         cwd=ROOT / 'python', capture_output=True, text=True, check=True).stdout
    path = Path(tmp) / f'{name}.lean'
    path.write_text(out)
    res = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=ROOT, capture_output=True, text=True)
    ok = res.returncode == 0 and 'error' not in res.stdout and \
        f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]" in res.stdout
    print(f'{tag}: m^2 = {text}  (D = {D}, t = {r}n + ({s}))  hits {[n for n, _ in hits]}  '
          f'Lean: {"OK" if ok else "FAILED"}')
    if not ok:
        print(res.stdout, res.stderr)
    return ok


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--seed', type=int, default=None)
    args = ap.parse_args()
    seed = args.seed if args.seed is not None else random.SystemRandom().randrange(10 ** 9)
    rng = random.Random(seed)
    print(f'descent gate, seed {seed}')
    passing = [D for D in range(2, 330) if mordell_complete(-D) is None and certificate(D)]
    nonempty = [D for D in passing if point_list(D)]
    empty = [D for D in passing if not point_list(D)]
    with tempfile.TemporaryDirectory() as tmp:
        ok = run(rng.choice(nonempty), rng, tmp, 'nonempty') and run(rng.choice(empty), rng, tmp, 'empty')
    print('descent gate OK' if ok else 'descent gate FAILED')
    raise SystemExit(0 if ok else 1)


if __name__ == '__main__':
    main()
