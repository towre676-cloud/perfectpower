"""External completion of the open branches of the branch compiler, with PARI's Thue solver.

For every curve y^2 = x^3 - D (1 <= D <= 100) that the branch compiler leaves OPEN_BRANCH
(`receipts/mordell_branch.json`), each open table entry (k, p, q) gives the Thue equation

    F(a, b) = q a^3 + 3 p a^2 b - 3 D q a b^2 - p D b^3 = k^3

(the s-coordinate of (p + q s)(a + b s)^3).  PARI's `thue(thueinit(P, 1), k^3)` returns all its
integer solutions; flag 1 makes PARI certify the result without GRH.  Each solution gives
y = (p W1 + D q W2)/k^3 when integral, and the points are kept when y^2 + D is a cube.  With the
field-cube branches (already listed exactly), this is a branch-by-branch complete *external*
computation.  It is compared with the Sage census (`data/mordell_census.csv`) and the published
counts; it is **not** a Lean proof (Thue-equation completeness rests on Baker-type bounds inside
PARI).

Run: /opt/sagevenv/bin/python crosscheck/branch_thue_pari.py [timeout_seconds]
Writes receipts/mordell_branch_thue.json.
"""
import csv
import json
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'python'))


WORKER = """
import sys, json, time, cypari2
D, k, p, q = map(int, sys.argv[1:5])
pari = cypari2.Pari()
pari.allocatemem(2 * 10 ** 9)
t0 = time.time()
P = pari.Pol([q, 3 * p, -3 * D * q, -p * D])
sols = pari.thue(pari.thueinit(P, 1), k ** 3)
print(json.dumps({'solutions': sorted((int(s[0]), int(s[1])) for s in sols), 'sec': round(time.time() - t0, 2)}))
"""


def run_with_timeout(args, timeout):
    """One branch in its own process (isolated job with a timeout)."""
    import subprocess
    D, k, p, q = args
    base = {'D': D, 'k': k, 'p': p, 'q': q}
    try:
        r = subprocess.run([sys.executable, '-c', WORKER, str(D), str(k), str(p), str(q)],
                           capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return {**base, 'status': 'TIMEOUT', 'timeout_s': timeout}
    if r.returncode != 0:
        return {**base, 'status': 'ERROR', 'error': r.stderr[-300:]}
    return {**base, **json.loads(r.stdout.strip().splitlines()[-1])}


def main():
    timeout = int(sys.argv[1]) if len(sys.argv) > 1 else 600
    from perfectpower.branch_descent import compile_curve, icbrt
    from perfectpower.descent import W1, W2
    census = {}
    with open(ROOT / 'data' / 'mordell_census.csv') as f:
        for row in csv.DictReader(f):
            census[int(row['k'])] = row
    ledger = json.loads((ROOT / 'receipts' / 'mordell_branch.json').read_text())
    curves = []
    for rec in ledger['curves_detail']:
        if rec['status'] != 'OPEN_BRANCH':
            continue
        D = rec['D']
        c = compile_curve(D)
        pts = set(tuple(p) for p in c['points'])
        branches, complete = [], True
        for e in c['open']:
            r = run_with_timeout((D, e['k'], e['p'], e['q']), timeout)
            if 'solutions' not in r:
                complete = False
            else:
                for a, b in r['solutions']:
                    num = e['p'] * W1(D, a, b) + D * e['q'] * W2(D, a, b)
                    if num % e['k'] ** 3 == 0:
                        y = num // e['k'] ** 3
                        x = icbrt(y * y + D)
                        if x ** 3 == y * y + D:
                            pts.add((x, y))
            branches.append(r)
            print(D, e, r.get('solutions', r.get('status')), r.get('sec'), flush=True)
        row = census.get(-D, {})
        sage_x = sorted(int(v) for v in row.get('x_coordinates', '').split()) if row else None
        xs = sorted({x for x, _ in pts})
        curves.append({'D': D, 'k': -D, 'branches': branches,
                       'status': 'EXTERNALLY_COMPLETE' if complete else 'INCOMPLETE',
                       'points': sorted(pts), 'x_coordinates': xs,
                       'sage_census_x': sage_x, 'sage_rank': row.get('rank'),
                       'agrees_with_sage': (sage_x == xs) if sage_x is not None else None})
    out = {'engine': 'PARI thue with thueinit(P, 1) (unconditional), via passagemath cypari2',
           'label': 'EXTERNAL: complete computation under PARI correctness; not a Lean theorem',
           'curves': curves,
           'externally_complete': sum(c['status'] == 'EXTERNALLY_COMPLETE' for c in curves),
           'agree_with_sage': sum(bool(c['agrees_with_sage']) for c in curves)}
    (ROOT / 'receipts' / 'mordell_branch_thue.json').write_text(json.dumps(out, indent=1) + '\n')
    print(f"{len(curves)} open curves: {out['externally_complete']} externally complete, "
          f"{out['agree_with_sage']} agree with the Sage census")


if __name__ == '__main__':
    main()
