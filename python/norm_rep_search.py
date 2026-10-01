"""Residue norm-representative certificates for nonmonic source equations (`receipts/norm_rep_search.json`).

A nonmonic source `F = 1` (leading coefficient `c₀`, `|c₀| > 1`) encodes with norm `N = c₀²`.  Its
certificate for `NormRepProof.normRep_of_res` is a list of representatives `γ` with `N(γ) = ±N` and a
modulus `m` with `N ∣ m` such that every residue class mod `m` whose norm is `≡ N` is divisible by some
`γ` (`γ# r ≡ 0 mod N(γ)`).  Then every element of norm `N` is `γ` times a unit.  `res_ok` is an exact
mirror of `NormRepProof.resRepB`; the search only proposes, and the kernel decides.

* `forms_monic`: a class that takes the value `±1` at a primitive point has a monic representative
  `F ∘ T`; it needs no residue certificate at all (`normRep_one`).
* `reps_of_norm`: elements of norm `±N` in a box, one per associate class (`g ~ h` iff `h/g` is integral).
* `search`: the least modulus `m ∈ {N, 2N, …}` (with `m³` below a budget) for which the representatives
  pass, then a greedy minimal subset.  Each source is tried in its own order and in every order it maps
  into (`receipts/order_transports.json`): a larger order often needs a much smaller modulus.
* **Limit.** A residue certificate is local.  If an ideal of norm `N` is not principal, its residue
  classes cannot be covered by any modulus, and the statement needs class-group information instead.

Run: python3 python/norm_rep_search.py
"""
from __future__ import annotations

import itertools
import json
import math
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'python'))

import make_lean_unit_fields as U  # noqa: E402
from perfectpower import thue_graph as TG  # noqa: E402


def adj(P, Q, g):
    A, B, C = g
    return ((A + P * C) ** 2 - (P * B + Q * C) * B, Q * C * C - A * B, B * B - A * C - P * C * C)


def divides(P, Q, g, r):
    """`g ∣ r` in `ℤ[x]`: `r g#` is divisible by `N(g)` (as in `resRepB`)."""
    n = U.nrm(P, Q, g)
    return all(c % n == 0 for c in U.mul(P, Q, r, adj(P, Q, g)))


def reps_of_norm(P, Q, N, R=8):
    """Elements of norm `±N` with coordinates in `[-R, R]`, one per associate class, smallest first."""
    found = sorted((g for g in itertools.product(range(-R, R + 1), repeat=3) if abs(U.nrm(P, Q, g)) == N),
                   key=lambda g: (sum(map(abs, g)), g))
    reps = []
    for g in found:
        if not any(divides(P, Q, h, g) and divides(P, Q, g, h) for h in reps):
            reps.append(g)
    return reps


def res_ok(P, Q, N, m, reps):
    """Exact mirror of `NormRepProof.resRepB P Q N m reps`; returns the first failing residue or None."""
    if m <= 0 or m % N or not all(abs(U.nrm(P, Q, g)) == N for g in reps):
        return (None,)
    for r in itertools.product(range(m), repeat=3):
        if U.nrm(P, Q, r) % m == N % m and not any(divides(P, Q, g, r) for g in reps):
            return r
    return None


def search(P, Q, N, budget=1_200_000, R=8):
    reps = reps_of_norm(P, Q, N, R)
    if not reps:
        return {'status': 'NO_REPRESENTATIVE_FOUND', 'box': R}
    m = N
    while m ** 3 <= budget:
        if res_ok(P, Q, N, m, reps) is None:
            # greedy: drop representatives that are not needed
            keep = list(reps)
            for g in list(reps):
                trial = [h for h in keep if h != g]
                if trial and res_ok(P, Q, N, m, trial) is None:
                    keep = trial
            return {'status': 'CERTIFIED_IN_PYTHON', 'm': m, 'reps': keep, 'residues': m ** 3,
                    'candidates': len(reps)}
        m += N
    return {'status': 'NO_MODULUS_WITHIN_BUDGET', 'budget': budget, 'candidates': len(reps), 'reps': reps}


def monic_representative(F, R=40):
    """A primitive `(x, y)` with `F(x, y) = ±1` and a unimodular `T` with first column `(x, y)`, or None."""
    for x in range(-R, R + 1):
        for y in range(-R, R + 1):
            if math.gcd(x, y) == 1 and abs(TG.evalF(F, x, y)) == 1:
                g, a, b = _egcd(x, y)            # a x + b y = 1
                T = ((x, -b), (y, a))           # det = x a + b y = 1
                return T, TG.compose(F, T)
    return None


def _egcd(a, b):
    if b == 0:
        return (abs(a), (1 if a > 0 else -1), 0)
    g, x, y = _egcd(b, a % b)
    return g, y, x - (a // b) * y


def main():
    import order_cost as OC
    import order_transport as OT
    tr = json.loads((ROOT / 'receipts' / 'order_transports.json').read_text())['embeddings']
    cov = json.loads((ROOT / 'receipts' / 'descent_coverage.json').read_text())
    rows = []
    for e in cov['unit_equations']:
        if not e['needed'] or abs(e['form'][0]) == 1:
            continue
        F = tuple(e['form'])
        mr = monic_representative(F)
        if mr:
            T, G = mr
            rows.append({'form': list(F), 'status': 'MONIC_REPRESENTATIVE', 'T': T, 'monic_form': list(G),
                         'blocks': e['blocks']})
            continue
        P, Q, k, phi = OC.order_of(F)
        N = F[0] ** 2
        # the own order first, then every order it maps into (a larger order often has a smaller modulus)
        tries = [((P, Q), None, phi)]
        for i, t in enumerate(tr):
            if tuple(t['domain']) == (P, Q):
                T = tuple(t['codomain'])
                tries.append((T, i, OT.emb(T[0], T[1], t['generator_image'], phi)))
        attempts = []
        for (A, B), via, ph in tries:
            r = search(A, B, N)
            attempts.append(dict({'order': [A, B], 'map': via, 'phi': list(ph)}, **r))
        good = [a for a in attempts if a['status'] == 'CERTIFIED_IN_PYTHON']
        best = min(good, key=lambda a: a['residues']) if good else attempts[0]
        rows.append({'form': list(F), 'N': N, 'blocks': e['blocks'], 'status': best['status'], 'best': best,
                     'attempts': attempts})
        print(F, N, best['status'], best['order'], best.get('m'), best.get('reps'), flush=True)
    out = {'label': 'Residue norm-representative certificates proposed in Python (exact mirror of '
                    'NormRepProof.resRepB); not Lean theorems until a curve module checks them',
           'rows': rows,
           'monic_representatives': sum(r['status'] == 'MONIC_REPRESENTATIVE' for r in rows),
           'certified_in_python': sum(r['status'] == 'CERTIFIED_IN_PYTHON' for r in rows),
           'open': sum(r['status'] not in ('MONIC_REPRESENTATIVE', 'CERTIFIED_IN_PYTHON') for r in rows)}
    (ROOT / 'receipts' / 'norm_rep_search.json').write_text(json.dumps(out, indent=1, default=list) + '\n')
    print({k: v for k, v in out.items() if k != 'rows'})


if __name__ == '__main__':
    main()
