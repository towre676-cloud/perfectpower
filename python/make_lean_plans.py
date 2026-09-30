"""Emit PerfectPower/Generated/Plans.lean: one kernel-checked theorem per catalogued compiler plan.

For a transport plan the theorem states the complete solution set of the *original* constraint.
It is proved by the reduction chain (`PlanCerts.power_transport` / `root_transport`, built from
`Reduction.Exact.comp`, `affine`, `quadratic` and `pull_complete`), with the pull-back computed
by `decide`.  For a filtered Pell plan it is either infinitude from one admissible witness
(`FilteredPell.quadRoot_infinite_of_witness`) or a complete search range `⊆ [1, Nb]` from a
`FinCert` checked by `decide +kernel` (`PlanCerts.quadRoot_subset_of_cert`).

The catalogue is deterministic: the demo constraints plus filtered Pell constraints from a seeded
search, kept only when the certificate is small.  Also writes receipts/plan_certificates.json,
which the compiler reads to cite the theorem of a plan.
"""
import json
import random
import sys
from math import isqrt
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from perfectpower.compiler import (COMPLETE_FINITE, STRUCTURED_INFINITE, PowerConstraint,  # noqa: E402
                                   QuadraticRootConstraint, TriangularConstraint, _root_params,
                                   compile_constraint, count_cert, fin_cert, match_affine_cube,
                                   _thr)
from perfectpower.specialize import parse_poly  # noqa: E402
from perfectpower.arith import pell_fundamental  # noqa: E402

root = Path(__file__).resolve().parents[1]

CURVES = {-2: ('PlanCerts.pairs_m2', [(3, 5), (3, -5)]),
          -4: ('PlanCerts.pairs_m4', [(2, 2), (2, -2), (5, 11), (5, -11)]),
          -13: ('PlanCerts.pairs_m13', [(17, 70), (17, -70)]),
          -5: ('(PlanCerts.pairs_empty PlanCerts.no_points_m5)', []),
          -6: ('(PlanCerts.pairs_empty PlanCerts.no_points_m6)', [])}


def lz(x: int) -> str:
    return f'({x})' if x < 0 else str(x)


def poly_lean(F, var='(n : ℤ)') -> str:
    terms = [f'{lz(c)} * {var} ^ {i}' for i, c in enumerate(F) if c]
    return ' + '.join(terms) if terms else '0'


def fset(pairs, ty) -> str:
    if not pairs:
        return f'(∅ : Finset ({ty}))'
    return '({' + ', '.join(f'({x}, {lz(y)})' for x, y in pairs) + '} : Finset (' + ty + '))'


def transport_theorem(name, con, plan):
    """A transport plan as a theorem on the original constraint, or None."""
    red = plan.reduced
    m = match_affine_cube(red.F)
    if m is None:
        return None
    r, s, k = m
    if k not in CURVES:
        return None
    lemma, pts = CURVES[k]
    hits = plan.all_hits()
    pairs = [(n, w) for n, ws in hits for w in ws]
    if isinstance(con, PowerConstraint):
        Fs = poly_lean(con.F)
        body = f'''/-- Plan `{name}`: {con.describe()}.  Chain: affine `t = {r}n + ({s})` to
`m^2 = t^3 + ({k})` (`{lemma}`). -/
theorem {name} (n : ℕ) (m : ℤ) :
    (1 ≤ n ∧ m ^ 2 = {Fs}) ↔ (n, m) ∈ {fset(pairs, 'ℕ × ℤ')} := by
  have h := PlanCerts.power_transport {lemma} (r := {r}) (by decide) ({s})
    (fun n : ℕ => {Fs}) (fun n => by beta_reduce; ring) n m
  have hp : (PlanCerts.powerChain ({k}) (r := {r}) (by decide) ({s}) (fun n : ℕ => {Fs})
      (fun n => by beta_reduce; ring)).pull {fset(pts, 'ℤ × ℤ')} = {fset(pairs, 'ℕ × ℤ')} := by decide
  rw [hp] at h
  exact h
'''
        return body
    rp = _root_params(con)
    a, b, c, F, L = rp
    Y = 'fun _ => True' if L is None else f'fun y : ℤ => {lz(L)} ≤ y'
    Ydesc = 'True' if L is None else f'{lz(L)} ≤ y'
    Fs = poly_lean(F)
    body = f'''/-- Plan `{name}`: {con.describe()}.  Chain: quadratic `m = 2*{a}*y + ({b})`, then affine
`t = {r}n + ({s})` to `m^2 = t^3 + ({k})` (`{lemma}`). -/
theorem {name} (n : ℕ) (y : ℤ) :
    (1 ≤ n ∧ {Ydesc} ∧ {lz(a)} * y ^ 2 + {lz(b)} * y + {lz(c)} = {Fs}) ↔
      (n, y) ∈ {fset(pairs, 'ℕ × ℤ')} := by
  have h := PlanCerts.root_transport {lemma} (a := {a}) (by decide) ({b}) ({c})
    (fun n : ℕ => {Fs}) ({Y}) (r := {r}) (by decide) ({s}) (fun n => by beta_reduce; ring) n y
  have hp : (PlanCerts.rootChain ({k}) (a := {a}) (by decide) ({b}) ({c}) (fun n : ℕ => {Fs})
      ({Y}) (r := {r}) (by decide) ({s}) (fun n => by beta_reduce; ring)).pull {fset(pts, 'ℤ × ℤ')} =
      {fset(pairs, 'ℕ × ℤ')} := by decide
  rw [hp] at h
  exact h
'''
    return body


def qh_args(a, b, c, F, L):
    C0, B0, A0 = F
    Ls = 'none' if L is None else f'(some {lz(L)})'
    return f'{lz(a)} {lz(b)} {lz(c)} {lz(A0)} {lz(B0)} {lz(C0)} {Ls}', Ls


def filtered_theorem(name, con, plan):
    fd = plan.data.get('filter_decision')
    if not fd or fd['kind'] != 'filtered_pell':
        return None
    a, b, c, F, L = _root_params(con)
    args, Ls = qh_args(a, b, c, F, L)
    C0_, B0_, A0_ = F
    u, v = pell_fundamental(4 * 4 * a * A0_)
    head = f'''/-- Plan `{name}`: {con.describe()}.  Filtered Pell family modulo {fd['modulus']}: '''
    if plan.status == STRUCTURED_INFINITE:
        X, Y = fd['witness']
        return head + f'''an admissible
witness `(X, Y) = ({X}, {Y})`, hence infinitely many solutions. -/
theorem {name} : (FilteredPell.QuadHits {args}).Infinite :=
  FilteredPell.quadRoot_infinite_of_witness {Ls} (by decide) (by decide) (u := {u}) (v := {v})
    (by decide) (by decide) (by decide +kernel) ({X}, {Y})
    ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩ (by decide +kernel)
'''
    # finite: the certificate and a range [1, Nb]
    fc = fin_cert(con)
    C0, B0, A0 = F
    A_, B_, C_ = 4 * a * A0, 4 * a * B0, 4 * a * C0 + b * b - 4 * a * c
    K = B_ * B_ - 4 * A_ * C_ + 4 * A_ * _thr(a, b, L) ** 2
    Nb = 0
    while not (2 * A_ * (Nb + 1) + B_ > 0 and K <= (2 * A_ * (Nb + 1) + B_) ** 2):
        Nb += 1
    Delta = B_ * B_ - 4 * A_ * C_
    isq = [isqrt(t) if (t := Delta + 4 * A_ * Y * Y) > 0 else 0 for Y in range(fc['Ymax'] + 1)]
    roots = ', '.join(f'(({X}, {Y}), {k})' for (X, Y), k in fc['roots'])
    hits = [n for n, _ in plan.all_hits()]
    return head + f'''no cycle meets an
admissible state, so every solution has `n ≤ {Nb}`; the solutions are `n ∈ {hits}`. -/
theorem {name} : FilteredPell.QuadHits {args} ⊆ Set.Iic {Nb} :=
  PlanCerts.quadRoot_subset_of_cert {Ls} (by decide) (by decide) (u := {u}) (v := {v})
    (by decide) (by decide) (by decide +kernel)
    ⟨{fc['Ymax']}, {isq}, [{roots}]⟩ (by decide +kernel) {Nb} (by decide +kernel)
    (by decide +kernel)
'''


def count_theorem(name, con, plan):
    """`|A(N) - (p/q) / log eps * log N| <= K` for all large N, from a CountCert, or None when
    the certificate would be too large for the kernel."""
    cc = count_cert(con)
    if cc is None or cc['Ymax'] > 400 or cc['M'] > 800 or \
            max([P for _, (P, _) in cc['roots']] + [0]) > 400 or not cc['sum_g_over_P']:
        return None
    a, b, c, F, L = _root_params(con)
    args, Ls = qh_args(a, b, c, F, L)
    C0, B0, A0 = F
    q = cc['sum_g_over_P']
    roots = ', '.join(f'(({X}, {Y}), ({P}, {g}))' for (X, Y), (P, g) in cc['roots'])
    D = 4 * 4 * a * A0
    u, v = cc['u'], cc['v']
    num, den = q.numerator, q.denominator
    return (
        f"/-- The roots of `{name}` (for `X^2 - {D} Y^2 = Δ`), each with its residue-cycle length\n"
        f"`P` modulo {cc['M']} and its number `g` of admissible states. -/\n"
        f"def {name}_roots : List ((ℤ × ℤ) × (ℕ × ℕ)) := [{roots}]\n\n"
        f"/-- Certificate for the constant of `{name}`. -/\n"
        f"def {name}_cert : FilteredPell.CountCert := ⟨{cc['Ymax']}, {cc['isqrts']}, {name}_roots⟩\n\n"
        f"/-- **Count of `{name}`**: {con.describe()}.  The number `A(N)` of solutions `n ≤ N`\n"
        f"satisfies `|A(N) - ({num}/{den}) / log ε · log N| ≤ K` for all large `N`, where\n"
        f"`ε = {u} + {v}√{D}` and `{q} = ∑ g / P` over the roots (each `n` counted once). -/\n"
        f"theorem {name}_count : ∃ K : ℝ, ∀ N : ℕ, (4 * {lz(a)} * {lz(B0)} : ℤ).natAbs + 1 ≤ N →\n"
        f"    |((FilteredPell.countQuad {args} N : ℕ) : ℝ) -\n"
        f"      (({num} : ℝ) / {den}) / Real.log (PellExact.eps (4 * (4 * {lz(a)} * {lz(A0)})) {u} {v}) *\n"
        f"        Real.log N| ≤ K := by\n"
        f"  obtain ⟨K, hK⟩ := FilteredPell.quadRoot_count_of_cert (a := {a}) (b := {b}) (c := {c})\n"
        f"    (A₀ := {A0}) (B₀ := {B0}) (C₀ := {C0}) {Ls} (by decide) (by decide)\n"
        f"    (u := {u}) (v := {v}) (by decide) (by decide) (by decide +kernel) {name}_cert\n"
        f"    (by decide +kernel)\n"
        f"  have e : ({name}_roots.map fun e => (e.2.2 : ℝ) / e.2.1).sum = ({num} : ℝ) / {den} := by\n"
        f"    simp only [{name}_roots, List.map, List.sum_cons, List.sum_nil]\n"
        f"    norm_num\n"
        f"  have e' : ({name}_cert.roots.map fun e => (e.2.2 : ℝ) / e.2.1).sum =\n"
        f"      ({num} : ℝ) / {den} := e\n"
        f"  refine ⟨K, fun N hN => ?_⟩\n"
        f"  have := hK N hN\n"
        f"  rwa [e'] at this\n")


def member_theorem(name, con, n0, y0):
    """`n0` is a solution, with its witness `y0`."""
    a, b, c, F, L = _root_params(con)
    args, _ = qh_args(a, b, c, F, L)
    return f'''/-- A solution of `{name}` far beyond any scan: `n = {n0}`, `y = {y0}` (the compiler finds it
as the first admissible point of an orbit, by fast exponentiation of the unit). -/
theorem {name}_member : ({n0} : ℕ) ∈ FilteredPell.QuadHits {args} :=
  ⟨by norm_num, {y0}, by simp [FilteredPell.Dom], by norm_num⟩
'''


def catalogue():
    cat = [('plan_cube_transport', PowerConstraint(parse_poly('(5*n - 7)**3 - 2'), 2)),
           ('plan_cube_minus13', PowerConstraint(parse_poly('(3*n + 2)**3 - 13'), 2)),
           ('plan_cube_minus4', PowerConstraint(parse_poly('(n - 1)**3 - 4'), 2)),
           ('plan_no_points_minus5', PowerConstraint(parse_poly('(2*n + 1)**3 - 5'), 2)),
           ('plan_triangular_cube', TriangularConstraint(parse_poly('64*n**3 - 120*n**2 + 75*n - 16'), 'int')),
           ('plan_root_cube', QuadraticRootConstraint(1, 1, 0, parse_poly('16*n**3 - 12*n**2 + 3*n - 1'), 'nonneg')),
           ('plan_late_transport', PowerConstraint(parse_poly('(n - 1000004)**3 - 2'), 2)),
           ('plan_far_first_hit', QuadraticRootConstraint(2, 1, 0, (1, 0, 263), 'pos'))]
    # filtered Pell constraints from a seeded search, kept when the certificate is small
    rng = random.Random(20260930)
    inf, fin = [], []
    while len(inf) < 5 or len(fin) < 5:
        a = rng.choice([-3, -2, 2, 3])
        con = QuadraticRootConstraint(a, rng.randint(-4, 4), rng.randint(-4, 4),
                                      (rng.randint(-5, 5), rng.randint(-5, 5), rng.choice([-3, -2, -1, 1, 2, 3, 5])),
                                      rng.choice(['int', 'nonneg', 'pos']))
        p = compile_constraint(con)
        fd = p.data.get('filter_decision')
        if not fd or fd['kind'] != 'filtered_pell':
            continue
        fc = fin_cert(con)
        if fc['M'] > 800 or fc['Ymax'] > 400 or max([k for _, k in fc['roots']] + [0]) > 400:
            continue
        if p.status == STRUCTURED_INFINITE and len(inf) < 5 and abs(fd['witness'][0]) < 10 ** 12:
            inf.append(con)
        elif p.status == COMPLETE_FINITE and len(fin) < 5:
            fin.append(con)
    cat += [(f'plan_filtered_infinite_{i + 1}', c) for i, c in enumerate(inf)]
    cat += [(f'plan_filtered_finite_{i + 1}', c) for i, c in enumerate(fin)]
    return cat


def main():
    out = ['import PerfectPower.PlanCerts', 'import PerfectPower.FilteredCount', '',
           '/-! Machine-generated by `python3 python/make_lean_plans.py`; do not edit.  One theorem per',
           'catalogued compiler plan, about the original constraint (see `PlanCerts.lean`). -/', '',
           'namespace PerfectPower.Generated.Plans', '', 'open PerfectPower', '']
    receipt = []
    for name, con in catalogue():
        plan = compile_constraint(con)
        thm = transport_theorem(name, con, plan) if plan.method.startswith('affine transport') \
            else filtered_theorem(name, con, plan)
        if thm is None:
            raise SystemExit(f'no certificate for {name}: {plan.method}')
        out.append(thm)
        extra = []
        if plan.status == STRUCTURED_INFINITE and plan.data.get('filter_decision'):
            ct = count_theorem(name, con, plan)
            if ct is not None:
                out.append(ct)
                extra.append(f'PerfectPower.Generated.Plans.{name}_count')
        if name == 'plan_far_first_hit':
            n0, ws = next(iter(plan.iter_hits(10 ** 20)))
            out.append(member_theorem(name, con, n0, ws[0]))
            extra.append(f'PerfectPower.Generated.Plans.{name}_member')
        hits = plan.all_hits() if plan.status == COMPLETE_FINITE else None
        receipt.append({'theorem': f'PerfectPower.Generated.Plans.{name}',
                        'constraint': con.describe(), 'status': plan.status,
                        'method': plan.method, 'also': extra,
                        'hits': None if hits is None else [[n, w] for n, w in hits]})
    out.append('end PerfectPower.Generated.Plans\n')
    (root / 'PerfectPower' / 'Generated' / 'Plans.lean').write_text('\n'.join(out))
    (root / 'receipts' / 'plan_certificates.json').write_text(json.dumps(receipt, indent=1) + '\n')
    print(f'{len(receipt)} plan theorems -> PerfectPower/Generated/Plans.lean')


if __name__ == '__main__':
    main()
