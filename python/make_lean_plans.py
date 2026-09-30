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


def _auto_args(con):
    a, b, c, F, L = _root_params(con)
    C0, B0, A0 = F
    Ls = 'none' if L is None else f'(some {lz(L)})'
    u, v = pell_fundamental(4 * 4 * a * A0)
    named = f'(a := {a}) (b := {b}) (c := {c}) (A₀ := {A0}) (B₀ := {B0}) (C₀ := {C0})'
    M = f'(4 * (4 * {lz(a)} * {lz(A0)}) * {lz(a)} : ℤ).natAbs'
    good = f'(FilteredPell.quadGoodB {lz(a)} {lz(b)} (4 * {lz(a)} * {lz(A0)}) (4 * {lz(a)} * {lz(B0)}) {Ls})'
    abc = f'(4 * {lz(a)} * {lz(A0)}) (4 * {lz(a)} * {lz(B0)}) (4 * {lz(a)} * {lz(C0)} + {lz(b)} ^ 2 - 4 * {lz(a)} * {lz(c)})'
    return a, b, c, A0, B0, C0, L, Ls, u, v, named, M, good, abc


def count_theorem(name, con, plan):
    """The count with a certified constant, from a certificate **computed by Lean**
    (`FilteredPell.autoCount`): the theorem carries only the constant."""
    cc = count_cert(con)
    if cc is None or cc['Ymax'] > 3000 or max([P for _, (P, _) in cc['roots']] + [0]) > 400 \
            or not cc['sum_g_over_P']:
        return None
    a, b, c, A0, B0, C0, L, Ls, u, v, named, M, good, abc = _auto_args(con)
    args, _ = qh_args(a, b, c, (C0, B0, A0), L)
    q = cc['sum_g_over_P']
    D = 4 * 4 * a * A0
    return (
        f"/-- **Count of `{name}`**: {con.describe()}.  `|A(N) - ({q}) / log ε · log N| ≤ K` for all\n"
        f"large `N`, `ε = {u} + {v}√{D}`.  The certificate (roots, cycle lengths modulo the filter\n"
        f"modulus, admissible states) is computed and checked by the kernel; only the constant is\n"
        f"stated here. -/\n"
        f"theorem {name}_count : ∃ K : ℝ, ∀ N : ℕ, (4 * {lz(a)} * {lz(B0)} : ℤ).natAbs + 1 ≤ N →\n"
        f"    |((FilteredPell.countQuad {args} N : ℕ) : ℝ) -\n"
        f"      ((({q.numerator} : ℚ) / {q.denominator} : ℚ) : ℝ) /\n"
        f"        Real.log (PellExact.eps (4 * (4 * {lz(a)} * {lz(A0)})) {u} {v}) * Real.log N| ≤ K :=\n"
        f"  FilteredPell.quadRoot_count_auto {named} {Ls} (by decide) (by decide)\n"
        f"    (u := {u}) (v := {v}) (by decide) (by decide) (by decide +kernel) (by decide +kernel)\n")


def first_theorem(name, con, plan):
    """`n₀` is the least solution: minimality from the orbit order and the computed roots."""
    cc = count_cert(con)
    if cc is None or cc['Ymax'] > 3000 or max([P for _, (P, _) in cc['roots']] + [0]) > 400:
        return None
    a, b, c, A0, B0, C0, L, Ls, u, v, named, M, good, abc = _auto_args(con)
    if not 2 * 4 * a * A0 + 4 * a * B0 > 0:
        return None
    n0, ws = next(iter(plan.iter_hits(10 ** 60)))
    args, _ = qh_args(a, b, c, (C0, B0, A0), L)
    return n0, (
        f"/-- **The least solution of `{name}`** is `n = {n0}` (`y = {ws[0]}`): every root's orbit up to\n"
        f"its first point with `X ≥ 2An₀ + B` has no admissible point (checked exactly), and the roots\n"
        f"are complete (computed certificate). -/\n"
        f"theorem {name}_first : IsLeast (FilteredPell.QuadHits {args}) {n0} :=\n"
        f"  FilteredPell.quadRoot_isLeast {named} {Ls} (by decide) (by decide) (u := {u}) (v := {v})\n"
        f"    (by decide) (by decide) (by decide +kernel)\n"
        f"    (FilteredPell.buildCert {M} {good} {abc} {u} {v})\n"
        f"    (by decide +kernel) (by decide) {n0} 400 (by decide +kernel)\n"
        f"    ⟨by norm_num, {ws[0]}, by simp [FilteredPell.Dom], by norm_num⟩\n")


def family_theorem(name, con, plan):
    """A member of Mordell's family k = (4t - 1)^3 - 4m^2, through its affine substitution."""
    fam = plan.data['family']
    r, s, k = match_affine_cube(plan.reduced.F)
    Fs = poly_lean(con.F)
    t, m, j, m1, u = fam['t'], fam['m'], fam['j'], fam['m1'], fam['u']
    return (
        f"/-- Plan `{name}`: {con.describe()}.  The model is `m^2 = t^3 + ({k})` with `t = {r}n + ({s})`,\n"
        f"and `{k} = (4·{t} - 1)^3 - 4·{m}^2` with `{m} = 2^{j}·{m1}`, `{m1} ∣ {u}^2 + 1`: a member of\n"
        f"Mordell's family, which has no integral point (`MordellFamily.no_points`). -/\n"
        f"theorem {name} (n : ℕ) (m : ℤ) : ¬ (1 ≤ n ∧ m ^ 2 = {Fs}) := by\n"
        f"  rintro ⟨-, h⟩\n"
        f"  refine MordellFamily.no_points_cert {lz(t)} {m} {m1} {u} {j} (by norm_num) (by decide)\n"
        f"    ({r} * (n : ℤ) + ({s})) m ?_\n"
        f"  rw [h]; ring\n")


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
           ('plan_far_first_hit', QuadraticRootConstraint(2, 1, 0, (1, 0, 263), 'pos')),
           ('plan_late_certified', QuadraticRootConstraint(41, 1, 3, (3, 0, 1), 'nonneg')),
           ('plan_mordell_family_1', PowerConstraint(parse_poly('(n + 5)**3 + 1025127'), 2)),
           ('plan_mordell_family_2', PowerConstraint(parse_poly('(2*n + 1)**3 + 29115'), 2))]
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
    out = ['import PerfectPower.PlanCerts', 'import PerfectPower.FilteredAuto', 'import PerfectPower.MordellFamily', '',
           '/-! Machine-generated by `python3 python/make_lean_plans.py`; do not edit.  One theorem per',
           'catalogued compiler plan, about the original constraint (see `PlanCerts.lean`). -/', '',
           'namespace PerfectPower.Generated.Plans', '', 'open PerfectPower', '']
    receipt = []
    for name, con in catalogue():
        plan = compile_constraint(con)
        if plan.method.startswith('affine transport'):
            thm = transport_theorem(name, con, plan)
        elif plan.method.startswith("Mordell's family"):
            thm = family_theorem(name, con, plan)
        else:
            thm = filtered_theorem(name, con, plan)
        if thm is None:
            raise SystemExit(f'no certificate for {name}: {plan.method}')
        out.append(thm)
        extra = []
        if plan.status == STRUCTURED_INFINITE and plan.data.get('filter_decision'):
            ct = count_theorem(name, con, plan)
            if ct is not None:
                out.append(ct)
                extra.append(f'PerfectPower.Generated.Plans.{name}_count')
        if plan.status == STRUCTURED_INFINITE and plan.data.get('filter_decision'):
            ft = first_theorem(name, con, plan)
            if ft is not None:
                out.append(ft[1])
                extra.append(f'PerfectPower.Generated.Plans.{name}_first')
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
