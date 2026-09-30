import PerfectPower.FilteredPell
import PerfectPower.MordellMinus4
import PerfectPower.MordellMinus5
import PerfectPower.MordellMinus6

/-!
# Plan certificates: the compiler's chosen path, checked in Lean

The Python compiler (`python/perfectpower/compiler.py`) picks a path for a constraint.  This
file gives the Lean statements that path must instantiate, so that `python/make_lean_plans.py`
can emit, for each plan, a theorem about the **original** constraint that the kernel checks.

* **Transport plans** (a solved Mordell curve reached through a reduction chain).  The chain is
  built from `Reduction.Exact.comp`, `Reduction.affine` and `Reduction.quadratic`, and the
  complete list is pulled back by `Exact.pull_complete`; the generated file only supplies the
  polynomial identity (by `linear_combination`) and computes the pull-back by `decide`.
  `power_transport`: `m^2 = (rn + s)^3 + k`.  `root_transport`: `a y^2 + b y + c = F(n)` with
  `4a F(n) + b^2 - 4ac = (rn + s)^3 + k`.  The complete lists: `pairs_m2`, `pairs_m4`,
  `pairs_m13`, and `pairs_empty` for curves without integral points.
* **Filtered Pell plans.**  `FilteredPell.quadRoot_infinite_of_witness` (one admissible
  solution) and `quadRoot_subset_of_cert`: a kernel-checked `FinCert` plus one inequality put every
  solution in `[1, Nb]`; the Python plan then lists the solutions in that range by direct
  evaluation.
-/

namespace PerfectPower.PlanCerts

open PerfectPower Reduction FilteredPell

/-! ### Complete lists of the solved curves, as sets of pairs -/

theorem pairs_m2 (q : ℤ × ℤ) :
    q.2 ^ 2 = q.1 ^ 3 + (-2) ↔ q ∈ ({(3, 5), (3, -5)} : Finset (ℤ × ℤ)) := by
  rw [show q.1 ^ 3 + (-2) = q.1 ^ 3 - 2 by ring]
  exact cube_sub_two_pairs q

theorem pairs_m4 (q : ℤ × ℤ) :
    q.2 ^ 2 = q.1 ^ 3 + (-4) ↔
      q ∈ ({(2, 2), (2, -2), (5, 11), (5, -11)} : Finset (ℤ × ℤ)) := by
  obtain ⟨x, y⟩ := q
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  rw [show x ^ 3 + (-4) = x ^ 3 - 4 by ring, MordellMinus4.points]
  tauto

theorem pairs_m13 (q : ℤ × ℤ) :
    q.2 ^ 2 = q.1 ^ 3 + (-13) ↔ q ∈ ({(17, 70), (17, -70)} : Finset (ℤ × ℤ)) := by
  obtain ⟨x, y⟩ := q
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  rw [show x ^ 3 + (-13) = x ^ 3 - 13 by ring, MordellMinus13.points]
  tauto

theorem pairs_empty {k : ℤ} (h : ∀ x y : ℤ, y ^ 2 ≠ x ^ 3 + k) (q : ℤ × ℤ) :
    q.2 ^ 2 = q.1 ^ 3 + k ↔ q ∈ (∅ : Finset (ℤ × ℤ)) := by
  simp only [Finset.notMem_empty, iff_false]
  exact h q.1 q.2

theorem no_points_m5 (x y : ℤ) : y ^ 2 ≠ x ^ 3 + (-5) := by
  rw [show x ^ 3 + (-5) = x ^ 3 - 5 by ring]; exact MordellMinus5.no_points x y

theorem no_points_m6 (x y : ℤ) : y ^ 2 ≠ x ^ 3 + (-6) := by
  rw [show x ^ 3 + (-6) = x ^ 3 - 6 by ring]; exact MordellMinus6.no_points x y

/-! ### Transport chains -/

/-- The chain for `m^2 = F(n)` with `F(n) = (rn + s)^3 + k`: one affine step. -/
def powerChain (k : ℤ) {r : ℤ} (hr : r ≠ 0) (s : ℤ) (F : ℕ → ℤ)
    (hF : ∀ n : ℕ, F n = (r * n + s) ^ 3 + k) :
    Exact (fun p : ℕ × ℤ => 1 ≤ p.1 ∧ p.2 ^ 2 = F p.1) (fun q : ℤ × ℤ => q.2 ^ 2 = q.1 ^ 3 + k) :=
  (affine (fun q : ℤ × ℤ => q.2 ^ 2 = q.1 ^ 3 + k) hr s).congr fun p => by
    simp only [hF]

/-- **Transport plan, power form**: completeness pulled back through the chain. -/
theorem power_transport {k : ℤ} {T : Finset (ℤ × ℤ)} (hT : ∀ q, q.2 ^ 2 = q.1 ^ 3 + k ↔ q ∈ T)
    {r : ℤ} (hr : r ≠ 0) (s : ℤ) (F : ℕ → ℤ) (hF : ∀ n : ℕ, F n = (r * n + s) ^ 3 + k)
    (n : ℕ) (m : ℤ) :
    (1 ≤ n ∧ m ^ 2 = F n) ↔ (n, m) ∈ (powerChain k hr s F hF).pull T :=
  (powerChain k hr s F hF).pull_complete hT (n, m)

/-- The chain for `a y^2 + b y + c = F(n)`, `y ∈ Y`, when the discriminant
`4a F(n) + b^2 - 4ac` is `(rn + s)^3 + k`: quadratic, then affine. -/
def rootChain (k : ℤ) {a : ℤ} (ha : a ≠ 0) (b c : ℤ) (F : ℕ → ℤ) (Y : ℤ → Prop)
    [DecidablePred Y] {r : ℤ} (hr : r ≠ 0) (s : ℤ)
    (hF : ∀ n : ℕ, 4 * a * F n + b ^ 2 - 4 * a * c = (r * n + s) ^ 3 + k) :
    Exact (fun p : ℕ × ℤ => 1 ≤ p.1 ∧ Y p.2 ∧ a * p.2 ^ 2 + b * p.2 + c = F p.1)
      (fun q : ℤ × ℤ => q.2 ^ 2 = q.1 ^ 3 + k) :=
  (quadratic ha b c F Y).comp
    ((affine (fun q : ℤ × ℤ => q.2 ^ 2 = q.1 ^ 3 + k) hr s).congr fun p => by
      simp only [hF])

/-- **Transport plan, quadratic-root form.** -/
theorem root_transport {k : ℤ} {T : Finset (ℤ × ℤ)} (hT : ∀ q, q.2 ^ 2 = q.1 ^ 3 + k ↔ q ∈ T)
    {a : ℤ} (ha : a ≠ 0) (b c : ℤ) (F : ℕ → ℤ) (Y : ℤ → Prop) [DecidablePred Y] {r : ℤ}
    (hr : r ≠ 0) (s : ℤ) (hF : ∀ n : ℕ, 4 * a * F n + b ^ 2 - 4 * a * c = (r * n + s) ^ 3 + k)
    (n : ℕ) (y : ℤ) :
    (1 ≤ n ∧ Y y ∧ a * y ^ 2 + b * y + c = F n) ↔
      (n, y) ∈ (rootChain k ha b c F Y hr s hF).pull T :=
  (rootChain k ha b c F Y hr s hF).pull_complete hT (n, y)

/-! ### Filtered Pell plans: a complete search range -/

/-- From the certificate's inequality to a range: if `K ≤ (2A(Nb+1) + B)^2` with
`2A(Nb+1) + B > 0`, every solution has `n ≤ Nb` (below the vertex, `2An + B ≤ 0`, it does too). -/
theorem quadRoot_subset_of_cert {a b c A₀ B₀ C₀ u v : ℤ} (L : Option ℤ) (ha : a ≠ 0)
    (hA : 0 < 4 * a * A₀) (hu1 : 1 < u) (hv : 0 < v)
    (hu : u ^ 2 - 4 * (4 * a * A₀) * v ^ 2 = 1) (cert : FinCert)
    (hc : cert.check (4 * (4 * a * A₀) * a).natAbs (quadGoodB a b (4 * a * A₀) (4 * a * B₀) L)
      (4 * a * A₀) (4 * a * B₀) (4 * a * C₀ + b ^ 2 - 4 * a * c) u v = true)
    (Nb : ℕ) (hpos : 0 < 2 * (4 * a * A₀) * ((Nb : ℤ) + 1) + 4 * a * B₀)
    (hK : (4 * a * B₀) ^ 2 - 4 * (4 * a * A₀) * (4 * a * C₀ + b ^ 2 - 4 * a * c) +
        4 * (4 * a * A₀) * thr a b L ^ 2 ≤ (2 * (4 * a * A₀) * ((Nb : ℤ) + 1) + 4 * a * B₀) ^ 2) :
    QuadHits a b c A₀ B₀ C₀ L ⊆ Set.Iic Nb := by
  intro n hn
  simp only [Set.mem_Iic]
  by_contra hlt
  push_neg at hlt
  have hmono : 2 * (4 * a * A₀) * ((Nb : ℤ) + 1) + 4 * a * B₀ ≤ 2 * (4 * a * A₀) * n + 4 * a * B₀ := by
    nlinarith
  have hX : 0 < 2 * (4 * a * A₀) * n + 4 * a * B₀ := by linarith
  have hb := quadRoot_bound_of_cert L ha hA hu1 hv hu cert hc n hn hX
  nlinarith

end PerfectPower.PlanCerts
