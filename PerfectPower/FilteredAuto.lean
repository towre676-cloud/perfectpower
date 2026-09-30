import PerfectPower.FilteredCount

/-!
# Compact certificates: Lean computes the roots, periods and marks itself

`CountCert` carries tables: the roots, and each root's cycle length and number of admissible
states.  Here Lean **builds** that data by kernel
evaluation (`buildCert`) and then **checks** it with the proved checker (`CountCert.check`), so a
generated theorem carries only the claimed constant.

* `cycleLen`: the length of a residue cycle, found by iterating until the start returns (checked).
* `autoCount`: build, check, and return `∑ g / P` as a rational; `quadRoot_count_auto` turns
  `autoCount … = some q` into the count theorem with constant `q / log ε`.

**The first solution.**  `quadRoot_isLeast_auto`: if every root's orbit, up to its first point
with `X ≥ X₀ = 2A n₀ + B`, contains no admissible point (checked exactly, not only modulo `M`),
and `n₀` is a solution, then `n₀` is the **least** solution.  The proof: every solution lies on
the orbit of a root (`exists_root`), the roots are the certified ones (`roots_complete_of_check`),
and `X` increases along an orbit (`orbit_fst_mono`), so a smaller solution would be one of the
checked points.
-/

namespace PerfectPower.FilteredPell

open PerfectPower PellExact RationalYun Finset
open scoped Classical

/-! ### Cycle lengths (not trusted) -/

/-- The number of steps until `f` returns to `s₀` (with fuel). -/
def cycleLen (f : ℤ × ℤ → ℤ × ℤ) (s₀ : ℤ × ℤ) : ℕ → ℤ × ℤ → ℕ → ℕ
  | 0, _, k => k
  | fuel + 1, s, k => if f s = s₀ then k + 1 else cycleLen f s₀ fuel (f s) (k + 1)

/-! ### Building the count certificate -/

/-- The certificate, computed: the box, and for every root its cycle length and marks. -/
def buildCert (M : ℕ) (goodB : ℤ × ℤ → Bool) (A B C u v : ℤ) : CountCert :=
  let D := 4 * A
  let Δ := B ^ 2 - 4 * A * C
  let Ymax : ℕ := (isqrtZ (|Δ| * u ^ 2 / D)).toNat + 1
  let roots : List ((ℤ × ℤ) × (ℕ × ℕ)) := (List.range (Ymax + 1)).filterMap fun Y =>
    let t := Δ + D * (Y : ℤ) ^ 2
    let q := isqrtZ t
    if 0 < q ∧ q * q = t ∧ solB D Δ (pred D u v (q, (Y : ℤ))) = false then
      let s₀ : ℤ × ℤ := (q % M, (Y : ℤ) % M)
      let P := cycleLen (stepInt M D u v) s₀ (M * M) s₀ 0
      some ((q, (Y : ℤ)), (P, orbitCount (stepInt M D u v) goodB P s₀ 0))
    else none
  ⟨Ymax, roots⟩

/-- Build and check; the claimed constant `∑ g / P`. -/
def autoCount (M : ℕ) (goodB : ℤ × ℤ → Bool) (A B C u v : ℤ) : Option ℚ :=
  let c := buildCert M goodB A B C u v
  if c.check M goodB A B C u v then some (c.roots.map fun e => (e.2.2 : ℚ) / e.2.1).sum
  else none

/-- **The count from a computed certificate.** -/
theorem quadRoot_count_auto {a b c A₀ B₀ C₀ u v : ℤ} (L : Option ℤ) (ha : a ≠ 0)
    (hA : 0 < 4 * a * A₀) (hu1 : 1 < u) (hv : 0 < v)
    (hu : u ^ 2 - 4 * (4 * a * A₀) * v ^ 2 = 1) {q : ℚ}
    (h : autoCount (4 * (4 * a * A₀) * a).natAbs (quadGoodB a b (4 * a * A₀) (4 * a * B₀) L)
      (4 * a * A₀) (4 * a * B₀) (4 * a * C₀ + b ^ 2 - 4 * a * c) u v = some q) :
    ∃ K : ℝ, ∀ N : ℕ, (4 * a * B₀).natAbs + 1 ≤ N →
      |((countQuad a b c A₀ B₀ C₀ L N : ℕ) : ℝ) -
        (q : ℝ) / Real.log (eps (4 * (4 * a * A₀)) u v) * Real.log N| ≤ K := by
  unfold autoCount at h
  dsimp only at h
  split_ifs at h with hc
  obtain ⟨K, hK⟩ := quadRoot_count_of_cert L ha hA hu1 hv hu _ hc
  refine ⟨K, fun N hN => ?_⟩
  have e : ((buildCert (4 * (4 * a * A₀) * a).natAbs (quadGoodB a b (4 * a * A₀) (4 * a * B₀) L)
      (4 * a * A₀) (4 * a * B₀) (4 * a * C₀ + b ^ 2 - 4 * a * c) u v).roots.map
        fun e => (e.2.2 : ℝ) / e.2.1).sum = (q : ℝ) := by
    rw [← Option.some.inj h, Rat.cast_list_sum, List.map_map]
    congr 1
    apply List.map_congr_left
    intro e _
    simp
  have := hK N hN
  rwa [e] at this

/-! ### The first solution -/

/-- Along the orbit of a quadrant solution, `X` is increasing. -/
lemma orbit_fst_mono {D u v Δ : ℤ} (hD : 0 ≤ D) (hu : u ^ 2 - D * v ^ 2 = 1) (hu1 : 1 < u)
    (hv : 0 ≤ v) {ρ : ℤ × ℤ} (hρ : Sol D Δ ρ) {j k : ℕ} (hjk : j ≤ k) :
    (unitOrbit D u v ρ j).1 ≤ (unitOrbit D u v ρ k).1 := by
  induction k with
  | zero => rw [Nat.le_zero.mp hjk]
  | succ k ih =>
    rcases Nat.lt_or_ge j (k + 1) with h | h
    · have := ih (by omega)
      rw [orbit_succ]
      have := unitAct_fst_gt hD hu1 hv (orbit_sol hD hu hu1.le hv hρ k) (u := u) (v := v)
      linarith
    · rw [show j = k + 1 by omega]

/-- The listed roots are all the roots, when the count certificate checks. -/
lemma roots_complete_of_check {M : ℕ} {goodB : ℤ × ℤ → Bool} {A B C u v : ℤ} (hA : 0 < A)
    (hu1 : 1 < u) (hv : 0 < v) (hu : u ^ 2 - 4 * A * v ^ 2 = 1) {c : CountCert}
    (hc : c.check M goodB A B C u v = true) (ρ : ℤ × ℤ)
    (hρ : IsRoot (4 * A) u v (B ^ 2 - 4 * A * C) ρ) : ρ ∈ c.roots.map Prod.fst := by
  simp only [CountCert.check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hc
  obtain ⟨⟨⟨-, hbox⟩, hlist⟩, -⟩ := hc
  have hD : 0 < 4 * A := by positivity
  have hρbox := root_in_box hD hu1 hv hu hρ
  obtain ⟨hρX, hρY, hρN⟩ := hρ.1
  have hρY' : ρ.2 < (c.Ymax : ℤ) + 1 := by
    by_contra h'
    push_neg at h'
    have : 4 * A * ((c.Ymax : ℤ) + 1) ^ 2 ≤ 4 * A * ρ.2 ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hD.le
      exact pow_le_pow_left₀ (by positivity) h' 2
    linarith [le_abs_self (B ^ 2 - 4 * A * C)]
  have hYn : ρ.2.toNat < c.Ymax + 1 := by omega
  have hYc : ((ρ.2.toNat : ℕ) : ℤ) = ρ.2 := Int.toNat_of_nonneg hρY
  have ht : B ^ 2 - 4 * A * C + 4 * A * ((ρ.2.toNat : ℕ) : ℤ) ^ 2 = ρ.1 * ρ.1 := by
    rw [hYc]; linarith
  rcases hlist _ hYn with hneg | ⟨⟨hq0, hq1, hq2⟩, hsq⟩
  · rw [ht] at hneg; nlinarith
  rw [ht] at hq0 hq1 hq2 hsq
  generalize isqrtZ (ρ.1 * ρ.1) = q at hq0 hq1 hq2 hsq
  have hqX : q = ρ.1 := by
    have h1 : q ≤ ρ.1 := by nlinarith
    have h2 : ρ.1 < q + 1 := by nlinarith
    omega
  rw [hqX, hYc] at hsq
  rcases hsq with ((hnot | hnot) | hpred) | hmem
  · exact absurd rfl hnot
  · exact absurd hρX hnot
  · exact absurd ((solB_iff _).mp hpred) hρ.2
  · exact hmem

/-- The exact filter of the quadratic-root constraint, as a Boolean. -/
def quadGoodExactB (a b A B : ℤ) (L : Option ℤ) (p : ℤ × ℤ) : Bool :=
  decide (2 * A ∣ p.1 - B) && [1, -1].any fun s : ℤ =>
    decide (2 * a ∣ s * p.2 - b) &&
      (match L with
       | none => true
       | some l => decide (l ≤ (s * p.2 - b) / (2 * a)))

lemma quadGoodExactB_iff {a b A B : ℤ} (L : Option ℤ) (ha : a ≠ 0) (p : ℤ × ℤ) :
    (quadFilter a b A B L ha).good p ↔ quadGoodExactB a b A B L p = true := by
  cases L <;>
  simp [quadFilter, quadGoodExactB, Dom, Finset.mem_insert, Finset.mem_singleton]

/-- The first point of an orbit with `X ≥ X₀` (with fuel). -/
def firstGE (D u v X₀ : ℤ) (ρ : ℤ × ℤ) : ℕ → ℕ → ℕ
  | 0, j => j
  | fuel + 1, j => if X₀ ≤ (unitOrbit D u v ρ j).1 then j else firstGE D u v X₀ ρ fuel (j + 1)

/-- The minimality check: every root's orbit, below its first point with `X ≥ X₀`, has no
admissible point. -/
def minCheck (goodExact : ℤ × ℤ → Bool) (D u v X₀ : ℤ) (roots : List (ℤ × ℤ)) (fuel : ℕ) :
    Bool :=
  roots.all fun ρ =>
    let J := firstGE D u v X₀ ρ fuel 0
    decide (X₀ ≤ (unitOrbit D u v ρ J).1) &&
      (List.range J).all fun j => !goodExact (unitOrbit D u v ρ j)

/-- **The least solution.**  If the count certificate checks (so its roots are all the roots),
the minimality check passes for `X₀ = 2A n₀ + B`, every `n ≥ 1` lies past the vertex, and `n₀`
is a solution, then `n₀` is the least solution. -/
theorem quadRoot_isLeast {a b c A₀ B₀ C₀ u v : ℤ} (L : Option ℤ) (ha : a ≠ 0)
    (hA : 0 < 4 * a * A₀) (hu1 : 1 < u) (hv : 0 < v)
    (hu : u ^ 2 - 4 * (4 * a * A₀) * v ^ 2 = 1) (cert : CountCert)
    (hc : cert.check (4 * (4 * a * A₀) * a).natAbs (quadGoodB a b (4 * a * A₀) (4 * a * B₀) L)
      (4 * a * A₀) (4 * a * B₀) (4 * a * C₀ + b ^ 2 - 4 * a * c) u v = true)
    (hvert : 0 < 2 * (4 * a * A₀) + 4 * a * B₀) (n₀ : ℕ) (fuel : ℕ)
    (hmin : minCheck (quadGoodExactB a b (4 * a * A₀) (4 * a * B₀) L) (4 * (4 * a * A₀)) u v
      (2 * (4 * a * A₀) * n₀ + 4 * a * B₀) (cert.roots.map Prod.fst) fuel = true)
    (hn₀ : n₀ ∈ QuadHits a b c A₀ B₀ C₀ L) :
    IsLeast (QuadHits a b c A₀ B₀ C₀ L) n₀ := by
  refine ⟨hn₀, fun n hn => ?_⟩
  have hD : 0 < 4 * (4 * a * A₀) := by positivity
  by_contra hlt
  push_neg at hlt
  have hn1 : 1 ≤ n := hn.1
  have hX : 0 < 2 * (4 * a * A₀) * n + 4 * a * B₀ := by
    have : (2 * (4 * a * A₀) : ℤ) * 1 ≤ 2 * (4 * a * A₀) * n :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hn1) (by omega)
    linarith
  obtain ⟨-, Y, hsol, hgood⟩ := (quadHits_iff L ha hA n hX).mp hn
  obtain ⟨ρ, j, hρ, hj⟩ := exists_root hD hu1 hv hu _ _ rfl hsol
  have hρmem := roots_complete_of_check hA hu1 hv hu hc ρ hρ
  simp only [minCheck, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    List.mem_range, Bool.not_eq_true'] at hmin
  obtain ⟨hJ, hbefore⟩ := hmin ρ hρmem
  have hlt' : 2 * (4 * a * A₀) * (n : ℤ) + 4 * a * B₀ < 2 * (4 * a * A₀) * n₀ + 4 * a * B₀ := by
    have hA2 : 0 < 2 * (4 * a * A₀) := by positivity
    have hnn : (n : ℤ) < n₀ := by exact_mod_cast hlt
    exact add_lt_add_right (mul_lt_mul_of_pos_left hnn hA2) _
  have hXj : (unitOrbit (4 * (4 * a * A₀)) u v ρ j).1 = 2 * (4 * a * A₀) * n + 4 * a * B₀ := by
    rw [hj]
  have hjJ : j < firstGE (4 * (4 * a * A₀)) u v (2 * (4 * a * A₀) * n₀ + 4 * a * B₀) ρ fuel 0 := by
    by_contra hge
    push_neg at hge
    have hmono := orbit_fst_mono hD.le hu hu1 hv.le hρ.1 hge
    linarith
  have hfalse := hbefore j hjJ
  have htrue := (quadGoodExactB_iff L ha _).mp hgood
  rw [hj, htrue] at hfalse
  exact absurd hfalse (by decide)

end PerfectPower.FilteredPell
