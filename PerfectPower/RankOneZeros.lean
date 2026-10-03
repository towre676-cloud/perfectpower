import PerfectPower.RankOne
import PerfectPower.SkolemZeros

/-!
# Rank-one sources with several solutions

`RankOne.source` needs the `z²` coordinate of `ηⁿ` to vanish only at `n = 0`, so it cannot
handle a source with two or more solutions.  Here `SkolemZeros.corner_zeros` replaces
`SkolemP.corner_zero`.  Per residue class `r < M`, the test is either
* `p ∤ (g^r)₂`, or
* `(g^r)₂ = 0` and `p ∤ ((g^{M+r})₂ − (g^r)₂)/p`.

With that test, every solution of `−u³ + P u v² + Q v³ = 1` lies in the finite list `cands`.  The
list is read off the powers `η^N` (`N < M`) and `ε^N` (`N < M'`) (`source_sub`).  A generated module
then filters `cands` by the equation with one kernel check (`source_list`).  The `(D·Aʳ)₂₀` test runs
on `ℤ[z]` powers: `p · (D Aʳ)₂₀ = (g^{M+r})₂ − (g^r)₂` because `A^M = 1 + pD`.
-/

namespace PerfectPower.RankOneZeros

open PerfectPower UnitBox UnitPremises RankOne Matrix

/-- The per-class Skolem tests for the finite zero set, on powers in `ℤ[z]`. -/
def skolemZB (P Q : ℤ) (g : Z3) (p M : ℕ) : Bool :=
  decide (0 < M) &&
    (List.finRange 3).all (fun i => (List.finRange 3).all fun j =>
      decide ((p : ℤ) ∣ Mx P Q (pow P Q g M) i j - (1 : Matrix (Fin 3) (Fin 3) ℤ) i j)) &&
    (List.range M).all (fun r => decide (¬ (p : ℤ) ∣ (pow P Q g r).2.2) ||
      (decide ((pow P Q g r).2.2 = 0) &&
        decide (¬ (p : ℤ) ∣ ((pow P Q g (M + r)).2.2 - (pow P Q g r).2.2) / p)))

lemma pow_add' (P Q : ℤ) (g : Z3) (a b : ℕ) : Mx P Q (pow P Q g (a + b)) = Mx P Q (pow P Q g a) * Mx P Q (pow P Q g b) := by
  rw [Mx_pow, Mx_pow, Mx_pow, pow_add]

theorem zeros_of {P Q : ℤ} {g : Z3} {p M : ℕ} (hp : 0 < p) (h : skolemZB P Q g p M = true) :
    ∃ D : Matrix (Fin 3) (Fin 3) ℤ, 0 < M ∧ Mx P Q g ^ M = 1 + p • D ∧
      ∀ r, r < M → ¬ (p : ℤ) ∣ (Mx P Q g ^ r) 2 0 ∨
        ((Mx P Q g ^ r) 2 0 = 0 ∧ ¬ (p : ℤ) ∣ (D * Mx P Q g ^ r) 2 0) := by
  simp only [skolemZB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange,
    true_implies, List.mem_range, Bool.or_eq_true] at h
  obtain ⟨⟨hM, hdiv⟩, hr⟩ := h
  set D : Matrix (Fin 3) (Fin 3) ℤ :=
    Matrix.of fun i j => (Mx P Q (pow P Q g M) i j - (1 : Matrix (Fin 3) (Fin 3) ℤ) i j) / p with hDdef
  have hA : Mx P Q g ^ M = 1 + p • D := by
    rw [← Mx_pow]
    ext i j
    rw [Matrix.add_apply, Matrix.smul_apply, hDdef, Matrix.of_apply, nsmul_eq_mul, Int.mul_ediv_cancel' (hdiv i j)]
    ring
  refine ⟨D, hM, hA, fun r hrM => ?_⟩
  rw [← Mx_pow, (Mx_col P Q _).2.2]
  rcases hr r hrM with h' | ⟨h0, h1⟩
  · exact Or.inl h'
  · refine Or.inr ⟨h0, ?_⟩
    have hpD : (p : ℤ) * (D * Mx P Q g ^ r) 2 0 = (pow P Q g (M + r)).2.2 - (pow P Q g r).2.2 := by
      have e : (p • D) * Mx P Q g ^ r = Mx P Q (pow P Q g (M + r)) - Mx P Q (pow P Q g r) := by
        rw [pow_add', Mx_pow P Q g M, hA, add_mul, one_mul, Mx_pow]; abel
      have e2 := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℤ => A 2 0) e
      simp only at e2
      rw [smul_mul_assoc, Matrix.smul_apply, nsmul_eq_mul, Matrix.sub_apply, (Mx_col P Q _).2.2,
        (Mx_col P Q _).2.2] at e2
      exact e2
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
    rw [← hpD, Int.mul_ediv_cancel_left _ hp0] at h1
    rw [Mx_pow]; exact h1

/-- The candidate solutions: `±` the first two coordinates of `η^N` (`N < M`) and `ε^N` (`N < M'`),
as `(u, v)` with `u − vz = ±g`. -/
def cands (P Q : ℤ) (η ε : Z3) (M M' : ℕ) : List (ℤ × ℤ) :=
  ((List.range M).map (pow P Q η) ++ (List.range M').map (pow P Q ε)).flatMap
    fun g => [(g.1, -g.2.1), (-g.1, g.2.1)]

/-- **Every solution is a candidate.** -/
theorem source_sub {P Q : ℤ} {η ε : Z3} (h1 : mul P Q η ε = (1, 0, 0)) (h2 : mul P Q ε η = (1, 0, 0))
    (hnη : nrm P Q η = 1) (hnε : nrm P Q ε = 1) {c : Cert} (hc : condB P Q η c = true)
    (hbox : slabB P Q η c = true) {p : ℕ} [Fact p.Prime] (hp3 : 3 ≤ p) {M M' : ℕ}
    (hηB : skolemZB P Q η p M = true) (hεB : skolemZB P Q ε p M' = true) (u v : ℤ)
    (h : -u ^ 3 + P * u * v ^ 2 + Q * v ^ 3 = 1) : (u, v) ∈ cands P Q η ε M M' := by
  have hp0 : 0 < p := by omega
  obtain ⟨D, hM, hA, hcls⟩ := zeros_of hp0 hηB
  obtain ⟨D', hM', hA', hcls'⟩ := zeros_of hp0 hεB
  have hn : nrm P Q (u, -v, 0) = -1 := by simp only [nrm]; linear_combination -h
  obtain ⟨n, hMx⟩ := units_eq h1 h2 hnη hnε hc hbox (u, -v, 0) (Or.inr hn)
  rw [← Mx_zp P Q η ε h1 h2] at hMx
  set g := zp P Q η ε n with hg
  have hcol := Mx_col P Q (u, -v, 0)
  have hgc := Mx_col P Q g
  simp only at hcol
  -- `(u, −v, 0) = ±g` coordinatewise
  have key : (u = g.1 ∧ -v = g.2.1 ∧ 0 = g.2.2) ∨ (u = -g.1 ∧ -v = -g.2.1 ∧ 0 = -g.2.2) := by
    rcases hMx with hM2 | hM2 <;> rw [hM2] at hcol
    · left; exact ⟨hcol.1.symm.trans hgc.1, hcol.2.1.symm.trans hgc.2.1, hcol.2.2.symm.trans hgc.2.2⟩
    · right
      simp only [Matrix.neg_apply] at hcol
      exact ⟨by rw [← hcol.1, hgc.1], by rw [← hcol.2.1, hgc.2.1], by rw [← hcol.2.2, hgc.2.2]⟩
  have hz : g.2.2 = 0 := by rcases key with k | k <;> linarith [k.2.2]
  have hmem : g ∈ (List.range M).map (pow P Q η) ++ (List.range M').map (pow P Q ε) := by
    simp only [hg, zp] at hz ⊢
    split_ifs at hz ⊢ with hn0
    · have hz' : (Mx P Q η ^ n.toNat) 2 0 = 0 := by rw [← Mx_pow, (Mx_col P Q _).2.2]; exact hz
      have := SkolemZeros.corner_zeros hp3 hM hA hcls n.toNat hz'
      exact List.mem_append_left _ (List.mem_map.mpr ⟨n.toNat, List.mem_range.mpr this, rfl⟩)
    · have hz' : (Mx P Q ε ^ (-n).toNat) 2 0 = 0 := by rw [← Mx_pow, (Mx_col P Q _).2.2]; exact hz
      have := SkolemZeros.corner_zeros hp3 hM' hA' hcls' (-n).toNat hz'
      exact List.mem_append_right _ (List.mem_map.mpr ⟨(-n).toNat, List.mem_range.mpr this, rfl⟩)
  refine List.mem_flatMap.mpr ⟨g, hmem, ?_⟩
  rcases key with ⟨hu, hv, _⟩ | ⟨hu, hv, _⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]; left; exact ⟨hu, by linarith⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]; right; exact ⟨hu, by linarith⟩

/-- `F(u, v) = −u³ + P u v² + Q v³`. -/
def F (P Q : ℤ) (x : ℤ × ℤ) : ℤ := -x.1 ^ 3 + P * x.1 * x.2 ^ 2 + Q * x.2 ^ 3

/-- The kernel filter: the candidates that solve the equation are exactly `L`. -/
def listB (P Q : ℤ) (η ε : Z3) (M M' : ℕ) (L : List (ℤ × ℤ)) : Bool :=
  (cands P Q η ε M M').all (fun x => decide (F P Q x = 1) == decide (x ∈ L)) && L.all (fun x => decide (F P Q x = 1))

/-- **The source theorem with a finite solution list.** -/
theorem source_list {P Q : ℤ} {η ε : Z3} (h1 : mul P Q η ε = (1, 0, 0)) (h2 : mul P Q ε η = (1, 0, 0))
    (hnη : nrm P Q η = 1) (hnε : nrm P Q ε = 1) {c : Cert} (hc : condB P Q η c = true)
    (hbox : slabB P Q η c = true) {p : ℕ} [Fact p.Prime] (hp3 : 3 ≤ p) {M M' : ℕ}
    (hηB : skolemZB P Q η p M = true) (hεB : skolemZB P Q ε p M' = true) {L : List (ℤ × ℤ)}
    (hL : listB P Q η ε M M' L = true) (u v : ℤ) :
    -u ^ 3 + P * u * v ^ 2 + Q * v ^ 3 = 1 ↔ (u, v) ∈ L := by
  simp only [listB, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at hL
  obtain ⟨hc1, hc2⟩ := hL
  constructor
  · intro h
    have hm := source_sub h1 h2 hnη hnε hc hbox hp3 hηB hεB u v h
    have := hc1 _ hm
    simp only [F, h, decide_true] at this
    exact of_decide_eq_true this.symm
  · intro h
    have := hc2 _ h
    simpa [F] using this
