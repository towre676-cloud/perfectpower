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

/-! ### Recentring and auxiliary primes (`SkolemZeros.corner_zeros2`) -/

/-- `[x, x g, x g², …]`, `n` entries. -/
def pl (P Q : ℤ) (g : Z3) : Z3 → ℕ → List Z3
  | _, 0 => []
  | x, n + 1 => x :: pl P Q g (mul P Q x g) n

lemma pl_getD (P Q : ℤ) (g : Z3) : ∀ (n a i : ℕ), i < n → (pl P Q g (pow P Q g a) n).getD i (0, 0, 0) = pow P Q g (a + i)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, a, 0, _ => by simp [pl]
  | n + 1, a, i + 1, h => by
    simp only [pl, List.getD_cons_succ]
    rw [show mul P Q (pow P Q g a) g = pow P Q g (a + 1) from rfl, pl_getD P Q g n (a + 1) i (by omega)]
    congr 1; omega

lemma pl_length (P Q : ℤ) (g : Z3) : ∀ (x : Z3) (n : ℕ), (pl P Q g x n).length = n
  | _, 0 => rfl
  | x, n + 1 => by simp [pl, pl_length P Q g _ n]

lemma getD_map_corner : ∀ (l : List Z3) (j : ℕ), j < l.length →
    (l.map fun y => y.2.2).getD j 0 = (l.getD j (0, 0, 0)).2.2
  | [], _, h => absurd h (by simp)
  | _ :: _, 0, _ => rfl
  | _ :: xs, j + 1, h => by simpa using getD_map_corner xs j (by simp at h; omega)

/-- `f i xᵢ` for every entry, with the index. -/
def allIdx (f : ℕ → ℤ → Bool) : ℕ → List ℤ → Bool
  | _, [] => true
  | i, x :: xs => f i x && allIdx f (i + 1) xs

lemma allIdx_get (f : ℕ → ℤ → Bool) : ∀ (l : List ℤ) (i j : ℕ), allIdx f i l = true → j < l.length →
    f (i + j) (l.getD j 0) = true
  | [], _, _, _, h => absurd h (Nat.not_lt_zero _)
  | x :: xs, i, 0, h, _ => by simp only [allIdx, Bool.and_eq_true] at h; simpa using h.1
  | x :: xs, i, j + 1, h, hj => by
    simp only [allIdx, Bool.and_eq_true] at h
    have := allIdx_get f xs (i + 1) j h.2 (by simp at hj; omega)
    simpa [show i + 1 + j = i + (j + 1) by omega] using this

/-- `Mx(x) ≡ 1 (mod q)` entrywise. -/
def oneModB (P Q : ℤ) (x : Z3) (q : ℕ) : Bool :=
  (List.finRange 3).all (fun i => (List.finRange 3).all fun j =>
    decide ((q : ℤ) ∣ Mx P Q x i j - (1 : Matrix (Fin 3) (Fin 3) ℤ) i j))

/-- The per-class tests of `corner_zeros2` for `g` with inverse `h`, period `M` at `p`, and
auxiliary primes `aux = [(q, M_q)]`; `K` bounds the precomputed powers. -/
def skolemZB2 (P Q : ℤ) (g h : Z3) (p M : ℕ) (aux : List (ℕ × ℕ)) (K : ℕ) : Bool :=
  let G := pl P Q g (1, 0, 0) (K + 1)
  let H := pl P Q h (1, 0, 0) (M + 1)
  let c := fun r => (G.getD r (0, 0, 0)).2.2
  let ch := fun r => (H.getD r (0, 0, 0)).2.2
  decide (0 < M) && decide (2 * M ≤ K) && oneModB P Q (G.getD M (0, 0, 0)) p &&
    aux.all (fun a => decide (0 < a.2) && decide (a.2 ≤ K) && oneModB P Q (G.getD a.2 (0, 0, 0)) a.1) &&
    (List.range M).all fun r =>
      decide (¬ (p : ℤ) ∣ c r) ||
      (decide (c r = 0) && decide (¬ (p : ℤ) ∣ (c (M + r) - c r) / p)) ||
      (decide (0 < r) && decide (ch (M - r) = 0) && decide (¬ (p : ℤ) ∣ (c r - ch (M - r)) / p)) ||
      aux.any fun a => allIdx (fun s x => decide (a.2 ≤ s) || decide (s % Nat.gcd M a.2 ≠ r % Nat.gcd M a.2) ||
        decide (¬ (a.1 : ℤ) ∣ x)) 0 (G.map fun y => y.2.2)

lemma oneMod_of {P Q : ℤ} {g : Z3} {q n : ℕ} (h : oneModB P Q (pow P Q g n) q = true) :
    ∃ Dq : Matrix (Fin 3) (Fin 3) ℤ, Mx P Q g ^ n = 1 + q • Dq := by
  simp only [oneModB, List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] at h
  refine ⟨Matrix.of fun i j => (Mx P Q (pow P Q g n) i j - (1 : Matrix (Fin 3) (Fin 3) ℤ) i j) / q, ?_⟩
  rw [← Mx_pow]
  ext i j
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul, Int.mul_ediv_cancel' (h i j)]
  ring

/-- **The finite zero set from the kernel check**: every `N` with `(g^N)₂ = 0` is below `M`. -/
theorem zeros2_of {P Q : ℤ} {g h : Z3} (hgh : mul P Q g h = (1, 0, 0)) {p : ℕ} [Fact p.Prime] (hp3 : 3 ≤ p)
    {M K : ℕ} {aux : List (ℕ × ℕ)}
    (hB : skolemZB2 P Q g h p M aux K = true) (N : ℕ) (hN : (pow P Q g N).2.2 = 0) : N < M := by
  simp only [skolemZB2, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, List.any_eq_true] at hB
  obtain ⟨⟨⟨⟨hM, hMK⟩, hone⟩, hauxB⟩, hr⟩ := hB
  have hp0 : 0 < p := by omega
  have hG : ∀ i, i < K + 1 → (pl P Q g (1, 0, 0) (K + 1)).getD i (0, 0, 0) = pow P Q g i := fun i hi => by
    simpa using pl_getD P Q g (K + 1) 0 i hi
  have hH : ∀ i, i < M + 1 → (pl P Q h (1, 0, 0) (M + 1)).getD i (0, 0, 0) = pow P Q h i := fun i hi => by
    simpa using pl_getD P Q h (M + 1) 0 i hi
  have hc : ∀ i, (Mx P Q g ^ i) 2 0 = (pow P Q g i).2.2 := fun i => by rw [← Mx_pow, (Mx_col P Q _).2.2]
  have hch : ∀ i, (Mx P Q h ^ i) 2 0 = (pow P Q h i).2.2 := fun i => by rw [← Mx_pow, (Mx_col P Q _).2.2]
  rw [hG M (by omega)] at hone
  obtain ⟨D, hA⟩ := oneMod_of hone
  have hAB : Mx P Q g * Mx P Q h = 1 := by rw [← Mx_mul, hgh, Mx_one]
  have hpD : ∀ r, (p : ℤ) * (D * Mx P Q g ^ r) 2 0 = (pow P Q g (M + r)).2.2 - (pow P Q g r).2.2 := by
    intro r
    have e : (p • D) * Mx P Q g ^ r = Mx P Q g ^ (M + r) - Mx P Q g ^ r := by
      rw [pow_add, hA, add_mul, one_mul]; abel
    have e2 := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℤ => A 2 0) e
    simp only at e2
    rw [smul_mul_assoc, Matrix.smul_apply, nsmul_eq_mul, Matrix.sub_apply, hc, hc] at e2
    exact e2
  have hpDh : ∀ r, r ≤ M → (p : ℤ) * (D * Mx P Q h ^ (M - r)) 2 0 = (pow P Q g r).2.2 - (pow P Q h (M - r)).2.2 := by
    intro r hr
    have e : (p • D) * Mx P Q h ^ (M - r) = Mx P Q g ^ r - Mx P Q h ^ (M - r) := by
      have : Mx P Q g ^ M * Mx P Q h ^ (M - r) = Mx P Q g ^ r := by
        rw [show M = r + (M - r) by omega, pow_add, Matrix.mul_assoc, show r + (M - r) - r = M - r by omega,
          SkolemZeros.pow_mul_pow_inv hAB, Matrix.mul_one]
      rw [← this, hA, add_mul, one_mul]; abel
    have e2 := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℤ => A 2 0) e
    simp only at e2
    rw [smul_mul_assoc, Matrix.smul_apply, nsmul_eq_mul, Matrix.sub_apply, hc, hch] at e2
    exact e2
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp0.ne'
  refine SkolemZeros.corner_zeros2 hp3 hM hAB hA (fun r hrM => ?_) N (by rw [hc]; exact hN)
  rw [hc r, hch (M - r)]
  rcases hr r hrM with ((h1 | ⟨h0, h1⟩) | ⟨⟨hr0, h0⟩, h1⟩) | ⟨a, ha, hall⟩
  · left; rwa [hG r (by omega)] at h1
  · right; left
    rw [hG r (by omega)] at h0 h1
    rw [hG (M + r) (by omega)] at h1
    refine ⟨h0, ?_⟩
    rwa [← hpD r, Int.mul_ediv_cancel_left _ hpz] at h1
  · right; right; left
    rw [hH (M - r) (by omega)] at h0 h1
    rw [hG r (by omega)] at h1
    refine ⟨hr0, h0, ?_⟩
    rwa [← hpDh r hrM.le, Int.mul_ediv_cancel_left _ hpz] at h1
  · right; right; right
    have ha' := hauxB a ha
    obtain ⟨⟨hMq, hMqK⟩, hq1⟩ := ha'
    rw [hG a.2 (by omega)] at hq1
    obtain ⟨Dq, hAq⟩ := oneMod_of hq1
    refine ⟨a.1, a.2, Dq, hMq, hAq, fun s hs hsr => ?_⟩
    have hlen := pl_length P Q g (1, 0, 0) (K + 1)
    have := allIdx_get _ _ 0 s hall (by simp only [List.length_map, hlen]; omega)
    simp only [zero_add, Bool.or_eq_true, decide_eq_true_eq] at this
    rw [getD_map_corner _ _ (by rw [hlen]; omega), hG s (by omega)] at this
    rw [hc]
    rcases this with (h1 | h1) | h1
    · omega
    · exact absurd hsr h1
    · exact h1

/-- The candidate solutions: `±` the first two coordinates of `η^N` (`N < M`) and `ε^N` (`N < M'`),
as `(u, v)` with `u − vz = ±g`. -/
def cands (P Q : ℤ) (η ε : Z3) (M M' : ℕ) : List (ℤ × ℤ) :=
  ((List.range M).map (pow P Q η) ++ (List.range M').map (pow P Q ε)).flatMap
    fun g => [(g.1, -g.2.1), (-g.1, g.2.1)]

/-- **Every solution is a candidate**, given bounds on the zeros of the `z²` coordinate. -/
theorem source_sub {P Q : ℤ} {η ε : Z3} (h1 : mul P Q η ε = (1, 0, 0)) (h2 : mul P Q ε η = (1, 0, 0))
    (hnη : nrm P Q η = 1) (hnε : nrm P Q ε = 1) {c : Cert} (hc : condB P Q η c = true)
    (hbox : slabB P Q η c = true) {M M' : ℕ}
    (hzη : ∀ N, (pow P Q η N).2.2 = 0 → N < M) (hzε : ∀ N, (pow P Q ε N).2.2 = 0 → N < M') (u v : ℤ)
    (h : -u ^ 3 + P * u * v ^ 2 + Q * v ^ 3 = 1) : (u, v) ∈ cands P Q η ε M M' := by
  have hn : nrm P Q (u, -v, 0) = -1 := by simp only [nrm]; linear_combination -h
  obtain ⟨n, hMx⟩ := units_eq h1 h2 hnη hnε hc hbox (u, -v, 0) (Or.inr hn)
  rw [← Mx_zp P Q η ε h1 h2] at hMx
  set g := zp P Q η ε n with hg
  have hcol := Mx_col P Q (u, -v, 0)
  have hgc := Mx_col P Q g
  simp only at hcol
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
    · exact List.mem_append_left _ (List.mem_map.mpr ⟨n.toNat, List.mem_range.mpr (hzη _ hz), rfl⟩)
    · exact List.mem_append_right _ (List.mem_map.mpr ⟨(-n).toNat, List.mem_range.mpr (hzε _ hz), rfl⟩)
  refine List.mem_flatMap.mpr ⟨g, hmem, ?_⟩
  rcases key with ⟨hu, hv, _⟩ | ⟨hu, hv, _⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]; left; exact ⟨hu, by linarith⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]; right; exact ⟨hu, by linarith⟩

/-- The zero bound from `skolemZB`. -/
theorem zeros1_of {P Q : ℤ} {g : Z3} {p : ℕ} [Fact p.Prime] (hp3 : 3 ≤ p) {M : ℕ}
    (hB : skolemZB P Q g p M = true) (N : ℕ) (hN : (pow P Q g N).2.2 = 0) : N < M := by
  obtain ⟨D, hM, hA, hcls⟩ := zeros_of (by omega) hB
  exact SkolemZeros.corner_zeros hp3 hM hA hcls N (by rw [← Mx_pow, (Mx_col P Q _).2.2]; exact hN)

/-- `F(u, v) = −u³ + P u v² + Q v³`. -/
def F (P Q : ℤ) (x : ℤ × ℤ) : ℤ := -x.1 ^ 3 + P * x.1 * x.2 ^ 2 + Q * x.2 ^ 3

/-- The kernel filter: the candidates that solve the equation are exactly `L`. -/
def listB (P Q : ℤ) (η ε : Z3) (M M' : ℕ) (L : List (ℤ × ℤ)) : Bool :=
  (cands P Q η ε M M').all (fun x => decide (F P Q x = 1) == decide (x ∈ L)) && L.all (fun x => decide (F P Q x = 1))

/-- **The source theorem with a finite solution list.** -/
theorem source_list {P Q : ℤ} {η ε : Z3} (h1 : mul P Q η ε = (1, 0, 0)) (h2 : mul P Q ε η = (1, 0, 0))
    (hnη : nrm P Q η = 1) (hnε : nrm P Q ε = 1) {c : Cert} (hc : condB P Q η c = true)
    (hbox : slabB P Q η c = true) {M M' : ℕ}
    (hzη : ∀ N, (pow P Q η N).2.2 = 0 → N < M) (hzε : ∀ N, (pow P Q ε N).2.2 = 0 → N < M')
    {L : List (ℤ × ℤ)} (hL : listB P Q η ε M M' L = true) (u v : ℤ) :
    -u ^ 3 + P * u * v ^ 2 + Q * v ^ 3 = 1 ↔ (u, v) ∈ L := by
  simp only [listB, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at hL
  obtain ⟨hc1, hc2⟩ := hL
  constructor
  · intro h
    have hm := source_sub h1 h2 hnη hnε hc hbox hzη hzε u v h
    have := hc1 _ hm
    simp only [F, h, decide_true] at this
    exact of_decide_eq_true this.symm
  · intro h
    have := hc2 _ h
    simpa [F] using this
