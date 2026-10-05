import PerfectPower.ArithmeticSimplifier
import PerfectPower.PolynomialCapacity
import Mathlib.Data.Int.Interval

namespace PerfectPower.SemilinearCapacity

/-- Every integer in a residue class has a unique lattice coordinate. -/
theorem residue_coordinate (m r n : ℤ) (_hm : 0 < m) (hr : 0 ≤ r) (hrm : r < m) :
    n % m = r ↔ ∃ k : ℤ, n = r + m * k := by
  constructor
  · intro h
    exact ⟨n / m, by simpa [h] using (Int.emod_add_ediv n m).symm⟩
  · rintro ⟨k, rfl⟩
    rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt hr hrm]

/-- The exact floor-quotient bounds include negative endpoints. -/
theorem lattice_bounds (lo hi m r k : ℤ) (hm : 0 < m) :
    lo ≤ r + m * k ∧ r + m * k ≤ hi ↔
      (lo - 1 - r) / m + 1 ≤ k ∧ k ≤ (hi - r) / m := by
  rw [show (lo - 1 - r) / m + 1 ≤ k ↔ (lo - 1 - r) / m < k by omega,
      Int.ediv_lt_iff_lt_mul hm, Int.le_ediv_iff_mul_le hm]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> nlinarith

/-- A kernel-checkable residue-cell transcript is an exact interval image. -/
theorem residue_interval_image (lo hi m r : ℤ) (hm : 0 < m)
    (hr : 0 ≤ r) (hrm : r < m) :
    (Finset.Icc lo hi).filter (fun n => n % m = r) =
    (Finset.Icc ((lo - 1 - r) / m + 1) ((hi - r) / m)).image (fun k => r + m * k) := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ⟨⟨hlo,hhi⟩, hn⟩
    obtain ⟨k, rfl⟩ := (residue_coordinate m r n hm hr hrm).mp hn
    exact ⟨k, (lattice_bounds lo hi m r k hm).mp ⟨hlo,hhi⟩, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨(lattice_bounds lo hi m r k hm).mpr hk,
      (residue_coordinate m r _ hm hr hrm).mpr ⟨k,rfl⟩⟩

/-- The floor difference counts the residue cell without scanning its interval. -/
theorem residue_interval_count (lo hi m r : ℤ) (hm : 0 < m)
    (hr : 0 ≤ r) (hrm : r < m) :
    ((Finset.Icc lo hi).filter (fun n => n % m = r)).card =
      ((hi - r) / m - (lo - 1 - r) / m).toNat := by
  rw [residue_interval_image lo hi m r hm hr hrm,
      Finset.card_image_of_injective]
  · rw [Int.card_Icc]
    congr 1
    ring
  · intro a b h
    exact mul_left_cancel₀ (ne_of_gt hm) (add_left_cancel h)

/-- Disjoint residues add exactly; no multiplicity is lost or introduced. -/
theorem residue_set_count (lo hi m : ℤ) (R : Finset ℤ) (hm : 0 < m)
    (hr : ∀ r ∈ R, 0 ≤ r ∧ r < m) :
    ((Finset.Icc lo hi).filter (fun n => n % m ∈ R)).card =
      ∑ r ∈ R, ((hi - r) / m - (lo - 1 - r) / m).toNat := by
  have he : (Finset.Icc lo hi).filter (fun n => n % m ∈ R) =
      R.biUnion (fun r => (Finset.Icc lo hi).filter (fun n => n % m = r)) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_biUnion]
    constructor
    · rintro ⟨hn,hr⟩; exact ⟨n % m,hr,hn,rfl⟩
    · rintro ⟨r,hr,hn,he⟩; exact ⟨hn, he ▸ hr⟩
  rw [he, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro r hr'
    exact residue_interval_count lo hi m r hm (hr r hr').1 (hr r hr').2
  · intro r hr' s hs' hrs
    apply Finset.disjoint_left.mpr
    intro n hn hns
    simp only [Finset.mem_filter] at hn hns
    exact hrs (hn.2.symm.trans hns.2)

/-- Accepted coordinates increase prefix counts by exactly one. -/
theorem accepted_rank (S : Finset ℤ) (n : ℤ) (hn : n ∈ S) :
    (S.filter (fun x => x ≤ n)).card = (S.filter (fun x => x < n)).card + 1 := by
  have he : S.filter (fun x => x ≤ n) = insert n (S.filter (fun x => x < n)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hx,hxn⟩
      rcases lt_or_eq_of_le hxn with h | h
      · exact Or.inr ⟨hx,h⟩
      · exact Or.inl h
    · rintro (rfl | ⟨hx,hxn⟩)
      · exact ⟨hn,le_rfl⟩
      · exact ⟨hx,hxn.le⟩
  rw [he, Finset.card_insert_of_notMem]
  simp

/-- The original affine integer image, including negative slopes. -/
theorem affine_image (a b u : ℤ) :
    (∃ x : ℤ, a * x + b = u) ↔ a ∣ u - b := by
  constructor
  · rintro ⟨x,h⟩
    exact ⟨x, by omega⟩
  · rintro ⟨x,h⟩
    exact ⟨x, by omega⟩

/-- Affine chart inversion keeps both divisibility and the exact integer value. -/
theorem affine_fibre (a b u x : ℤ) (ha : a ≠ 0) :
    a * x + b = u ↔ a ∣ u - b ∧ x = (u - b) / a := by
  constructor
  · intro h
    have he : u - b = a * x := by omega
    refine ⟨⟨x,he⟩, ?_⟩
    rw [he, Int.mul_ediv_cancel_left x ha]
  · rintro ⟨hd,rfl⟩
    have he := Int.ediv_mul_cancel hd
    nlinarith

/-- A period-sized step preserves the residue predicate. -/
theorem step_residue (m n : ℤ) : (n + m) % m = n % m := by
  simp [Int.add_emod]

/-- Period-step descent respects all residue classes in a cell. -/
theorem period_descent (f : ℤ → ℤ) (m x : ℤ) (S : ℤ → Prop)
    (hnext : S (x + m)) (hd : f (x + m) - f x < 0) :
    ∃ y, S y ∧ y % m = x % m ∧ f y < f x := by
  exact ⟨x + m, hnext, step_residue m x, by omega⟩

/-- Interpreting an independently checked finite family of nonlinear fibres. -/
theorem fibre_product (A B : ℤ → ℤ) (u v x y : ℤ) (X Y : Finset ℤ)
    (hx : ∀ z, A z = u ↔ z ∈ X) (hy : ∀ z, B z = v ↔ z ∈ Y) :
    A x = u ∧ B y = v ↔ (x,y) ∈ X ×ˢ Y := by
  simp only [Finset.mem_product, hx, hy]

/-- Integer polynomial evaluation in ascending Horner coefficients. -/
def horner : List ℤ → ℤ → ℤ
  | [], _ => 0
  | c :: cs, x => c + x * horner cs x

/-- Every integer polynomial preserves congruence. -/
theorem horner_residue (cs : List ℤ) (m x y : ℤ) (h : x % m = y % m) :
    horner cs x % m = horner cs y % m := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      simp only [horner]
      rw [Int.add_emod c (x * horner cs x) m,
        Int.add_emod c (y * horner cs y) m,
        Int.mul_emod x (horner cs x) m,
        Int.mul_emod y (horner cs y) m, h, ih]

/-- An exact modular truth table repeats at every multiple of its modulus. -/
theorem horner_period (cs : List ℤ) (m M x : ℤ) (hM : m ∣ M) :
    horner cs (x + M) % m = horner cs x % m := by
  apply horner_residue
  rw [Int.add_emod, Int.emod_eq_zero_of_dvd hM]
  simp

/-- Infinite-domain descent is sound when a (possibly loose) integer lower bound
has been certified. This avoids assuming a finite feasible interval. -/
theorem global_candidate_bound (f : ℤ → ℤ) (S C : ℤ → Prop) (L m : ℤ)
    (bounded : ∀ x, S x → L ≤ f x)
    (descent : ∀ x, S x → ¬ C x → ∃ y, S y ∧ f y < f x)
    (checked : ∀ x, S x → C x → m ≤ f x) : ∀ x, S x → m ≤ f x := by
  have aux : ∀ n : ℕ, ∀ x, S x → (f x - L).toNat = n → m ≤ f x := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hx hn
      by_cases hc : C x
      · exact checked x hx hc
      obtain ⟨y,hy,hlt⟩ := descent x hx hc
      have hbx := bounded x hx
      have hby := bounded y hy
      have hmeasure : (f y - L).toNat < n := by omega
      have hlo := ih (f y - L).toNat hmeasure y hy rfl
      omega
  intro x hx
  exact aux (f x - L).toNat x hx rfl

/-- Complete optimizer interpretation over bounded-below infinite domains. -/
theorem global_optimizer_iff (f : ℤ → ℤ) (S C : ℤ → Prop) (L m x : ℤ)
    (bounded : ∀ x, S x → L ≤ f x)
    (descent : ∀ x, S x → ¬ C x → ∃ y, S y ∧ f y < f x)
    (checked : ∀ x, S x → C x → m ≤ f x)
    (attained : ∃ y, S y ∧ f y = m) :
    (S x ∧ ∀ y, S y → f x ≤ f y) ↔ S x ∧ C x ∧ f x = m := by
  constructor
  · rintro ⟨hx,hm⟩
    obtain ⟨y,hy,he⟩ := attained
    have hlo := global_candidate_bound f S C L m bounded descent checked x hx
    have hhi := hm y hy
    exact ⟨hx, PerfectPower.PolynomialCapacity.minimizers_in_candidates
      f S C descent x hx hm, by omega⟩
  · rintro ⟨hx,_,he⟩
    refine ⟨hx, ?_⟩
    intro y hy
    rw [he]
    exact global_candidate_bound f S C L m bounded descent checked y hy

/-- Assembly directly from period-step descent witnesses, retaining every tie. -/
theorem period_optimizer_iff (f : ℤ → ℤ) (S C : ℤ → Prop) (M L m x : ℤ)
    (bounded : ∀ x, S x → L ≤ f x)
    (steps : ∀ x, S x → ¬ C x →
      (S (x - M) ∧ f (x - M) < f x) ∨ (S (x + M) ∧ f (x + M) < f x))
    (checked : ∀ x, S x → C x → m ≤ f x)
    (attained : ∃ y, S y ∧ f y = m) :
    (S x ∧ ∀ y, S y → f x ≤ f y) ↔ S x ∧ C x ∧ f x = m := by
  apply global_optimizer_iff f S C L m x bounded _ checked attained
  intro z hz hc
  rcases steps z hz hc with ⟨hy,hl⟩ | ⟨hy,hl⟩
  · exact ⟨z - M,hy,hl⟩
  · exact ⟨z + M,hy,hl⟩

/-- Native proof production for a literal single-residue interval count. -/
macro "native_residue_count" : tactic =>
  `(tactic| (rw [PerfectPower.SemilinearCapacity.residue_interval_count _ _ _ _
    (by norm_num) (by norm_num) (by norm_num)]; norm_num [Int.toNat]))

end PerfectPower.SemilinearCapacity
