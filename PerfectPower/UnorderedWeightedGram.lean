import PerfectPower.CauchyBinet
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Pi

noncomputable section
namespace PerfectPower.UnorderedWeightedGram
open scoped BigOperators Classical
open Equiv
variable {e : Type*} [Fintype e] [LinearOrder e] {n : ℕ}

abbrev Basis (e : Type*) [Fintype e] (n : ℕ) := {s : Finset e // s.card = n}

def canonical (s : Basis e n) : Fin n ↪ e := (s.1.orderEmbOfFin s.2).toEmbedding

def support (p : Fin n ↪ e) : Basis e n :=
  ⟨Finset.univ.image p, by rw [Finset.card_image_of_injective _ p.injective]; simp⟩

def rangeEquiv (p : Fin n ↪ e) : Fin n ≃ (support p).1 :=
  Equiv.ofBijective (fun i => ⟨p i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩)
    ⟨by intro i j h; exact p.injective (congrArg Subtype.val h), by
      intro z
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp z.2
      exact ⟨i,Subtype.ext hi⟩⟩

def ordering (p : Fin n ↪ e) : Perm (Fin n) :=
  (rangeEquiv p).trans ((support p).1.orderIsoOfFin (support p).2).toEquiv.symm

theorem canonical_ordering (p : Fin n ↪ e) (i : Fin n) :
    canonical (support p) (ordering p i) = p i := by
  change ↑(((support p).1.orderIsoOfFin (support p).2)
    (((support p).1.orderIsoOfFin (support p).2).symm (rangeEquiv p i))) = p i
  simp [rangeEquiv]

theorem support_composed (s : Basis e n) (σ : Perm (Fin n)) :
    support (σ.toEmbedding.trans (canonical s)) = s := by
  apply Subtype.ext
  change Finset.univ.image (fun i => canonical s (σ i)) = s.1
  change Finset.image ((canonical s) ∘ σ) Finset.univ = s.1
  rw [← Finset.image_image]
  have hσ : Finset.univ.image σ = Finset.univ := by
    ext i; simp
  rw [hσ]
  exact Finset.image_orderEmbOfFin_univ s.1 s.2

def selectionEquiv : (Fin n ↪ e) ≃ Basis e n × Perm (Fin n) where
  toFun p := (support p,ordering p)
  invFun q := q.2.toEmbedding.trans (canonical q.1)
  left_inv p := by ext i; exact canonical_ordering p i
  right_inv q := by
    obtain ⟨s,σ⟩ := q
    have hs := support_composed s σ
    apply Prod.ext hs
    apply Equiv.ext
    intro i
    apply (canonical s).injective
    have h := canonical_ordering (σ.toEmbedding.trans (canonical s)) i
    simpa only [hs,Function.Embedding.trans_apply,Equiv.toEmbedding_apply] using h

variable {R : Type*} [CommRing R] [StarRing R]

def term (B : Matrix e (Fin n) R) (w : e → R) (p : Fin n → e) : R :=
  (∏ i, w (p i)) * star (Matrix.det (fun i j => B (p i) j)) *
    Matrix.det (fun i j => B (p i) j)

theorem term_permutation (B : Matrix e (Fin n) R) (w : e → R)
    (p : Fin n → e) (σ : Perm (Fin n)) :
    term B w (fun i => p (σ i)) = term B w p := by
  have hw : (∏ i, w (p (σ i))) = ∏ i, w (p i) :=
    Fintype.prod_equiv σ _ _ (by intro i; rfl)
  have hd := Matrix.det_permute σ (fun i j => B (p i) j)
  change Matrix.det (fun i j => B (p (σ i)) j) = _ at hd
  rcases Int.units_eq_one_or (Perm.sign σ) with h | h
  · simp only [h,Int.cast_one,mul_one,one_mul] at hd
    simp [term,hw,hd]
  · simp only [h,Int.cast_neg,Int.cast_one,neg_one_mul] at hd
    simp [term,hw,hd]

theorem ordered_sum_grouped (B : Matrix e (Fin n) R) (w : e → R) :
    (∑ p : Fin n → e, term B w p) =
      (n.factorial : R) * ∑ s : Basis e n, term B w (canonical s) := by
  have hfilter : (∑ p : Fin n → e, term B w p) =
      ∑ p : Fin n → e with Function.Injective p, term B w p := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p _ hp
    have hn : ¬ Function.Injective p := by simpa using hp
    have hz : Matrix.det (fun i j => B (p i) j) = 0 :=
      (Matrix.det_transpose (fun i j => B (p i) j)).symm.trans
        (PerfectPower.RectangularDeterminant.repeated_selection_zero (fun i j => B j i) p hn)
    simp [term,hz]
  rw [hfilter]
  have he : (∑ p : Fin n → e with Function.Injective p, term B w p) =
      ∑ p : Fin n ↪ e, term B w p := by
    apply Finset.sum_bij (fun p hp => (⟨p,(Finset.mem_filter.mp hp).2⟩ : Fin n ↪ e))
    · intro p hp; exact Finset.mem_univ _
    · intro p hp q hq h; exact congrArg Function.Embedding.toFun h
    · intro p _; exact ⟨p,Finset.mem_filter.mpr ⟨Finset.mem_univ _,p.injective⟩,rfl⟩
    · intro p hp; rfl
  rw [he]
  calc
    _ = ∑ q : Basis e n × Perm (Fin n), term B w (fun i => canonical q.1 (q.2 i)) := by
      apply Fintype.sum_equiv selectionEquiv
      intro p
      congr 1; funext i; exact (canonical_ordering p i).symm
    _ = (n.factorial : R) * ∑ s : Basis e n, term B w (canonical s) := by
      rw [Fintype.sum_prod_type]
      simp only [term_permutation,Finset.sum_const,Fintype.card_perm,Fintype.card_fin,nsmul_eq_mul]
      rw [← Finset.mul_sum]
      simp only [Finset.card_univ,Fintype.card_perm,Fintype.card_fin]

/-- Each size-n subset contributes once; zero weights and deficient rank are allowed. -/
theorem weighted_gram [NoZeroDivisors R] [CharZero R]
    (B : Matrix e (Fin n) R) (w : e → R) :
    (PerfectPower.CauchyBinet.gram B w).det =
      ∑ s : Basis e n, (∏ i, w (canonical s i)) *
        star (Matrix.det (fun i j => B (canonical s i) j)) *
          Matrix.det (fun i j => B (canonical s i) j) := by
  have h := PerfectPower.CauchyBinet.weighted_gram B w
  simp only [Fintype.card_fin] at h
  change (n.factorial : R) * _ = ∑ p : Fin n → e, term B w p at h
  rw [ordered_sum_grouped] at h
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)) h

/-- Real nonnegative weights give a nonnegative Gram determinant, including zero weights. -/
theorem real_nonnegative (B : Matrix e (Fin n) ℝ) (w : e → ℝ) (hw : ∀ i, 0≤w i) :
    0≤(PerfectPower.CauchyBinet.gram B w).det := by
  rw [weighted_gram]
  apply Finset.sum_nonneg
  intro s _
  rw [star_trivial]
  have hp : 0≤∏ i, w (canonical s i) := Finset.prod_nonneg (fun i _ => hw _)
  nlinarith [mul_nonneg hp (sq_nonneg (Matrix.det (fun i j => B (canonical s i) j)))]

/-- With positive weights, determinant zero is exactly failure of every maximal minor. -/
theorem real_zero_iff (B : Matrix e (Fin n) ℝ) (w : e → ℝ) (hw : ∀ i, 0<w i) :
    (PerfectPower.CauchyBinet.gram B w).det=0 ↔
      ∀ s : Basis e n, Matrix.det (fun i j => B (canonical s i) j)=0 := by
  rw [weighted_gram]
  have hn (s : Basis e n) :
      0≤(∏ i, w (canonical s i))*star (Matrix.det (fun i j => B (canonical s i) j))*
        Matrix.det (fun i j => B (canonical s i) j) := by
    rw [star_trivial]
    have hp : 0<∏ i, w (canonical s i) := Finset.prod_pos (fun i _ => hw _)
    nlinarith [mul_nonneg hp.le (sq_nonneg (Matrix.det (fun i j => B (canonical s i) j)))]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun s _ => hn s)]
  constructor
  · intro h s
    have he := h s (Finset.mem_univ s)
    rw [star_trivial] at he
    have hp : 0<∏ i, w (canonical s i) := Finset.prod_pos (fun i _ => hw _)
    have hz : (∏ i, w (canonical s i))* (Matrix.det (fun i j => B (canonical s i) j))^2=0 := by
      nlinarith [he]
    have hminor := (mul_eq_zero.mp hz).resolve_left (ne_of_gt hp)
    nlinarith [sq_nonneg (Matrix.det (fun i j => B (canonical s i) j))]
  · intro h s _
    simp [h s]

end PerfectPower.UnorderedWeightedGram
