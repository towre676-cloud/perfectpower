import PerfectPower.NativePolynomialSquare
import Mathlib

namespace PerfectPower.BernsteinRootTree
open scoped BigOperators

/-- Unnormalized Bernstein basis on the half-open interval (a,b]. -/
def form (n : ℕ) (c : Fin (n+1) → ℚ) (a b x : ℚ) : ℚ :=
  ∑ i, c i * (x-a)^i.val * (b-x)^(n-i.val)

theorem form_pos (n : ℕ) (c : Fin (n+1) → ℚ) (a b x : ℚ)
    (hc : ∀ i, 0 ≤ c i) (hlast : 0 < c (Fin.last n))
    (ha : a < x) (hb : x ≤ b) : 0 < form n c a b x := by
  unfold form
  apply Finset.sum_pos'
  · intro i hi
    exact mul_nonneg (mul_nonneg (hc i) (pow_nonneg (sub_pos.mpr ha).le _))
      (pow_nonneg (sub_nonneg.mpr hb) _)
  · refine ⟨Fin.last n, Finset.mem_univ _, ?_⟩
    simp only [Fin.val_last, Nat.sub_self, pow_zero, mul_one]
    exact mul_pos hlast (pow_pos (sub_pos.mpr ha) _)

theorem excludes (F : ℤ → ℚ) (a b : ℤ) (n : ℕ) (c : Fin (n+1) → ℚ)
    (s : ℚ) (hs : s ≠ 0) (hc : ∀ i, 0 ≤ c i) (hlast : 0 < c (Fin.last n))
    (he : ∀ x : ℤ, F x = s * form n c a b x) :
    ∀ x : ℤ, a < x → x ≤ b → F x ≠ 0 := by
  intro x ha hb hz
  have hp := form_pos n c a b x hc hlast (by exact_mod_cast ha) (by exact_mod_cast hb)
  rw [he] at hz
  exact (ne_of_gt hp) ((mul_eq_zero.mp hz).resolve_left hs)

/-- A proof-producing subdivision tree. No variation counts are trusted. -/
inductive Tree (F : ℤ → ℚ) : ℤ → ℤ → Type
  | empty (a b : ℤ) (h : b ≤ a) : Tree F a b
  | unit (a : ℤ) : Tree F a (a+1)
  | skip (a b : ℤ) (h : ∀ x, a < x → x ≤ b → F x ≠ 0) : Tree F a b
  | split (a m b : ℤ) (ham : a ≤ m) (hmb : m ≤ b)
      (left : Tree F a m) (right : Tree F m b) : Tree F a b

def Tree.roots {F : ℤ → ℚ} {a b : ℤ} : Tree F a b → Finset ℤ
  | .empty _ _ _ => ∅
  | .unit a => if F (a+1)=0 then {a+1} else ∅
  | .skip _ _ _ => ∅
  | .split _ _ _ _ _ left right => left.roots ∪ right.roots

theorem Tree.complete {F : ℤ → ℚ} {a b : ℤ} (t : Tree F a b) (x : ℤ) :
    x ∈ t.roots ↔ a < x ∧ x ≤ b ∧ F x=0 := by
  induction t with
  | empty a b h => simp only [Tree.roots,Finset.notMem_empty, false_iff]; omega
  | unit a =>
    simp only [Tree.roots]
    split_ifs with h
    · simp only [Finset.mem_singleton]; constructor
      · intro hx;subst x;exact ⟨by omega,le_rfl,h⟩
      · intro hx;omega
    · simp only [Finset.notMem_empty,false_iff];intro hx
      have he : x=a+1 := by omega
      exact h (he ▸ hx.2.2)
  | skip a b h =>
    simp only [Tree.roots,Finset.notMem_empty,false_iff]
    exact fun hx => h x hx.1 hx.2.1 hx.2.2
  | split a m b ham hmb left right ihl ihr =>
    simp only [Tree.roots,Finset.mem_union,ihl,ihr]
    constructor
    · rintro (h | h) <;> exact ⟨by omega,by omega,h.2.2⟩
    · intro h
      by_cases hm : x ≤ m
      · exact Or.inl ⟨h.1,hm,h.2.2⟩
      · exact Or.inr ⟨by omega,h.2.1,h.2.2⟩

/-- The supplied outer root bound and every discarded interval are part of the proof. -/
theorem global_complete (F : ℤ → ℚ) (B : ℤ) (hbound : ∀ x, F x=0 → |x|≤B)
    (t : Tree F (-B-1) B) (x : ℤ) : F x=0 ↔ x ∈ t.roots := by
  rw [t.complete]
  constructor
  · intro h
    have hb := abs_le.mp (hbound x h)
    exact ⟨by omega,hb.2,h⟩
  · exact fun h => h.2.2

theorem integer_complete (as : List ℤ) (hv : NativePolynomialSquare.valid as)
    (hd : 2 ≤ as.length)
    (t : Tree (fun x => (NativePolynomialSquare.eval as x : ℚ))
      (-NativePolynomialSquare.bound as 0-1) (NativePolynomialSquare.bound as 0)) (x : ℤ) :
    NativePolynomialSquare.eval as x=0 ↔ x ∈ t.roots := by
  have hb : ∀ x : ℤ, (NativePolynomialSquare.eval as x : ℚ)=0 → |x|≤NativePolynomialSquare.bound as 0 := by
    intro x hx
    have hz : NativePolynomialSquare.eval as x=0 := by exact_mod_cast hx
    apply NativePolynomialSquare.eval_bound as 0 x hv hd
    simp [hz]
  have h := global_complete _ _ hb t x
  simpa only [Int.cast_eq_zero] using h

end PerfectPower.BernsteinRootTree
