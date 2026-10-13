import Std

/-! Finite arithmetic oscillator semantics. All proofs are checked by Lean's
kernel; no native_decide, axioms, or analytic hypotheses are introduced. -/
namespace PerfectPower.ArithmeticHeightPauli

abbrev Profile (r : Nat) := Fin r → Nat

def CoordinateStep {r : Nat} (x y : Profile r) : Prop :=
  ∃ j, (x j + 1 = y j ∨ y j + 1 = x j) ∧ ∀ i, i ≠ j → x i = y i

inductive Walk {r : Nat} : Nat → Profile r → Profile r → Prop where
  | nil (x) : Walk 0 x x
  | cons {k x y z} : CoordinateStep x y → Walk k y z → Walk (k+1) x z

theorem step_coordinate_bound {r : Nat} {x y : Profile r}
    (h : CoordinateStep x y) (i : Fin r) : x i ≤ y i+1 ∧ y i ≤ x i+1 := by
  obtain ⟨j, hj, hrest⟩ := h
  by_cases hij : i = j
  · subst i; rcases hj with hj | hj <;> omega
  · have he := hrest i hij; omega

theorem walk_coordinate_bound {r k : Nat} {x y : Profile r}
    (h : Walk k x y) (i : Fin r) : x i ≤ y i+k ∧ y i ≤ x i+k := by
  induction h with
  | nil => omega
  | cons hs hw ih =>
    have hb := step_coordinate_bound hs i
    omega

def scale {r : Nat} (d : Nat) (x : Profile r) : Profile r := fun i => d*x i

theorem short_graded_walk_eq {r d k : Nat} {x y : Profile r}
    (hk : k < d) (hw : Walk k (scale d x) (scale d y)) : x = y := by
  funext i
  have hb := walk_coordinate_bound hw i
  simp only [scale] at hb
  by_cases heq : x i = y i
  · exact heq
  · have hcases : x i < y i ∨ y i < x i := by omega
    rcases hcases with hxy | hyx
    · have hm := Nat.mul_le_mul_left d (show x i+1 ≤ y i by omega)
      rw [Nat.mul_add, Nat.mul_one] at hm
      omega
    · have hm := Nat.mul_le_mul_left d (show y i+1 ≤ x i by omega)
      rw [Nat.mul_add, Nat.mul_one] at hm
      omega

theorem distinct_graded_walk_lower_bound {r d k : Nat} {x y : Profile r}
    (hne : x ≠ y) (hw : Walk k (scale d x) (scale d y)) : d ≤ k := by
  by_cases hk : k < d
  · exact False.elim (hne (short_graded_walk_eq hk hw))
  · omega

theorem scale_compose {r : Nat} (d e : Nat) (x : Profile r) :
    scale e (scale d x) = scale (e*d) x := by
  funext i; simp [scale, Nat.mul_assoc]

theorem saturated_walk_other_coordinates {r k : Nat} {x y : Profile r}
    (hw : Walk k x y) (i : Fin r) (hi : y i = x i+k) :
    ∀ j, j ≠ i → y j = x j := by
  induction hw with
  | nil => intro j hj; rfl
  | @cons k x z y hs hw ih =>
    have hb := step_coordinate_bound hs i
    have hc := walk_coordinate_bound hw i
    have hzi : z i=x i+1 := by omega
    have hyi : y i=z i+k := by omega
    obtain ⟨a,ha,hrest⟩ := hs
    have hai : a=i := by
      by_cases he : a=i
      · exact he
      · have hh := hrest i (fun h => he h.symm); omega
    subst a
    intro j hj
    have hzj := hrest j hj
    have hyj := ih hyi j hj
    omega

theorem d_step_graded_up {r d : Nat} {x y : Profile r}
    (hd : 0<d) (hw : Walk d (scale d x) (scale d y))
    (i : Fin r) (hi : x i<y i) :
    y i=x i+1 ∧ ∀ j, j ≠ i → y j=x j := by
  have hb := walk_coordinate_bound hw i
  simp only [scale] at hb
  have root : y i=x i+1 := by
    by_cases he : y i=x i+1
    · exact he
    · have hm := Nat.mul_le_mul_left d (show x i+2 ≤ y i by omega)
      rw [Nat.mul_add] at hm
      have ht : d*2=d+d := by omega
      rw [ht] at hm
      omega
  refine ⟨root, ?_⟩
  have hi' : scale d y i=scale d x i+d := by simp [scale,root,Nat.mul_add]
  have rest := saturated_walk_other_coordinates hw i hi'
  intro j hj
  exact Nat.eq_of_mul_eq_mul_left hd (rest j hj)

def raiseAt {r : Nat} (x : Profile r) (i : Fin r) (k : Nat) : Profile r :=
  fun j => if j=i then x j+k else x j

theorem raise_step {r : Nat} (x : Profile r) (i : Fin r) (k : Nat) :
    CoordinateStep (raiseAt x i k) (raiseAt x i (k+1)) := by
  refine ⟨i, Or.inl ?_, ?_⟩
  · simp [raiseAt,Nat.add_assoc]
  · intro j hj; simp [raiseAt,hj]

theorem walk_append {r k l : Nat} {x y z : Profile r}
    (h : Walk k x y) (g : Walk l y z) : Walk (k+l) x z := by
  induction h with
  | nil => simpa using g
  | cons hs hw ih =>
    have hh := Walk.cons hs (ih g)
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

theorem raise_walk {r : Nat} (x : Profile r) (i : Fin r) (k : Nat) :
    Walk k x (raiseAt x i k) := by
  induction k with
  | zero =>
    have he : raiseAt x i 0=x := by funext j; simp [raiseAt]
    rw [he]; exact Walk.nil x
  | succ k ih =>
    exact walk_append ih (Walk.cons (raise_step x i k) (Walk.nil _))

theorem scale_raise {r : Nat} (d : Nat) (x : Profile r) (i : Fin r) :
    scale d (raiseAt x i 1)=raiseAt (scale d x) i d := by
  funext j; by_cases hj : j=i <;> simp [scale,raiseAt,hj,Nat.mul_add]

theorem root_edge_lifts {r : Nat} (d : Nat) (x : Profile r) (i : Fin r) :
    Walk d (scale d x) (scale d (raiseAt x i 1)) := by
  rw [scale_raise]; exact raise_walk _ _ _

inductive Good (p q : Nat) : Nat → Nat → List Bool → Prop where
  | nil : Good p q 0 0 []
  | up {u v xs} : Good p q u v xs → p^(u+1) ≤ q^v →
      Good p q (u+1) v (true::xs)
  | down {u v xs} : Good p q u v xs → p^u ≤ q^(v+1) →
      Good p q u (v+1) (false::xs)

def words (p q : Nat) : Nat → Nat → List (List Bool)
  | 0, 0 => [[]]
  | u+1, 0 => if p^(u+1) ≤ q^0 then (words p q u 0).map (true::·) else []
  | 0, v+1 => if p^0 ≤ q^(v+1) then (words p q 0 v).map (false::·) else []
  | u+1, v+1 => if p^(u+1) ≤ q^(v+1) then
      (words p q u (v+1)).map (true::·) ++
      (words p q (u+1) v).map (false::·) else []
termination_by u v => u+v
decreasing_by all_goals omega

def ballot (p q : Nat) : Nat → Nat → Nat
  | 0, 0 => 1
  | u+1, 0 => if p^(u+1) ≤ q^0 then ballot p q u 0 else 0
  | 0, v+1 => if p^0 ≤ q^(v+1) then ballot p q 0 v else 0
  | u+1, v+1 => if p^(u+1) ≤ q^(v+1) then
      ballot p q u (v+1) + ballot p q (u+1) v else 0
termination_by u v => u+v
decreasing_by all_goals omega

theorem words_length (p q u v : Nat) : (words p q u v).length = ballot p q u v := by
  induction u generalizing v with
  | zero =>
    induction v with
    | zero => simp [words, ballot]
    | succ v ih =>
      simp only [words, ballot]
      split <;> simp_all
  | succ u ih =>
    induction v with
    | zero =>
      simp only [words, ballot]
      split <;> simp_all
    | succ v ihv =>
      simp only [words, ballot]
      split <;> simp_all

theorem good_length {p q u v : Nat} {xs : List Bool} (h : Good p q u v xs) :
    xs.length = u+v := by
  induction h with
  | nil => rfl
  | up h hp ih => simp only [List.length_cons]; omega
  | down h hp ih => simp only [List.length_cons]; omega

theorem good_endpoint_height {p q u v : Nat} {xs : List Bool}
    (h : Good p q u v xs) : p^u ≤ q^v := by
  cases h with
  | nil => simp
  | up h hp => exact hp
  | down h hp => exact hp

theorem good_true_count {p q u v : Nat} {xs : List Bool} (h : Good p q u v xs) :
    xs.count true = u := by
  induction h with
  | nil => rfl
  | up h hp ih => simp [ih]
  | down h hp ih => simp [ih]

theorem good_false_count {p q u v : Nat} {xs : List Bool} (h : Good p q u v xs) :
    xs.count false = v := by
  induction h with
  | nil => rfl
  | up h hp ih => simp [ih]
  | down h hp ih => simp [ih]

theorem good_mem_words {p q u v : Nat} {xs : List Bool}
    (h : Good p q u v xs) : xs ∈ words p q u v := by
  induction h with
  | nil => simp [words]
  | @up u v xs hg hp ih =>
    cases v with
    | zero =>
      rw [words, if_pos hp]
      exact List.mem_map.mpr ⟨xs, ih, rfl⟩
    | succ v =>
      rw [words, if_pos hp]
      exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨xs, ih, rfl⟩))
  | @down u v xs hg hp ih =>
    cases u with
    | zero =>
      rw [words, if_pos hp]
      exact List.mem_map.mpr ⟨xs, ih, rfl⟩
    | succ u =>
      rw [words, if_pos hp]
      exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨xs, ih, rfl⟩))

theorem mem_words_good (p q u v : Nat) (xs : List Bool)
    (h : xs ∈ words p q u v) : Good p q u v xs := by
  induction u generalizing v xs with
  | zero =>
    induction v generalizing xs with
    | zero =>
      simp only [words, List.mem_cons, List.not_mem_nil, or_false] at h
      subst xs; exact Good.nil
    | succ v ih =>
      rw [words] at h
      split at h
      · rename_i hp
        obtain ⟨ys, hy, he⟩ := List.mem_map.mp h
        subst xs; exact Good.down (ih ys hy) hp
      · simp at h
  | succ u ih =>
    induction v generalizing xs with
    | zero =>
      rw [words] at h
      split at h
      · rename_i hp
        obtain ⟨ys, hy, he⟩ := List.mem_map.mp h
        subst xs; exact Good.up (ih 0 ys hy) hp
      · simp at h
    | succ v ihv =>
      rw [words] at h
      split at h
      · rename_i hp
        rcases List.mem_append.mp h with h | h
        · obtain ⟨ys, hy, he⟩ := List.mem_map.mp h
          subst xs; exact Good.up (ih (v+1) ys hy) hp
        · obtain ⟨ys, hy, he⟩ := List.mem_map.mp h
          subst xs; exact Good.down (ihv ys hy) hp
      · simp at h

theorem enumeration_complete (p q u v : Nat) (xs : List Bool) :
    xs ∈ words p q u v ↔ Good p q u v xs :=
  ⟨mem_words_good p q u v xs, good_mem_words⟩

theorem cons_map_nodup (b : Bool) (xs : List (List Bool))
    (h : xs.Nodup) : (xs.map (b::·)).Nodup := by
  exact List.Pairwise.map _ (fun a c hn he => hn (List.cons.inj he).2) h

theorem cons_maps_disjoint (xs ys : List (List Bool))
    (x : List Bool) (hx : x ∈ xs.map (true::·))
    (y : List Bool) (hy : y ∈ ys.map (false::·)) : x ≠ y := by
  obtain ⟨a,ha,he⟩ := List.mem_map.mp hx
  obtain ⟨b,hb,hf⟩ := List.mem_map.mp hy
  subst x; subst y; intro h; cases (List.cons.inj h).1

theorem words_nodup (p q u v : Nat) : (words p q u v).Nodup := by
  induction u generalizing v with
  | zero =>
    induction v with
    | zero => simp [words]
    | succ v ih =>
      rw [words]; split
      · exact cons_map_nodup false _ ih
      · simp
  | succ u ih =>
    induction v with
    | zero =>
      rw [words]; split
      · exact cons_map_nodup true _ (ih 0)
      · simp
    | succ v ihv =>
      rw [words]; split
      · exact List.pairwise_append.mpr
          ⟨cons_map_nodup true _ (ih (v+1)), cons_map_nodup false _ ihv,
           cons_maps_disjoint _ _⟩
      · simp

theorem complete_distinct_population (p q u v : Nat) :
    (words p q u v).Nodup ∧ (words p q u v).length = ballot p q u v ∧
    ∀ xs, xs ∈ words p q u v ↔ Good p q u v xs :=
  ⟨words_nodup p q u v, words_length p q u v, enumeration_complete p q u v⟩

theorem forbidden_endpoint_zero (p q u v : Nat) (h : ¬ p^u ≤ q^v) :
    ballot p q u v = 0 := by
  cases u with
  | zero =>
    cases v with
    | zero => exact False.elim (h (by simp))
    | succ v => rw [ballot, if_neg h]
  | succ u =>
    cases v with
    | zero => rw [ballot, if_neg h]
    | succ v => rw [ballot, if_neg h]

theorem height_barrier_equivalence (p q d u v : Nat) (hq : 0<q) (hv : v≤d) :
    p^u*q^(d-v) ≤ q^d ↔ p^u ≤ q^v := by
  have he : q^d=q^v*q^(d-v) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [he]
  exact ⟨fun h => Nat.le_of_mul_le_mul_right h (Nat.pow_pos hq),
    fun h => Nat.mul_le_mul_right _ h⟩

def shiftedTransition (p d n k : Nat) : Nat := p^d*(n+k)-k

theorem shifted_power_preserved (p d n k a : Nat)
    (h : n+k=a^d) (hdom : k≤p^d*(n+k)) :
    shiftedTransition p d n k+k=(p*a)^d := by
  rw [shiftedTransition,Nat.sub_add_cancel hdom,h,Nat.mul_pow]

theorem prime_chain_power_injective {p a b : Nat} (hp : 1 < p)
    (h : p^a = p^b) : a = b := by
  by_cases he : a=b
  · exact he
  · have hc : a<b ∨ b<a := by omega
    rcases hc with hc | hc
    · have hh := Nat.pow_lt_pow_right hp hc; omega
    · have hh := Nat.pow_lt_pow_right hp hc; omega

-- Gaussian-integer entries retain the exact real/imaginary Pauli block shape.
structure Gaussian where
  re : Int
  im : Int
deriving DecidableEq, Repr

def conjugate (z : Gaussian) : Gaussian := ⟨z.re,-z.im⟩
def negate (z : Gaussian) : Gaussian := ⟨-z.re,-z.im⟩
abbrev SpinMatrix (ι : Type) := Bool → Bool → ι → ι → Gaussian

def pauli {ι : Type} (C H R : ι → ι → Int) : SpinMatrix ι
  | false, false, i, j => ⟨R i j,0⟩
  | false, true, i, j => ⟨C i j,-H i j⟩
  | true, false, i, j => ⟨C i j,H i j⟩
  | true, true, i, j => ⟨-R i j,0⟩

def chargeConjugate {ι : Type} (M : SpinMatrix ι) : SpinMatrix ι :=
  fun s t i j => if s=t then conjugate (M (!s) (!t) i j)
    else negate (conjugate (M (!s) (!t) i j))

theorem pauli_charge_symmetry {ι : Type} (C H R : ι → ι → Int) :
    chargeConjugate (pauli C H R) = fun s t i j => negate (pauli C H R s t i j) := by
  funext s t i j
  cases s <;> cases t <;> simp [chargeConjugate, pauli, conjugate, negate]

theorem conjugate_involution (z : Gaussian) : conjugate (conjugate z) = z := by
  cases z; simp [conjugate]

theorem negate_involution (z : Gaussian) : negate (negate z) = z := by
  cases z; simp [negate]

def stateCharge {ι : Type} (ψ : Bool → ι → Gaussian) : Bool → ι → Gaussian
  | false, i => ⟨-(ψ true i).im,-(ψ true i).re⟩
  | true, i => ⟨(ψ false i).im,(ψ false i).re⟩

theorem state_charge_square {ι : Type} (ψ : Bool → ι → Gaussian) :
    stateCharge (stateCharge ψ)=fun s i => negate (ψ s i) := by
  funext s i; cases s <;> simp [stateCharge,negate]

end PerfectPower.ArithmeticHeightPauli
