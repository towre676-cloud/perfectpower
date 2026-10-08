import PerfectPower.WeilOrbitSymmetry
import PerfectPower.MonomialOrbitSpace
import Mathlib.LinearAlgebra.Basis.Defs

noncomputable section
namespace PerfectPower.WeilMonomial
open scoped BigOperators
open Matrix PerfectPower.WeilCRT
variable {A K : Type*} [CommRing A] [Fintype A] [DecidableEq A]
  [Field K] [CharZero K]

/-- Clock after shift, with the repository's phase convention. -/
def heisenberg (ψ : AddChar A K) (s t : A) : Matrix A A K :=
  fun x y => if x=y+s then ψ (t*x) else 0

/-- Synthesis in Heisenberg coordinates, after eliminating the unique shift. -/
def synth (ψ : AddChar A K) (c : A×A → K) : Matrix A A K :=
  fun x y => ∑ t, c (x-y,t)*ψ (t*x)

/-- Character orthogonality extracts the coefficient on each shifted diagonal. -/
def coeff (ψ : AddChar A K) (C : Matrix A A K) (st : A×A) : K :=
  (Fintype.card A : K)⁻¹ * ∑ x, C x (x-st.1)*ψ (-(st.2*x))

theorem coeff_synth (ψ : AddChar A K) (hp : ψ.IsPrimitive) (c : A×A → K) :
    coeff ψ (synth ψ c)=c := by
  funext ⟨s,t⟩
  simp only [coeff,synth,sub_sub_cancel]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have hterm : ∀ u, (∑ x : A, c (s,u)*ψ (u*x)*ψ (-(t*x))) =
      c (s,u)*(if u=t then (Fintype.card A : K) else 0) := by
    intro u
    simp_rw [mul_assoc,← ψ.map_add_eq_mul]
    have he : ∀ x : A, u*x+-(t*x)=(u-t)*x := by intro x; ring
    simp_rw [he]
    rw [← Finset.mul_sum,character_orthogonality ψ hp]
    simp only [sub_eq_zero]
  simp_rw [hterm]
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  have hn : (Fintype.card A : K)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

theorem synth_coeff (ψ : AddChar A K) (hp : ψ.IsPrimitive) (C : Matrix A A K) :
    synth ψ (coeff ψ C)=C := by
  ext x y
  simp only [synth,coeff]
  simp_rw [mul_assoc,Finset.sum_mul,← Finset.mul_sum]
  rw [Finset.sum_comm]
  have hterm : ∀ z : A,
      (∑ t : A, C z (z-(x-y))*ψ (-(t*z))*ψ (t*x)) =
      C z (z-(x-y))*(if x=z then (Fintype.card A : K) else 0) := by
    intro z
    simp_rw [mul_assoc,← ψ.map_add_eq_mul]
    have he : ∀ t : A, -(t*z)+t*x=(x-z)*t := by intro t; ring
    simp_rw [he]
    rw [← Finset.mul_sum,character_orthogonality ψ hp]
    simp only [sub_eq_zero]
  simp_rw [hterm]
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,if_true,sub_sub_cancel]
  have hn : (Fintype.card A : K)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

/-- Every matrix has unique Heisenberg coordinates, without a rank premise. -/
def coordinates (ψ : AddChar A K) (hp : ψ.IsPrimitive) :
    Matrix A A K ≃ₗ[K] (A×A → K) where
  toFun := coeff ψ
  invFun := synth ψ
  left_inv := synth_coeff ψ hp
  right_inv := coeff_synth ψ hp
  map_add' C D := by
    funext ⟨s,t⟩
    simp [coeff,add_mul,Finset.sum_add_distrib,mul_add]
  map_smul' r C := by
    funext ⟨s,t⟩
    simp [coeff,smul_eq_mul,mul_assoc,← Finset.mul_sum,mul_left_comm]

/-- The actual N squared Heisenberg basis, over a primitive character field. -/
def basis (ψ : AddChar A K) (hp : ψ.IsPrimitive) :
    Basis (A×A) K (Matrix A A K) := Basis.ofEquivFun (coordinates ψ hp)

theorem basis_apply (ψ : AddChar A K) (hp : ψ.IsPrimitive) (s t : A) :
    basis ψ hp (s,t)=heisenberg ψ s t := by
  rw [basis,Basis.coe_ofEquivFun]
  change synth ψ (Pi.single (s,t) 1)=heisenberg ψ s t
  ext x y
  simp only [synth,heisenberg]
  by_cases h : x-y=s
  · have hxy : x=y+s := by linear_combination h
    simp [Pi.single_apply,h,hxy]
  · have hxy : x≠y+s := by intro he; apply h; linear_combination he
    simp [Pi.single_apply,h,hxy,Prod.ext_iff]

omit [Fintype A] [CharZero K] in
theorem heisenberg_apply (ψ : AddChar A K) (s t x y : A) :
    heisenberg ψ s t x y = if y=x-s then ψ (t*x) else 0 := by
  have he : x=y+s ↔ y=x-s := by
    constructor <;> intro h <;> rw [h] <;> ring
  simp only [heisenberg,he]

omit [CharZero K] in
theorem fourier_mul_heisenberg_entry (ψ : AddChar A K) (s t x y : A) :
    (fourier ψ*heisenberg ψ s t) x y = ψ ((x+t)*(y+s)) := by
  simp only [Matrix.mul_apply,fourier,heisenberg,mul_ite,mul_zero]
  rw [Finset.sum_ite_eq',if_pos (Finset.mem_univ _),← ψ.map_add_eq_mul]
  congr 1
  ring

theorem heisenberg_mul_fourier_entry (ψ : AddChar A K) (s t x y : A) :
    (heisenberg ψ s t*fourier ψ) x y = ψ (t*x+(x-s)*y) := by
  simp only [Matrix.mul_apply,fourier,heisenberg_apply,ite_mul,zero_mul]
  rw [Finset.sum_ite_eq',if_pos (Finset.mem_univ _),← ψ.map_add_eq_mul]

theorem fourier_intertwines (ψ : AddChar A K) (s t : A) :
    fourier ψ*heisenberg ψ s t =
      ψ (s*t) • (heisenberg ψ (-t) s*fourier ψ) := by
  ext x y
  rw [fourier_mul_heisenberg_entry]
  simp only [Matrix.smul_apply,smul_eq_mul,heisenberg_mul_fourier_entry]
  rw [← ψ.map_add_eq_mul]
  congr 1
  ring

omit [CharZero K] in
theorem chirp_intertwines (ψ : AddChar A K) (s t : A) :
    halfChirp ψ 1*heisenberg ψ s t =
      ψ (-(s*s)) • (heisenberg ψ s (t+2*s)*halfChirp ψ 1) := by
  ext x y
  simp only [halfChirp,diagonal_mul,mul_diagonal,Matrix.smul_apply,smul_eq_mul]
  by_cases h : x=y+s
  · simp only [heisenberg,h,if_true,one_mul]
    rw [← ψ.map_add_eq_mul,← ψ.map_add_eq_mul,← ψ.map_add_eq_mul]
    congr 1
    ring
  · simp [heisenberg,h]

theorem heisenberg_transpose (ψ : AddChar A K) (s t : A) :
    (heisenberg ψ s t).transpose = ψ (s*t) • heisenberg ψ (-s) t := by
  ext x y
  change (if y=x+s then ψ (t*y) else 0)=ψ (s*t)*heisenberg ψ (-s) t x y
  rw [heisenberg_apply,sub_neg_eq_add]
  by_cases h : y=x+s
  · simp only [h,if_true]
    rw [← ψ.map_add_eq_mul]
    congr 1
    ring
  · simp [h]

theorem basis_repr (ψ : AddChar A K) (hp : ψ.IsPrimitive)
    (C : Matrix A A K) (w : A×A) : (basis ψ hp).repr C w=coeff ψ C w :=
  Basis.ofEquivFun_repr_apply (coordinates ψ hp) C w

theorem expansion (ψ : AddChar A K) (hp : ψ.IsPrimitive) (C : Matrix A A K) :
    (∑ w : A×A, coeff ψ C w • heisenberg ψ w.1 w.2)=C := by
  have hb : ∀ w : A×A, basis ψ hp w=heisenberg ψ w.1 w.2 := by
    rintro ⟨s,t⟩; exact basis_apply ψ hp s t
  simpa only [basis_repr,hb] using (basis ψ hp).sum_repr C

theorem synth_as_sum (ψ : AddChar A K) (hp : ψ.IsPrimitive) (c : A×A → K) :
    synth ψ c=∑ w : A×A, c w • heisenberg ψ w.1 w.2 := by
  have he := expansion ψ hp (synth ψ c)
  rw [coeff_synth ψ hp] at he
  exact he.symm

def rotate : A×A ≃ A×A where
  toFun w := (-w.2,w.1)
  invFun w := (w.2,-w.1)
  left_inv := by rintro ⟨s,t⟩; simp
  right_inv := by rintro ⟨s,t⟩; simp

def shear : A×A ≃ A×A where
  toFun w := (w.1,w.2+2*w.1)
  invFun w := (w.1,w.2-2*w.1)
  left_inv := by rintro ⟨s,t⟩; simp
  right_inv := by rintro ⟨s,t⟩; simp

def monomialAction (r : A×A ≃ A×A) (phase : A×A → K) (c : A×A → K) :
    A×A → K := fun w => phase (r.symm w)*c (r.symm w)

theorem reindex_synth (ψ : AddChar A K) (hp : ψ.IsPrimitive)
    (r : A×A ≃ A×A) (phase c : A×A → K) :
    synth ψ (monomialAction r phase c) =
      ∑ w : A×A, (phase w*c w) • heisenberg ψ (r w).1 (r w).2 := by
  rw [synth_as_sum ψ hp]
  exact Fintype.sum_equiv r.symm _ _ (by intro w; simp [monomialAction])

theorem fourier_conjugates (ψ : AddChar A K) (hp : ψ.IsPrimitive) (s t : A) :
    fourier ψ*heisenberg ψ s t*inverseFourier ψ =
      ψ (s*t) • heisenberg ψ (-t) s := by
  rw [fourier_intertwines,Matrix.smul_mul,mul_assoc,fourier_inverse ψ hp,mul_one]

theorem fourier_synth (ψ : AddChar A K) (hp : ψ.IsPrimitive) (c : A×A → K) :
    fourier ψ*synth ψ c*inverseFourier ψ =
      synth ψ (monomialAction rotate (fun w => ψ (w.1*w.2)) c) := by
  rw [synth_as_sum ψ hp,Matrix.mul_sum,Matrix.sum_mul,reindex_synth ψ hp]
  apply Finset.sum_congr rfl
  rintro ⟨s,t⟩ _
  simp only [Matrix.mul_smul,Matrix.smul_mul,fourier_conjugates ψ hp,
    smul_smul,rotate]
  rw [mul_comm]
  rfl

omit [CommRing A] [CharZero K] in
theorem conjugation_fixed_iff (G J C : Matrix A A K) (hGJ : G*J=1) (hJG : J*G=1) :
    G*C*J=C ↔ Commute C G := by
  constructor
  · intro h
    have he := congrArg (fun M : Matrix A A K => M*G) h
    simp only [mul_assoc,hJG,mul_one] at he
    exact he.symm
  · intro h
    rw [← h.eq,mul_assoc,hGJ,mul_one]

omit [CommRing A] [Fintype A] [DecidableEq A] [CharZero K] in
theorem monomial_fixed_iff (r : A×A ≃ A×A) (phase c : A×A → K) :
    monomialAction r phase c=c ↔ ∀ w, c (r w)=phase w*c w := by
  constructor
  · intro h w
    have he := congrFun h (r w)
    simpa [monomialAction] using he.symm
  · intro h
    funext w
    simpa [monomialAction] using (h (r.symm w)).symm

theorem commute_fourier_iff (ψ : AddChar A K) (hp : ψ.IsPrimitive) (C : Matrix A A K) :
    Commute C (fourier ψ) ↔ ∀ s t,
      coeff ψ C (-t,s)=ψ (s*t)*coeff ψ C (s,t) := by
  rw [← conjugation_fixed_iff (fourier ψ) (inverseFourier ψ) C
    (fourier_inverse ψ hp) (inverse_fourier ψ hp)]
  have hC : C=synth ψ (coeff ψ C) := (synth_coeff ψ hp C).symm
  conv_lhs => lhs; rw [hC,fourier_synth ψ hp]
  conv_lhs => rhs; rw [hC]
  have hinj : Function.Injective (synth ψ) := (coordinates ψ hp).symm.injective
  rw [hinj.eq_iff]
  change monomialAction rotate (fun w => ψ (w.1*w.2)) (coeff ψ C)=coeff ψ C ↔ _
  rw [monomial_fixed_iff]
  constructor
  · intro h s t; exact h (s,t)
  · intro h ⟨s,t⟩; exact h s t

omit [CharZero K] in
theorem chirp_inverse (ψ : AddChar A K) :
    halfChirp ψ 1*halfChirp ψ (-1)=(1 : Matrix A A K) := by
  ext x y
  simp only [halfChirp,diagonal_mul,Matrix.diagonal_apply,Matrix.one_apply]
  by_cases h : x=y
  · subst y
    simp only [if_true,one_mul,neg_mul]
    rw [← ψ.map_add_eq_mul]
    simp
  · simp [h]

omit [CharZero K] in
theorem inverse_chirp (ψ : AddChar A K) :
    halfChirp ψ (-1)*halfChirp ψ 1=(1 : Matrix A A K) := by
  ext x y
  simp only [halfChirp,diagonal_mul,Matrix.diagonal_apply,Matrix.one_apply]
  by_cases h : x=y
  · subst y
    simp only [if_true,one_mul,neg_mul]
    rw [← ψ.map_add_eq_mul]
    simp
  · simp [h]

theorem chirp_conjugates (ψ : AddChar A K) (s t : A) :
    halfChirp ψ 1*heisenberg ψ s t*halfChirp ψ (-1) =
      ψ (-(s*s)) • heisenberg ψ s (t+2*s) := by
  rw [chirp_intertwines,Matrix.smul_mul,mul_assoc,chirp_inverse,mul_one]

theorem chirp_synth (ψ : AddChar A K) (hp : ψ.IsPrimitive) (c : A×A → K) :
    halfChirp ψ 1*synth ψ c*halfChirp ψ (-1) =
      synth ψ (monomialAction shear (fun w => ψ (-(w.1*w.1))) c) := by
  rw [synth_as_sum ψ hp,Matrix.mul_sum,Matrix.sum_mul,reindex_synth ψ hp]
  apply Finset.sum_congr rfl
  rintro ⟨s,t⟩ _
  simp only [Matrix.mul_smul,Matrix.smul_mul,chirp_conjugates,smul_smul]
  rw [mul_comm]
  rfl

theorem commute_chirp_iff (ψ : AddChar A K) (hp : ψ.IsPrimitive) (C : Matrix A A K) :
    Commute C (halfChirp ψ 1) ↔ ∀ s t,
      coeff ψ C (s,t+2*s)=ψ (-(s*s))*coeff ψ C (s,t) := by
  rw [← conjugation_fixed_iff (halfChirp ψ 1) (halfChirp ψ (-1)) C
    (chirp_inverse ψ) (inverse_chirp ψ)]
  have hC : C=synth ψ (coeff ψ C) := (synth_coeff ψ hp C).symm
  conv_lhs => lhs; rw [hC,chirp_synth ψ hp]
  conv_lhs => rhs; rw [hC]
  have hinj : Function.Injective (synth ψ) := (coordinates ψ hp).symm.injective
  rw [hinj.eq_iff,monomial_fixed_iff]
  constructor
  · intro h s t; exact h (s,t)
  · intro h ⟨s,t⟩; exact h s t

/-- Literal commutant membership is exactly the two corrected coefficient laws. -/
theorem commutant_iff (ψ : AddChar A K) (hp : ψ.IsPrimitive) (C : Matrix A A K) :
    C ∈ PerfectPower.CommutantDimension.pairSpace (fourier ψ) (halfChirp ψ 1) ↔
      (∀ s t, coeff ψ C (-t,s)=ψ (s*t)*coeff ψ C (s,t)) ∧
      (∀ s t, coeff ψ C (s,t+2*s)=ψ (-(s*s))*coeff ψ C (s,t)) := by
  change (Commute C (fourier ψ) ∧ Commute C (halfChirp ψ 1)) ↔ _
  rw [commute_fourier_iff ψ hp,commute_chirp_iff ψ hp]

open PerfectPower.MonomialOrbitSpace PerfectPower.WeilOrbitSymmetry

def moves : Bool → (A×A ≃ A×A)
  | true => rotate
  | false => shear

def phases (ψ : AddChar A K) : Bool → (A×A → K)
  | true => fun w => ψ (w.1*w.2)
  | false => fun w => ψ (-(w.1*w.1))

/-- Concrete matrices, with their actual generator equations, not a supplied basis. -/
def commutantEquiv (ψ : AddChar A K) (hp : ψ.IsPrimitive) :
    PerfectPower.CommutantDimension.pairSpace (fourier ψ) (halfChirp ψ 1) ≃ₗ[K]
      phaseSpace moves (phases ψ) where
  toFun C := ⟨coeff ψ C.val,by
    intro g w
    have he := (commutant_iff ψ hp C.val).mp C.property
    cases g <;> rcases w with ⟨s,t⟩
    · exact he.2 s t
    · exact he.1 s t⟩
  invFun c := ⟨synth ψ c.val,by
    apply (commutant_iff ψ hp _).mpr
    rw [coeff_synth ψ hp]
    exact ⟨fun s t => c.property true (s,t),fun s t => c.property false (s,t)⟩⟩
  left_inv C := by apply Subtype.ext; exact synth_coeff ψ hp C.val
  right_inv c := by apply Subtype.ext; exact coeff_synth ψ hp c.val
  map_add' C D := by apply Subtype.ext; exact (coordinates ψ hp).map_add C.val D.val
  map_smul' r C := by apply Subtype.ext; exact (coordinates ψ hp).map_smul r C.val

omit [Fintype A] [DecidableEq A] in
theorem character_ne_zero (ψ : AddChar A K) (x : A) : ψ x≠0 := by
  intro h
  have he := ψ.map_add_eq_mul x (-x)
  simp [h] at he

def oddGauge (ψ : AddChar A K) (h : A) (w : A×A) : K := ψ (-h*w.1*w.2)

omit [Fintype A] [DecidableEq A] [CharZero K] in
theorem odd_gauge_consistent (ψ : AddChar A K) (h : A) (hh : 2*h=1) :
    ∀ g w, oddGauge ψ h (moves g w)=phases ψ g w*oddGauge ψ h w := by
  intro g ⟨s,t⟩
  cases g
  · change ψ (-h*s*(t+2*s))=ψ (-(s*s))*ψ (-h*s*t)
    rw [← ψ.map_add_eq_mul,odd_chirp_gauge h s t hh]
    congr 1; ring
  · change ψ (-h*(-t)*s)=ψ (s*t)*ψ (-h*s*t)
    rw [← ψ.map_add_eq_mul,odd_fourier_gauge h s t hh]
    congr 1; ring

/-- The literal odd-level commutant is the space of functions on its orbit quotient. -/
def oddOrbitEquiv (ψ : AddChar A K) (hp : ψ.IsPrimitive) (h : A) (hh : 2*h=1) :
    PerfectPower.CommutantDimension.pairSpace (fourier ψ) (halfChirp ψ 1) ≃ₗ[K]
      (Orbits (moves (A:=A)) → K) :=
  (commutantEquiv ψ hp).trans
    ((gaugeEquiv moves (phases ψ) (oddGauge ψ h)
      (fun _ => character_ne_zero ψ _) (odd_gauge_consistent ψ h hh)).symm.trans
        (quotientEquiv moves))

theorem odd_commutant_finrank (ψ : AddChar A K) (hp : ψ.IsPrimitive)
    (h : A) (hh : 2*h=1) :
    Module.finrank K (PerfectPower.CommutantDimension.pairSpace
      (fourier ψ) (halfChirp ψ 1))=Fintype.card (Orbits (moves (A:=A))) := by
  rw [(oddOrbitEquiv ψ hp h hh).finrank_eq]
  exact Module.finrank_fintype_fun_eq_card K

def reflect : A×A ≃ A×A where
  toFun w := (-w.1,w.2)
  invFun w := (-w.1,w.2)
  left_inv := by rintro ⟨s,t⟩; simp
  right_inv := by rintro ⟨s,t⟩; simp

theorem transpose_synth (ψ : AddChar A K) (hp : ψ.IsPrimitive) (c : A×A → K) :
    (synth ψ c).transpose=
      synth ψ (monomialAction reflect (fun w => ψ (w.1*w.2)) c) := by
  rw [synth_as_sum ψ hp,transpose_sum,reindex_synth ψ hp]
  apply Finset.sum_congr rfl
  rintro ⟨s,t⟩ _
  simp only [transpose_smul,heisenberg_transpose,smul_smul]
  rw [mul_comm]
  rfl

/-- The remaining arithmetic hypothesis is orbit preservation by reflection. -/
theorem odd_commutant_symmetric (ψ : AddChar A K) (hp : ψ.IsPrimitive)
    (h : A) (hh : 2*h=1)
    (hr : ∀ w : A×A, (orbitSetoid (moves (A:=A))).r w (reflect w))
    (C : PerfectPower.CommutantDimension.pairSpace (fourier ψ) (halfChirp ψ 1)) :
    C.val.transpose=C.val := by
  have ht : ∀ w : A×A, oddGauge ψ h (reflect w)=ψ (w.1*w.2)*oddGauge ψ h w := by
    rintro ⟨s,t⟩
    change ψ (-h*(-s)*t)=ψ (s*t)*ψ (-h*s*t)
    rw [← ψ.map_add_eq_mul,← odd_transpose_gauge h s t hh]
    congr 1; ring
  have hc := reflection_coeff moves (phases ψ) (oddGauge ψ h)
    (fun _ => character_ne_zero ψ _) (odd_gauge_consistent ψ h hh)
    reflect (fun w => ψ (w.1*w.2)) hr ht (commutantEquiv ψ hp C)
  have hf : monomialAction reflect (fun w => ψ (w.1*w.2)) (coeff ψ C.val)=
      coeff ψ C.val := by
    apply (monomial_fixed_iff _ _ _).mpr
    exact hc
  have hC : C.val=synth ψ (coeff ψ C.val) := (synth_coeff ψ hp C.val).symm
  calc
    C.val.transpose=(synth ψ (coeff ψ C.val)).transpose := congrArg Matrix.transpose hC
    _ = synth ψ (coeff ψ C.val) := by rw [transpose_synth ψ hp,hf]
    _ = C.val := synth_coeff ψ hp C.val

theorem odd_commutative_of_reflection (ψ : AddChar A K) (hp : ψ.IsPrimitive)
    (h : A) (hh : 2*h=1)
    (hr : ∀ w : A×A, (orbitSetoid (moves (A:=A))).r w (reflect w))
    (C D : Matrix A A K)
    (hC : C ∈ PerfectPower.CommutantDimension.pairSpace (fourier ψ) (halfChirp ψ 1))
    (hD : D ∈ PerfectPower.CommutantDimension.pairSpace (fourier ψ) (halfChirp ψ 1)) :
    Commute C D := by
  apply commutative_of_symmetric (fourier ψ) (halfChirp ψ 1) _ C D hC hD
  intro M hM
  exact odd_commutant_symmetric ψ hp h hh hr ⟨M,hM⟩

/-- The half is derived for every positive odd cyclic modulus. -/
theorem odd_level_finrank {n : ℕ} [NeZero n]
    (ψ : AddChar (ZMod n) K) (hp : ψ.IsPrimitive) (hn : Odd n) :
    Module.finrank K (PerfectPower.CommutantDimension.pairSpace
      (fourier ψ) (halfChirp ψ 1))=Fintype.card (Orbits (moves (A:=ZMod n))) := by
  obtain ⟨h,hh⟩ := odd_half n hn
  exact odd_commutant_finrank ψ hp h hh

end PerfectPower.WeilMonomial
