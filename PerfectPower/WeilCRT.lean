import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Data.Matrix.Kronecker
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

noncomputable section
namespace PerfectPower.WeilCRT
open scoped BigOperators
open Matrix

section Gauss
variable {A K : Type*} [CommRing A] [Fintype A] [DecidableEq A]
  [Field K] [CharZero K]

def gauss (ψ : AddChar A K) (h : A) : K := ∑ z, ψ (h*z^2)
def fourier (ψ : AddChar A K) : Matrix A A K := fun x y => ψ (x*y)
def reverseFourier (ψ : AddChar A K) : Matrix A A K := fun x y => ψ (-(x*y))
def halfChirp (ψ : AddChar A K) (h : A) : Matrix A A K :=
  diagonal (fun x => ψ (h*x^2))

/-- Completing the square works over every finite commutative ring with a half. -/
theorem square_phase (h x y z : A) (hh : 2*h=1) :
    h*x^2+h*y^2+h*z^2+(x-y)*z = x*y+h*(z+(x-y))^2 := by
  have he : (2*h-1)*(x*y-(x-y)*z)=0 := by rw [hh]; ring
  linear_combination he

theorem shifted_gauss (ψ : AddChar A K) (h c : A) :
    (∑ z, ψ (h*(z+c)^2)) = gauss ψ h := by
  exact Fintype.sum_equiv (Equiv.addRight c) _ _ (fun _ => rfl)

/-- The Fourier generator is recovered from a chirp and its Fourier conjugate. -/
theorem generator_identity (ψ : AddChar A K) (h : A) (hh : 2*h=1) :
    halfChirp ψ h * (fourier ψ * halfChirp ψ h * reverseFourier ψ) *
      halfChirp ψ h = gauss ψ h • fourier ψ := by
  ext x y
  simp only [halfChirp]
  rw [mul_diagonal, diagonal_mul]
  rw [Matrix.mul_apply]
  simp only [mul_diagonal, fourier, reverseFourier, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.sum_mul]
  calc
    (∑ z, ψ (h*x^2) * (ψ (x*z) * ψ (h*z^2) * ψ (-(z*y))) * ψ (h*y^2)) =
        ∑ z, ψ (x*y) * ψ (h*(z+(x-y))^2) := by
      apply Finset.sum_congr rfl
      intro z _
      rw [← ψ.map_add_eq_mul, ← ψ.map_add_eq_mul, ← ψ.map_add_eq_mul,
        ← ψ.map_add_eq_mul, ← ψ.map_add_eq_mul]
      congr 1
      have hs := square_phase h x y z hh
      linear_combination hs
    _ = ψ (x*y) * gauss ψ h := by rw [← Finset.mul_sum, shifted_gauss]
    _ = gauss ψ h * ψ (x*y) := mul_comm _ _

/-- Orthogonality uses a primitive character, including at composite levels. -/
theorem character_orthogonality (ψ : AddChar A K) (hp : ψ.IsPrimitive) (c : A) :
    (∑ z, ψ (c*z)) = if c=0 then (Fintype.card A : K) else 0 := by
  classical
  by_cases hc : c=0
  · simp [hc]
  · have hn : ψ.mulShift c ≠ 0 := hp hc
    have hz := (AddChar.sum_eq_zero_iff_ne_zero).mpr hn
    simpa [AddChar.mulShift_apply, hc, mul_comm] using hz

/-- The change (z,w) ↦ (z-w,z+w) is bijective when 2 is invertible. -/
def squareChange (h : A) (hh : 2*h=1) : A × A ≃ A × A where
  toFun zw := (zw.1-zw.2, zw.1+zw.2)
  invFun uv := (h*(uv.2+uv.1), h*(uv.2-uv.1))
  left_inv := by
    intro ⟨z,w⟩
    ext <;> dsimp
    · linear_combination z*hh
    · linear_combination w*hh
  right_inv := by
    intro ⟨u,v⟩
    ext <;> dsimp
    · linear_combination u*hh
    · linear_combination v*hh

/-- Nonvanishing of the quadratic Gauss sum needs no evaluation of its phase. -/
theorem gauss_product (ψ : AddChar A K) (hp : ψ.IsPrimitive) (h : A)
    (hh : 2*h=1) : gauss ψ h * gauss ψ (-h) = (Fintype.card A : K) := by
  classical
  rw [gauss, gauss, Finset.sum_mul_sum]
  rw [← Fintype.sum_prod_type (fun zw : A×A => ψ (h*zw.1^2)*ψ (-h*zw.2^2))]
  calc
    (∑ zw : A×A, ψ (h*zw.1^2) * ψ (-h*zw.2^2)) =
        ∑ uv : A×A, ψ (h*uv.1*uv.2) := by
      apply Fintype.sum_equiv (squareChange h hh)
      intro ⟨z,w⟩
      simp only [squareChange, Equiv.coe_fn_mk, ← ψ.map_add_eq_mul]
      congr 1
      ring
    _ = ∑ u : A, ∑ v : A, ψ ((h*u)*v) := by rw [Fintype.sum_prod_type]
    _ = (Fintype.card A : K) := by
      simp_rw [character_orthogonality ψ hp]
      have hu (u : A) : h*u=0 ↔ u=0 := by
        constructor
        · intro hz
          have he : (2*h)*u=0 := by rw [mul_assoc,hz,mul_zero]
          simpa [hh] using he
        · intro hz; rw [hz,mul_zero]
      simp_rw [hu]
      simp

theorem gauss_ne_zero (ψ : AddChar A K) (hp : ψ.IsPrimitive) (h : A)
    (hh : 2*h=1) : gauss ψ h ≠ 0 := by
  intro hz
  have hc := gauss_product ψ hp h hh
  rw [hz,zero_mul] at hc
  exact (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) hc.symm

/-- Character orthogonality gives a checked inverse of the unnormalized Fourier matrix. -/
theorem fourier_reverse (ψ : AddChar A K) (hp : ψ.IsPrimitive) :
    fourier ψ * reverseFourier ψ = (Fintype.card A : K) • (1 : Matrix A A K) := by
  ext x y
  simp only [Matrix.mul_apply, fourier, reverseFourier, Matrix.smul_apply, smul_eq_mul]
  have he : (∑ z, ψ (x*z)*ψ (-(z*y))) = ∑ z, ψ ((x-y)*z) := by
    apply Finset.sum_congr rfl
    intro z _
    rw [← ψ.map_add_eq_mul]
    congr 1
    ring
  rw [he,character_orthogonality ψ hp]
  by_cases hxy : x=y <;> simp [hxy,sub_eq_zero,Matrix.one_apply]

theorem reverse_fourier (ψ : AddChar A K) (hp : ψ.IsPrimitive) :
    reverseFourier ψ * fourier ψ = (Fintype.card A : K) • (1 : Matrix A A K) := by
  ext x y
  simp only [Matrix.mul_apply, fourier, reverseFourier, Matrix.smul_apply, smul_eq_mul]
  have he : (∑ z, ψ (-(x*z))*ψ (z*y)) = ∑ z, ψ ((y-x)*z) := by
    apply Finset.sum_congr rfl
    intro z _
    rw [← ψ.map_add_eq_mul]
    congr 1
    ring
  rw [he,character_orthogonality ψ hp]
  by_cases hxy : x=y <;> simp [hxy,sub_eq_zero,eq_comm,Matrix.one_apply]

def inverseFourier (ψ : AddChar A K) : Matrix A A K :=
  (Fintype.card A : K)⁻¹ • reverseFourier ψ

theorem fourier_inverse (ψ : AddChar A K) (hp : ψ.IsPrimitive) :
    fourier ψ * inverseFourier ψ = 1 := by
  rw [inverseFourier,Matrix.mul_smul,fourier_reverse ψ hp,smul_smul]
  simp [Fintype.card_ne_zero]

theorem inverse_fourier (ψ : AddChar A K) (hp : ψ.IsPrimitive) :
    inverseFourier ψ * fourier ψ = 1 := by
  rw [inverseFourier,Matrix.smul_mul,reverse_fourier ψ hp,smul_smul]
  simp [Fintype.card_ne_zero]

theorem recover_fourier (ψ : AddChar A K) (hp : ψ.IsPrimitive) (h : A)
    (hh : 2*h=1) : fourier ψ =
    ((Fintype.card A : K)/gauss ψ h) •
      (halfChirp ψ h*(fourier ψ*halfChirp ψ h*inverseFourier ψ)*halfChirp ψ h) := by
  rw [inverseFourier,Matrix.mul_smul,Matrix.mul_smul,Matrix.smul_mul,
    generator_identity ψ h hh,smul_smul,smul_smul]
  have hc : (Fintype.card A : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hg := gauss_ne_zero ψ hp h hh
  have hs : ((Fintype.card A : K)/gauss ψ h)*((Fintype.card A : K)⁻¹*gauss ψ h)=1 := by
    field_simp
  rw [mul_assoc,hs,one_smul]

/-- This identity connects the half-chirp to a literal power of the original chirp. -/
theorem halfChirp_power {n : ℕ} [NeZero n] (ψ : AddChar (ZMod n) K) (h : ℕ) :
    halfChirp ψ (h : ZMod n) = (halfChirp ψ 1)^h := by
  rw [halfChirp,halfChirp,Matrix.diagonal_pow]
  apply congrArg Matrix.diagonal
  funext x
  simpa [nsmul_eq_mul,Pi.pow_apply,one_mul] using ψ.map_nsmul_eq_pow h (x^2)

end Gauss


section Separation
variable {K B : Type*} [Field K] [Ring B] [Algebra K B]

/-- Commutation transports to an explicitly checked two-sided inverse. -/
theorem commute_inverse (C F J : B) (hC : Commute C F)
    (hFJ : F*J=1) (hJF : J*F=1) : Commute C J := by
  change C*J=J*C
  calc
    C*J = (J*F)*(C*J) := by rw [hJF,one_mul]
    _ = J*(F*C)*J := by simp only [mul_assoc]
    _ = J*(C*F)*J := by rw [hC.eq]
    _ = J*C*(F*J) := by simp only [mul_assoc]
    _ = J*C := by rw [hFJ,mul_one]

/-- Exact data needed to separate the local generators. All identities are
algebraic, and the Gauss theorem above supplies the recovery identity. -/
structure SeparationData where
  F : B
  T : B
  FA : B
  FB : B
  TA : B
  TB : B
  J : B
  JB : B
  leftExponent : ℕ
  rightExponent : ℕ
  halfExponent : ℕ
  scalar : K
  fourier_product : F=FA*FB
  chirp_product : T=TA*TB
  project_left : T^leftExponent=TA
  project_right : T^rightExponent=TB
  inverse_right : F*J=1
  inverse_left : J*F=1
  local_inverse : FB*JB=1
  local_inverse_left : JB*FB=1
  recovery : FB=scalar • (TB^halfExponent*(F*TB^halfExponent*J)*TB^halfExponent)

/-- The simultaneous commutant of the global pair equals that of all four
separate local generators. Tensor factorization alone would not imply this. -/
theorem commutant_separates (d : SeparationData (K:=K) (B:=B)) (C : B) :
    (Commute C d.F ∧ Commute C d.T) ↔
      (Commute C d.FA ∧ Commute C d.FB ∧ Commute C d.TA ∧ Commute C d.TB) := by
  constructor
  · rintro ⟨hF,hT⟩
    have hA : Commute C d.TA := by rw [← d.project_left]; exact hT.pow_right _
    have hB : Commute C d.TB := by rw [← d.project_right]; exact hT.pow_right _
    have hJ := commute_inverse C d.F d.J hF d.inverse_right d.inverse_left
    have hR := hB.pow_right d.halfExponent
    have hFB : Commute C d.FB := by
      rw [d.recovery]
      exact (hR.mul_right ((hF.mul_right hR).mul_right hJ) |>.mul_right hR).smul_right _
    have hJB : Commute C d.JB := by
      exact commute_inverse C d.FB d.JB hFB d.local_inverse d.local_inverse_left
    have hFA : Commute C d.FA := by
      have he : d.FA=d.F*d.JB := by rw [d.fourier_product,mul_assoc,d.local_inverse,mul_one]
      rw [he]
      exact hF.mul_right hJB
    exact ⟨hFA,hFB,hA,hB⟩
  · rintro ⟨hFA,hFB,hTA,hTB⟩
    constructor
    · rw [d.fourier_product]; exact hFA.mul_right hFB
    · rw [d.chirp_product]; exact hTA.mul_right hTB

/-- CRT exponents isolate a factor of a commuting finite-order product. -/
theorem project_power (TA TB : B) (hab : Commute TA TB) (a b k l e : ℕ)
    (ha : TA^a=1) (hb : TB^b=1) (heA : e=1+a*k) (heB : e=b*l) :
    (TA*TB)^e=TA := by
  rw [hab.mul_pow]
  have hA : TA^e=TA := by rw [heA,pow_add,pow_mul,ha,one_pow,pow_one,mul_one]
  have hB : TB^e=1 := by rw [heB,pow_mul,hb,one_pow]
  rw [hA,hB,mul_one]

/-- Tensor products of local commuting operators commute with the global pair. -/
theorem kronecker_commute {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (C F : Matrix ι ι K) (D G : Matrix κ κ K)
    (hC : Commute C F) (hD : Commute D G) :
    Commute (Matrix.kronecker C D) (Matrix.kronecker F G) := by
  change Matrix.kronecker C D * Matrix.kronecker F G =
    Matrix.kronecker F G * Matrix.kronecker C D
  calc
    Matrix.kronecker C D * Matrix.kronecker F G = Matrix.kronecker (C*F) (D*G) :=
      (Matrix.mul_kronecker_mul C F D G).symm
    _ = Matrix.kronecker (F*C) (G*D) := by rw [hC.eq,hD.eq]
    _ = Matrix.kronecker F G * Matrix.kronecker C D := Matrix.mul_kronecker_mul F C G D

/-- Every odd modulus has the half required by the general Gauss proof. -/
theorem odd_half (n : ℕ) (hn : Odd n) : ∃ h : ZMod n, 2*h=1 := by
  have hu : IsUnit (2 : ZMod n) :=
    (ZMod.isUnit_iff_coprime 2 n).mpr (Nat.coprime_two_left.mpr hn)
  obtain ⟨u,hu⟩ := hu
  refine ⟨↑u⁻¹,?_⟩
  rw [← hu]
  simp

end Separation
end PerfectPower.WeilCRT
