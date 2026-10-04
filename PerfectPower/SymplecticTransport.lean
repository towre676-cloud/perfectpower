import Mathlib

noncomputable section
namespace PerfectPower.SymplecticTransport
open Matrix
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {K : Type*} [CommRing K]

/-- A certified integral basis change recovers the original alternating form exactly. -/
theorem recover_form (Ω J S I : Matrix ι ι K) (hSI : S*I=1)
    (h : S.transpose*Ω*S=J) : Ω=I.transpose*J*I := by
  rw [← h]
  have ht : I.transpose*S.transpose=1 := by rw [← transpose_mul,hSI,transpose_one]
  simp only [← Matrix.mul_assoc,ht,one_mul]
  rw [Matrix.mul_assoc,hSI,mul_one]

theorem inverse_form (Ω J S I T : Matrix ι ι K) (hSI : S*I=1) (hIS : I*S=1)
    (h : S.transpose*Ω*S=J) (hJT : J*T=1) (hTJ : T*J=1) :
    Ω*(S*T*S.transpose)=1 ∧ (S*T*S.transpose)*Ω=1 := by
  have hr := recover_form Ω J S I hSI h
  have hti : I.transpose*S.transpose=1 := by rw [← transpose_mul,hSI,transpose_one]
  have hts : S.transpose*I.transpose=1 := by rw [← transpose_mul,hIS,transpose_one]
  rw [hr]
  constructor
  · calc (I.transpose*J*I)*(S*T*S.transpose)=I.transpose*J*(I*S)*T*S.transpose := by
          simp only [Matrix.mul_assoc]
      _=I.transpose*(J*T)*S.transpose := by rw [hIS,mul_one];simp only [Matrix.mul_assoc]
      _=1 := by rw [hJT,mul_one,hti]
  · calc (S*T*S.transpose)*(I.transpose*J*I)=S*T*(S.transpose*I.transpose)*J*I := by
          simp only [Matrix.mul_assoc]
      _=S*(T*J)*I := by rw [hts,mul_one];simp only [Matrix.mul_assoc]
      _=1 := by rw [hTJ,mul_one,hSI]

omit [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
/-- Bilinear period diagnostics transform exactly under a supplied basis change. -/
theorem bilinear_transport (P : Matrix κ ι K) (S T : Matrix ι ι K) :
    P*(S*T*S.transpose)*P.transpose=(P*S)*T*(P*S).transpose := by
  simp only [transpose_mul,Matrix.mul_assoc]

end PerfectPower.SymplecticTransport
