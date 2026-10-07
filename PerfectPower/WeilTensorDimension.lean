import PerfectPower.CommutantDimension
import Mathlib.Data.Nat.ModEq
import Mathlib.LinearAlgebra.Matrix.Reindex

noncomputable section
namespace PerfectPower.WeilTensorDimension
open Matrix PerfectPower.WeilCRT PerfectPower.CommutantDimension
variable {K : Type*} [Field K] [CharZero K]
variable {a b : ℕ} [NeZero a] [NeZero b]

 theorem tensor_mul {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A C : Matrix ι ι K) (B D : Matrix κ κ K) :
    kronecker A B * kronecker C D = kronecker (A*C) (B*D) :=
  (Matrix.mul_kronecker_mul A C B D).symm

 theorem kronecker_power {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A : Matrix ι ι K) (B : Matrix κ κ K) (e : ℕ) :
    (kronecker A B)^e=kronecker (A^e) (B^e) := by
  induction e with
  | zero => exact Matrix.one_kronecker_one.symm
  | succ e ih =>
    rw [pow_succ,ih]
    exact (Matrix.mul_kronecker_mul (A^e) A (B^e) B).symm

 theorem chirp_zero {n : ℕ} [NeZero n] (ψ : AddChar (ZMod n) K) :
    halfChirp ψ 0=1 := by
  simp [halfChirp,Matrix.diagonal_one]

 theorem chirp_power {n : ℕ} [NeZero n] (ψ : AddChar (ZMod n) K) (e : ℕ) :
    (halfChirp ψ 1)^e=halfChirp ψ (e : ZMod n) := (halfChirp_power ψ e).symm

 theorem projected_chirp (ψa : AddChar (ZMod a) K) (ψb : AddChar (ZMod b) K)
    (e : ℕ) (heA : e ≡ 1 [MOD a]) (heB : e ≡ 0 [MOD b]) :
    (kronecker (halfChirp ψa 1) (halfChirp ψb 1))^e=
      kronecker (halfChirp ψa 1) (1 : Matrix (ZMod b) (ZMod b) K) := by
  rw [kronecker_power,chirp_power,chirp_power]
  have hA : (e : ZMod a)=1 := by simpa using (ZMod.natCast_eq_natCast_iff e 1 a).mpr heA
  have hB : (e : ZMod b)=0 := by simpa using (ZMod.natCast_eq_natCast_iff e 0 b).mpr heB
  rw [hA,hB,chirp_zero]

/-- The odd Fourier recovery word lifts into a tensor factor while the other
Fourier pair cancels against its checked inverse. -/
theorem recovery_word
    (ψa : AddChar (ZMod a) K) (ψb : AddChar (ZMod b) K)
    (ha : ψa.IsPrimitive) (hb : ψb.IsPrimitive) (h : ZMod b) (hh : 2*h=1) :
    kronecker (1 : Matrix (ZMod a) (ZMod a) K) (fourier ψb) =
      ((Fintype.card (ZMod b) : K)/gauss ψb h) •
        (kronecker (1 : Matrix (ZMod a) (ZMod a) K) (halfChirp ψb h) *
          (kronecker (fourier ψa) (fourier ψb) *
            kronecker (1 : Matrix (ZMod a) (ZMod a) K) (halfChirp ψb h) *
            kronecker (inverseFourier ψa) (inverseFourier ψb)) *
          kronecker (1 : Matrix (ZMod a) (ZMod a) K) (halfChirp ψb h)) := by
  have he := recover_fourier ψb hb h hh
  rw [tensor_mul,tensor_mul,
    tensor_mul,tensor_mul]
  simp only [Matrix.mul_one,Matrix.one_mul,fourier_inverse ψa ha]
  calc
    kronecker 1 (fourier ψb) = kronecker 1
        (((Fintype.card (ZMod b) : K)/gauss ψb h) •
          (halfChirp ψb h*(fourier ψb*halfChirp ψb h*inverseFourier ψb)*halfChirp ψb h)) :=
      congrArg (fun M => kronecker (1 : Matrix (ZMod a) (ZMod a) K) M) he
    _ = _ := Matrix.kronecker_smul _ _ _

/-- A complete separation packet for coprime cyclic levels with an odd second
factor. Only primitivity and elementary modulus hypotheses are inputs. -/
def packet (ψa : AddChar (ZMod a) K) (ψb : AddChar (ZMod b) K)
    (ha : ψa.IsPrimitive) (hb : ψb.IsPrimitive) (co : a.Coprime b) (oddB : Odd b) :
    SeparationData (K:=K) (B:=Matrix (ZMod a×ZMod b) (ZMod a×ZMod b) K) := by
  classical
  let h := Classical.choose (odd_half b oddB)
  have hh := Classical.choose_spec (odd_half b oddB)
  let ea := Nat.chineseRemainder co 1 0
  let eb := Nat.chineseRemainder co 0 1
  refine {
    F := kronecker (fourier ψa) (fourier ψb)
    T := kronecker (halfChirp ψa 1) (halfChirp ψb 1)
    FA := kronecker (fourier ψa) 1
    FB := kronecker 1 (fourier ψb)
    TA := kronecker (halfChirp ψa 1) 1
    TB := kronecker 1 (halfChirp ψb 1)
    J := kronecker (inverseFourier ψa) (inverseFourier ψb)
    JB := kronecker 1 (inverseFourier ψb)
    leftExponent := ea.val
    rightExponent := eb.val
    halfExponent := h.val
    scalar := (Fintype.card (ZMod b) : K)/gauss ψb h
    fourier_product := ?_
    chirp_product := ?_
    project_left := projected_chirp ψa ψb ea.val ea.property.1 ea.property.2
    project_right := ?_
    inverse_right := ?_
    inverse_left := ?_
    local_inverse := ?_
    local_inverse_left := ?_
    recovery := ?_ }
  · rw [tensor_mul]; simp
  · rw [tensor_mul]; simp
  · rw [kronecker_power,chirp_power,chirp_power]
    have hA : (eb.val : ZMod a)=0 := by simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr eb.property.1
    have hB : (eb.val : ZMod b)=1 := by simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr eb.property.2
    rw [hA,hB,chirp_zero]
  · rw [tensor_mul,fourier_inverse ψa ha,fourier_inverse ψb hb]
    exact Matrix.one_kronecker_one
  · rw [tensor_mul,inverse_fourier ψa ha,inverse_fourier ψb hb]
    exact Matrix.one_kronecker_one
  · rw [tensor_mul,fourier_inverse ψb hb,Matrix.one_mul]
    exact Matrix.one_kronecker_one
  · rw [tensor_mul,inverse_fourier ψb hb,Matrix.one_mul]
    exact Matrix.one_kronecker_one
  · rw [kronecker_power,one_pow,chirp_power,ZMod.natCast_zmod_val]
    exact recovery_word ψa ψb ha hb h hh

/-- General kernel-proved multiplicativity for cyclic Fourier/chirp tensor
pairs, including composite odd levels and the dyadic/odd combination. -/
theorem tensor_finrank (ψa : AddChar (ZMod a) K) (ψb : AddChar (ZMod b) K)
    (ha : ψa.IsPrimitive) (hb : ψb.IsPrimitive) (co : a.Coprime b) (oddB : Odd b) :
    Module.finrank K (pairSpace (kronecker (fourier ψa) (fourier ψb))
      (kronecker (halfChirp ψa 1) (halfChirp ψb 1))) =
      Module.finrank K (pairSpace (fourier ψa) (halfChirp ψa 1)) *
        Module.finrank K (pairSpace (fourier ψb) (halfChirp ψb 1)) := by
  exact crt_finrank (packet ψa ψb ha hb co oddB)
    (fourier ψa) (halfChirp ψa 1) (fourier ψb) (halfChirp ψb 1) rfl rfl rfl rfl



/-- Algebra isomorphisms transport the full simultaneous commutant. -/
def pairEquiv {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (E : Matrix ι ι K ≃ₐ[K] Matrix κ κ K) (F T : Matrix ι ι K) :
    pairSpace F T ≃ₗ[K] pairSpace (E F) (E T) where
  toFun C := ⟨E C,by
    constructor
    · change E C*E F=E F*E C
      simpa only [map_mul] using congrArg E C.property.1.eq
    · change E C*E T=E T*E C
      simpa only [map_mul] using congrArg E C.property.2.eq⟩
  invFun C := ⟨E.symm C,by
    constructor
    · change E.symm C*F=F*E.symm C
      simpa only [map_mul,E.symm_apply_apply] using congrArg E.symm C.property.1.eq
    · change E.symm C*T=T*E.symm C
      simpa only [map_mul,E.symm_apply_apply] using congrArg E.symm C.property.2.eq⟩
  left_inv C := by apply Subtype.ext; exact E.symm_apply_apply C
  right_inv C := by apply Subtype.ext; exact E.apply_symm_apply C
  map_add' C D := by apply Subtype.ext; exact E.map_add C D
  map_smul' r C := by apply Subtype.ext; exact E.toLinearMap.map_smul r C

def productCharacter (ψa : AddChar (ZMod a) K) (ψb : AddChar (ZMod b) K) :
    AddChar (ZMod a×ZMod b) K where
  toFun x := ψa x.1*ψb x.2
  map_zero_eq_one' := by simp
  map_add_eq_mul' := by
    intro x y
    simp only [Prod.fst_add,Prod.snd_add,AddChar.map_add_eq_mul]
    ring

def crtCharacter (ψa : AddChar (ZMod a) K) (ψb : AddChar (ZMod b) K)
    (co : a.Coprime b) : AddChar (ZMod (a*b)) K :=
  (productCharacter ψa ψb).compAddMonoidHom (ZMod.chineseRemainder co).toAddMonoidHom

 theorem productCharacter_primitive (ψa : AddChar (ZMod a) K) (ψb : AddChar (ZMod b) K)
    (ha : ψa.IsPrimitive) (hb : ψb.IsPrimitive) : (productCharacter ψa ψb).IsPrimitive := by
  intro x hx he
  have hA : x.1=0 := by
    by_contra hn
    apply ha hn
    ext t
    have hv := congrArg (fun ψ : AddChar (ZMod a×ZMod b) K => ψ (t,0)) he
    simpa [AddChar.mulShift_apply,productCharacter] using hv
  have hB : x.2=0 := by
    by_contra hn
    apply hb hn
    ext t
    have hv := congrArg (fun ψ : AddChar (ZMod a×ZMod b) K => ψ (0,t)) he
    simpa [AddChar.mulShift_apply,productCharacter] using hv
  exact hx (Prod.ext hA hB)

 theorem crtCharacter_primitive (ψa : AddChar (ZMod a) K) (ψb : AddChar (ZMod b) K)
    (ha : ψa.IsPrimitive) (hb : ψb.IsPrimitive) (co : a.Coprime b) :
    (crtCharacter ψa ψb co).IsPrimitive := by
  intro x hx he
  have hn : (ZMod.chineseRemainder co) x ≠ 0 := by
    intro hz
    apply hx
    exact (ZMod.chineseRemainder co).injective (by simpa using hz)
  apply productCharacter_primitive ψa ψb ha hb hn
  ext t
  have hv := congrArg (fun ψ : AddChar (ZMod (a*b)) K => ψ ((ZMod.chineseRemainder co).symm t)) he
  simpa [AddChar.mulShift_apply,crtCharacter,map_mul] using hv

 theorem crt_fourier (ψa : AddChar (ZMod a) K) (ψb : AddChar (ZMod b) K)
    (co : a.Coprime b) :
    Matrix.reindexAlgEquiv K K (ZMod.chineseRemainder co).toEquiv
      (fourier (crtCharacter ψa ψb co)) = kronecker (fourier ψa) (fourier ψb) := by
  ext x y
  change productCharacter ψa ψb ((ZMod.chineseRemainder co)
    ((ZMod.chineseRemainder co).symm x*(ZMod.chineseRemainder co).symm y)) =
      ψa (x.1*y.1)*ψb (x.2*y.2)
  rw [map_mul,RingEquiv.apply_symm_apply,RingEquiv.apply_symm_apply]
  rfl

 theorem reindex_diagonal {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (d : ι → K) :
    Matrix.reindexAlgEquiv K K e (diagonal d)=diagonal (fun i => d (e.symm i)) := by
  ext i j
  change diagonal d (e.symm i) (e.symm j)=diagonal (fun i => d (e.symm i)) i j
  simp [Matrix.diagonal,e.symm.injective.eq_iff]

 theorem crt_chirp (ψa : AddChar (ZMod a) K) (ψb : AddChar (ZMod b) K)
    (co : a.Coprime b) :
    Matrix.reindexAlgEquiv K K (ZMod.chineseRemainder co).toEquiv
      (halfChirp (crtCharacter ψa ψb co) 1) =
        kronecker (halfChirp ψa 1) (halfChirp ψb 1) := by
  rw [halfChirp,reindex_diagonal]
  change diagonal (fun x => crtCharacter ψa ψb co
    (1*((ZMod.chineseRemainder co).symm x)^2)) = _
  have he (x : ZMod a×ZMod b) : crtCharacter ψa ψb co
      (1*((ZMod.chineseRemainder co).symm x)^2) = ψa (1*x.1^2)*ψb (1*x.2^2) := by
    change productCharacter ψa ψb ((ZMod.chineseRemainder co)
      (1*((ZMod.chineseRemainder co).symm x)^2)) = _
    rw [map_mul,map_one,map_pow,RingEquiv.apply_symm_apply]
    rfl
  simp_rw [he]
  exact (Matrix.diagonal_kronecker_diagonal
    (fun x : ZMod a => ψa (1*x^2)) (fun y : ZMod b => ψb (1*y^2))).symm

/-- Actual cyclic CRT coordinates, rather than an assumed matrix factorization. -/
theorem crt_character_finrank (ψa : AddChar (ZMod a) K) (ψb : AddChar (ZMod b) K)
    (ha : ψa.IsPrimitive) (hb : ψb.IsPrimitive) (co : a.Coprime b) (oddB : Odd b) :
    Module.finrank K (pairSpace (fourier (crtCharacter ψa ψb co))
      (halfChirp (crtCharacter ψa ψb co) 1)) =
      Module.finrank K (pairSpace (fourier ψa) (halfChirp ψa 1)) *
        Module.finrank K (pairSpace (fourier ψb) (halfChirp ψb 1)) := by
  rw [(pairEquiv (Matrix.reindexAlgEquiv K K (ZMod.chineseRemainder co).toEquiv)
    (fourier (crtCharacter ψa ψb co)) (halfChirp (crtCharacter ψa ψb co) 1)).finrank_eq,
    crt_fourier,crt_chirp]
  exact tensor_finrank ψa ψb ha hb co oddB

end PerfectPower.WeilTensorDimension
