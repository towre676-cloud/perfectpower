import PerfectPower.SeparatedDimension
import PerfectPower.WeilCRT

noncomputable section
namespace PerfectPower.CommutantDimension
open scoped BigOperators
open Matrix
variable {K ι κ : Type*} [Field K] [Fintype ι] [Fintype κ]
  [DecidableEq ι] [DecidableEq κ]

/-- The ordinary simultaneous matrix commutant, as a vector subspace. -/
def pairSpace {η : Type*} [Fintype η] [DecidableEq η] (F T : Matrix η η K) :
    Submodule K (Matrix η η K) where
  carrier := {C | Commute C F ∧ Commute C T}
  zero_mem' := ⟨Commute.zero_left _,Commute.zero_left _⟩
  add_mem' := by
    rintro C D ⟨hCF,hCT⟩ ⟨hDF,hDT⟩
    exact ⟨hCF.add_left hDF,hCT.add_left hDT⟩
  smul_mem' := by
    rintro r C ⟨hCF,hCT⟩
    exact ⟨hCF.smul_left r,hCT.smul_left r⟩

/-- Reindex square matrices on a product into rectangles of local entries. -/
def regroup : Matrix (ι×κ) (ι×κ) K ≃ₗ[K] Matrix (ι×ι) (κ×κ) K where
  toFun M ij uv := M (ij.1,uv.1) (ij.2,uv.2)
  invFun M xu yv := M (xu.1,yv.1) (xu.2,yv.2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Identify ordinary local matrices with functions on their entry indices. -/
def entries {η : Type*} : Matrix η η K ≃ₗ[K] ((η×η) → K) where
  toFun M ij := M ij.1 ij.2
  invFun f i j := f (i,j)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def entrySpace {η : Type*} [Fintype η] [DecidableEq η] (F T : Matrix η η K) :=
  (pairSpace F T).map entries.toLinearMap

/-- Multiplication by a separate first-factor action acts on each local block. -/
theorem mul_left_entry (C : Matrix (ι×κ) (ι×κ) K) (F : Matrix ι ι K)
    (i j : ι) (u v : κ) :
    (C * kronecker F (1 : Matrix κ κ K)) (i,u) (j,v) =
      ∑ k, C (i,u) (k,v)*F k j := by
  simp [Matrix.mul_apply,Matrix.kronecker,Matrix.kroneckerMap_apply,
    Matrix.one_apply,Fintype.sum_prod_type,mul_ite]

theorem left_mul_entry (C : Matrix (ι×κ) (ι×κ) K) (F : Matrix ι ι K)
    (i j : ι) (u v : κ) :
    (kronecker F (1 : Matrix κ κ K) * C) (i,u) (j,v) =
      ∑ k, F i k*C (k,u) (j,v) := by
  simp [Matrix.mul_apply,Matrix.kronecker,Matrix.kroneckerMap_apply,
    Matrix.one_apply,Fintype.sum_prod_type,ite_mul]

theorem mul_right_entry (C : Matrix (ι×κ) (ι×κ) K) (G : Matrix κ κ K)
    (i j : ι) (u v : κ) :
    (C * kronecker (1 : Matrix ι ι K) G) (i,u) (j,v) =
      ∑ w, C (i,u) (j,w)*G w v := by
  simp [Matrix.mul_apply,Matrix.kronecker,Matrix.kroneckerMap_apply,
    Matrix.one_apply,Fintype.sum_prod_type,mul_ite,ite_mul]

theorem right_mul_entry (C : Matrix (ι×κ) (ι×κ) K) (G : Matrix κ κ K)
    (i j : ι) (u v : κ) :
    (kronecker (1 : Matrix ι ι K) G * C) (i,u) (j,v) =
      ∑ w, G u w*C (i,w) (j,v) := by
  simp [Matrix.mul_apply,Matrix.kronecker,Matrix.kroneckerMap_apply,
    Matrix.one_apply,Fintype.sum_prod_type,mul_ite,ite_mul]

def leftBlock (C : Matrix (ι×κ) (ι×κ) K) (u v : κ) : Matrix ι ι K :=
  fun i j => C (i,u) (j,v)
def rightBlock (C : Matrix (ι×κ) (ι×κ) K) (i j : ι) : Matrix κ κ K :=
  fun u v => C (i,u) (j,v)

theorem commute_left_iff (C : Matrix (ι×κ) (ι×κ) K) (F : Matrix ι ι K) :
    Commute C (kronecker F (1 : Matrix κ κ K)) ↔
      ∀ u v, Commute (leftBlock C u v) F := by
  constructor
  · intro h u v
    change leftBlock C u v*F=F*leftBlock C u v
    ext i j
    have he := congrFun (congrFun h.eq (i,u)) (j,v)
    rw [mul_left_entry,left_mul_entry] at he
    simpa only [Matrix.mul_apply,leftBlock] using he
  · intro h
    change C*kronecker F 1=kronecker F 1*C
    ext ⟨i,u⟩ ⟨j,v⟩
    rw [mul_left_entry,left_mul_entry]
    simpa only [Matrix.mul_apply,leftBlock] using
      congrFun (congrFun (h u v).eq i) j

theorem commute_right_iff (C : Matrix (ι×κ) (ι×κ) K) (G : Matrix κ κ K) :
    Commute C (kronecker (1 : Matrix ι ι K) G) ↔
      ∀ i j, Commute (rightBlock C i j) G := by
  constructor
  · intro h i j
    change rightBlock C i j*G=G*rightBlock C i j
    ext u v
    have he := congrFun (congrFun h.eq (i,u)) (j,v)
    rw [mul_right_entry,right_mul_entry] at he
    simpa only [Matrix.mul_apply,rightBlock] using he
  · intro h
    change C*kronecker 1 G=kronecker 1 G*C
    ext ⟨i,u⟩ ⟨j,v⟩
    rw [mul_right_entry,right_mul_entry]
    simpa only [Matrix.mul_apply,rightBlock] using
      congrFun (congrFun (h i j).eq u) v



 theorem entrySpace_mem {η : Type*} [Fintype η] [DecidableEq η]
    (F T : Matrix η η K) (f : (η×η) → K) :
    f ∈ entrySpace F T ↔ entries.symm f ∈ pairSpace F T := by
  constructor
  · rintro ⟨C,hC,he⟩
    change entries C=f at he
    rw [← he]
    simpa using hC
  · intro h
    exact ⟨entries.symm f,h,entries.apply_symm_apply f⟩

def fourSpace (FA TA : Matrix ι ι K) (FB TB : Matrix κ κ K) :=
  pairSpace (kronecker FA (1 : Matrix κ κ K)) (kronecker TA (1 : Matrix κ κ K)) ⊓
    pairSpace (kronecker (1 : Matrix ι ι K) FB) (kronecker (1 : Matrix ι ι K) TB)

theorem regroup_mem (FA TA : Matrix ι ι K) (FB TB : Matrix κ κ K)
    (C : Matrix (ι×κ) (ι×κ) K) :
    regroup C ∈ SeparatedDimension.separated (entrySpace FA TA) (entrySpace FB TB) ↔
      C ∈ fourSpace FA TA FB TB := by
  constructor
  · rintro ⟨hU,hV⟩
    have hL (u v : κ) : leftBlock C u v ∈ pairSpace FA TA :=
      (entrySpace_mem FA TA _).mp (hU (u,v))
    have hR (i j : ι) : rightBlock C i j ∈ pairSpace FB TB :=
      (entrySpace_mem FB TB _).mp (hV (i,j))
    exact ⟨⟨(commute_left_iff C FA).mpr (fun u v => (hL u v).1),
      (commute_left_iff C TA).mpr (fun u v => (hL u v).2)⟩,
      ⟨(commute_right_iff C FB).mpr (fun i j => (hR i j).1),
      (commute_right_iff C TB).mpr (fun i j => (hR i j).2)⟩⟩
  · rintro ⟨⟨hFA,hTA⟩,⟨hFB,hTB⟩⟩
    constructor
    · rintro ⟨u,v⟩
      apply (entrySpace_mem FA TA _).mpr
      exact ⟨(commute_left_iff C FA).mp hFA u v,(commute_left_iff C TA).mp hTA u v⟩
    · rintro ⟨i,j⟩
      apply (entrySpace_mem FB TB _).mpr
      exact ⟨(commute_right_iff C FB).mp hFB i j,(commute_right_iff C TB).mp hTB i j⟩

def regroupEquiv (FA TA : Matrix ι ι K) (FB TB : Matrix κ κ K) :
    fourSpace FA TA FB TB ≃ₗ[K]
      SeparatedDimension.separated (entrySpace FA TA) (entrySpace FB TB) where
  toFun C := ⟨regroup C,(regroup_mem FA TA FB TB C).mpr C.property⟩
  invFun M := ⟨regroup.symm M,(regroup_mem FA TA FB TB _).mp
    (by simpa using M.property)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finrank_entrySpace {η : Type*} [Fintype η] [DecidableEq η]
    (F T : Matrix η η K) :
    Module.finrank K (entrySpace F T) = Module.finrank K (pairSpace F T) := by
  exact LinearEquiv.finrank_map_eq entries (pairSpace F T)

/-- The simultaneous commutant of separate factor actions has product dimension. -/
theorem fourSpace_finrank (FA TA : Matrix ι ι K) (FB TB : Matrix κ κ K) :
    Module.finrank K (fourSpace FA TA FB TB) =
      Module.finrank K (pairSpace FA TA) * Module.finrank K (pairSpace FB TB) := by
  rw [(regroupEquiv FA TA FB TB).finrank_eq,
    SeparatedDimension.finrank_separated,finrank_entrySpace,finrank_entrySpace]

/-- A typed generator-separation packet now proves the full dimension product,
without an assumed basis or an assumed centralizer dimension. -/
theorem crt_finrank
    (d : WeilCRT.SeparationData (K:=K) (B:=Matrix (ι×κ) (ι×κ) K))
    (FA TA : Matrix ι ι K) (FB TB : Matrix κ κ K)
    (hFA : d.FA=kronecker FA (1 : Matrix κ κ K))
    (hTA : d.TA=kronecker TA (1 : Matrix κ κ K))
    (hFB : d.FB=kronecker (1 : Matrix ι ι K) FB)
    (hTB : d.TB=kronecker (1 : Matrix ι ι K) TB) :
    Module.finrank K (pairSpace d.F d.T) =
      Module.finrank K (pairSpace FA TA)*Module.finrank K (pairSpace FB TB) := by
  have he : pairSpace d.F d.T=fourSpace FA TA FB TB := by
    ext C
    change (Commute C d.F ∧ Commute C d.T) ↔
      ((Commute C (kronecker FA 1) ∧ Commute C (kronecker TA 1)) ∧
        (Commute C (kronecker 1 FB) ∧ Commute C (kronecker 1 TB)))
    rw [WeilCRT.commutant_separates d C,hFA,hTA,hFB,hTB]
    constructor
    · rintro ⟨h1,h2,h3,h4⟩; exact ⟨⟨h1,h3⟩,⟨h2,h4⟩⟩
    · rintro ⟨⟨h1,h3⟩,⟨h2,h4⟩⟩; exact ⟨h1,h2,h3,h4⟩
  rw [he,fourSpace_finrank]

end PerfectPower.CommutantDimension
