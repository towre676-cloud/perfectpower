import PerfectPower.CommutantDimension

/-!
The algebraic end of the orbit-reflection argument. No all-level orbit
classification is assumed to have been formalized: the spanning hypothesis
below is explicit. Transpose is linear and reverses multiplication, so a
matrix algebra spanned by transpose-fixed orbit sums is commutative.
-/
noncomputable section
namespace PerfectPower.WeilOrbitSymmetry
open scoped BigOperators
open Matrix PerfectPower.CommutantDimension
variable {K ι Ω : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- Symmetric matrices form a vector space, but generally not a subalgebra. -/
def symmetricSpace : Submodule K (Matrix ι ι K) where
  carrier := {C | C.transpose = C}
  zero_mem' := by simp
  add_mem' := by
    intro C D hC hD
    change (C+D).transpose=C+D
    rw [transpose_add,hC,hD]
  smul_mem' := by
    intro a C hC
    change (a • C).transpose=a • C
    rw [transpose_smul,hC]

theorem pairSpace_mul_mem (F T C D : Matrix ι ι K)
    (hC : C ∈ pairSpace F T) (hD : D ∈ pairSpace F T) :
    C*D ∈ pairSpace F T :=
  ⟨hC.1.mul_left hD.1,hC.2.mul_left hD.2⟩

omit [DecidableEq ι] in
theorem symmetric_product_iff_commute (C D : Matrix ι ι K)
    (hC : C.transpose=C) (hD : D.transpose=D) :
    (C*D).transpose=C*D ↔ Commute C D := by
  rw [transpose_mul,hC,hD]
  exact ⟨fun h => h.symm,fun h => h.eq.symm⟩

theorem commutative_of_symmetric (F T : Matrix ι ι K)
    (hs : pairSpace F T ≤ symmetricSpace) (C D : Matrix ι ι K)
    (hC : C ∈ pairSpace F T) (hD : D ∈ pairSpace F T) : Commute C D := by
  exact (symmetric_product_iff_commute C D (hs hC) (hs hD)).mp
    (hs (pairSpace_mul_mem F T C D hC hD))

omit [Fintype ι] [DecidableEq ι] in
/-- A finite orbit sum is transpose-fixed when reflection permutes its terms. -/
theorem orbit_sum_symmetric [Fintype Ω] (r : Ω ≃ Ω)
    (B : Ω → Matrix ι ι K) (hr : ∀ w, (B w).transpose=B (r w)) :
    (∑ w, B w).transpose=∑ w, B w := by
  rw [transpose_sum]
  simp_rw [hr]
  exact r.sum_comp B

omit [Fintype ι] [DecidableEq ι] in
theorem span_symmetric (B : Ω → Matrix ι ι K)
    (hB : ∀ w, (B w).transpose=B w) :
    Submodule.span K (Set.range B) ≤ symmetricSpace := by
  apply Submodule.span_le.mpr
  rintro C ⟨w,rfl⟩
  exact hB w

/-- The only remaining hypothesis is that the supplied orbit sums span. -/
theorem commutative_of_orbit_span (F T : Matrix ι ι K)
    (B : Ω → Matrix ι ι K) (hB : ∀ w, (B w).transpose=B w)
    (hspan : pairSpace F T ≤ Submodule.span K (Set.range B))
    (C D : Matrix ι ι K) (hC : C ∈ pairSpace F T)
    (hD : D ∈ pairSpace F T) : Commute C D :=
  commutative_of_symmetric F T (hspan.trans (span_symmetric B hB)) C D hC hD

section Gauge
variable {A : Type*} [CommRing A]

theorem odd_chirp_gauge (h s t : A) (hh : 2*h=1) :
    -h*s*(t+2*s) = -h*s*t-s*s := by
  calc
    -h*s*(t+2*s) = -h*s*t-(2*h)*(s*s) := by ring
    _ = -h*s*t-s*s := by rw [hh]; ring

theorem odd_fourier_gauge (h s t : A) (hh : 2*h=1) :
    -h*(-t)*s = -h*s*t+s*t := by
  have hphase : (2*h)*(s*t)=s*t := by rw [hh]; ring
  linear_combination hphase

theorem odd_transpose_gauge (h s t : A) (hh : 2*h=1) :
    -h*s*t+s*t = -h*(-s)*t := by
  have hphase : (2*h)*(s*t)=s*t := by rw [hh]; ring
  linear_combination -hphase

/-- For even indices s=2u,t=2v the exponent -st/2 is -2uv. -/
theorem even_chirp_gauge (u v : A) :
    -2*u*(v+2*u) = -2*u*v-(2*u)*(2*u) := by ring

theorem even_fourier_gauge (u v : A) :
    -2*(-v)*u = -2*u*v+(2*u)*(2*v) := by ring

theorem even_transpose_gauge (u v : A) :
    -2*u*v+(2*u)*(2*v) = -2*(-u)*v := by ring
end Gauge
end PerfectPower.WeilOrbitSymmetry
