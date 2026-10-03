import PerfectPower.NativeCubicNorm
import PerfectPower.RankOne

/-! An integral basis bridge for shifted negative-monic binary cubics. -/
namespace PerfectPower.NativeCubicBridge
open NativeCubic

def embed (P h : ℤ) (x : Triple) : UnitBox.Z3 :=
  (x.1-h*x.2.1+(h^2-P)*x.2.2,x.2.1+h*x.2.2,x.2.2)
def inverse (P h : ℤ) (y : UnitBox.Z3) : Triple :=
  (y.1+h*y.2.1+(P-2*h^2)*y.2.2,y.2.1-h*y.2.2,y.2.2)

theorem inverse_embed (P h : ℤ) (x : Triple) : inverse P h (embed P h x) = x := by
  obtain ⟨a,b,c⟩ := x
  apply Prod.ext
  · simp only [inverse,embed]; ring
  · apply Prod.ext <;> simp only [inverse,embed] <;> ring

theorem embed_inverse (P h : ℤ) (y : UnitBox.Z3) : embed P h (inverse P h y) = y := by
  obtain ⟨a,b,c⟩ := y
  apply Prod.ext
  · simp only [inverse,embed]; ring
  · apply Prod.ext <;> simp only [inverse,embed] <;> ring

theorem embed_mul (P Q h : ℤ) (x y : Triple) :
    embed P h (NativeCubic.mul (-1) (-3*h) (P-3*h^2) (Q+P*h-h^3) x y) =
      UnitBox.mul P Q (embed P h x) (embed P h y) := by
  obtain ⟨a,b,c⟩ := x
  obtain ⟨d,e,f⟩ := y
  apply Prod.ext
  · simp only [embed,NativeCubic.mul,UnitBox.mul]; ring
  · apply Prod.ext <;> simp only [embed,NativeCubic.mul,UnitBox.mul] <;> ring

theorem norm_embed (P Q h : ℤ) (x : Triple) :
    NativeCubic.norm (-1) (-3*h) (P-3*h^2) (Q+P*h-h^3) x =
      UnitPremises.nrm P Q (embed P h x) := by
  obtain ⟨a,b,c⟩ := x
  unfold NativeCubic.norm
  rw [Matrix.det_fin_three]
  simp [NativeCubic.Mx,NativeCubic.basis,NativeCubic.mul,UnitPremises.nrm,embed]
  ring
end PerfectPower.NativeCubicBridge
