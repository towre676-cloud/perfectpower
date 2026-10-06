import PerfectPower.EllipticDivision
import PerfectPower.NativeRationalRoots

namespace PerfectPower.TypedDivisionPackets
open Polynomial

/-- Native root data. Completeness is derived, never a field supplied by a producer. -/
structure RationalPacket (f : Polynomial ℚ) where
  coefficients : List ℤ
  scale : ℚ
  scale_ne_zero : scale ≠ 0
  valid : NativePolynomialSquare.valid coefficients
  monic : (NativePolynomialSquare.polynomial coefficients).Monic
  scaling : (NativePolynomialSquare.polynomial coefficients).map (Int.castRingHom ℚ) =
    f.scaleRoots scale

noncomputable def RationalPacket.interpret {f : Polynomial ℚ} (p : RationalPacket f) : Finset ℚ :=
  NativeRationalRoots.roots p.coefficients p.scale

theorem RationalPacket.complete {f : Polynomial ℚ} (p : RationalPacket f) (x : ℚ) :
    f.eval x=0 ↔ x ∈ p.interpret :=
  NativeRationalRoots.complete f p.coefficients p.scale p.scale_ne_zero p.valid
    p.monic p.scaling x

variable {G : Type*} [AddCommGroup G]

/-- A typed local fibre; proof fields must be kernel-checked at the native boundary. -/
structure FibrePacket (n : ℤ) (P : G) where
  points : List G
  sound_complete : ∀ Q, n • Q=P ↔ Q ∈ points

/-- Compose every intermediate branch, retaining multiplicities and empty fibres. -/
def compose (m n : ℤ) (P : G) (outer : FibrePacket n P)
    (inner : ∀ H : G, H ∈ outer.points → FibrePacket m H) : List G :=
  outer.points.attach.flatMap (fun H => (inner H.1 H.2).points)

theorem compose_complete (m n : ℤ) (P : G) (outer : FibrePacket n P)
    (inner : ∀ H : G, H ∈ outer.points → FibrePacket m H) (Q : G) :
    (n*m) • Q=P ↔ Q ∈ compose m n P outer inner := by
  rw [compose, List.mem_flatMap]
  constructor
  · intro h
    have ho : m • Q ∈ outer.points := (outer.sound_complete _).mp (by
      simpa only [mul_smul] using h)
    exact ⟨⟨m • Q, ho⟩, List.mem_attach _ _, (inner _ ho).sound_complete Q |>.mp rfl⟩
  · rintro ⟨H, _, hQ⟩
    have hi := (inner H.1 H.2).sound_complete Q |>.mpr hQ
    rw [mul_smul, hi]
    exact (outer.sound_complete H.1).mpr H.2

end PerfectPower.TypedDivisionPackets
