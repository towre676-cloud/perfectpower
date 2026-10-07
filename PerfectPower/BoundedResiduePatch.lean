import Mathlib.Data.Int.Interval
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic

/-! Complete finite boxes, smooth first lifts, and auxiliary relations on every
integer solution in a declared box and residue class. No height bound assumed. -/
namespace PerfectPower.BoundedResiduePatch
open scoped BigOperators

def residueValues (lo hi p r : ℤ) : Finset ℤ :=
  (Finset.Icc lo hi).filter fun x => p ∣ x-r

def coarse (bounds : (ℤ × ℤ) × (ℤ × ℤ)) (p : ℤ) (a b : ℤ) : Finset (ℤ × ℤ) :=
  (residueValues bounds.1.1 bounds.1.2 p a).product
    (residueValues bounds.2.1 bounds.2.2 p b)

def lifts (F : ℤ → ℤ → ℤ) (bounds : (ℤ × ℤ) × (ℤ × ℤ))
    (p a b : ℤ) : Finset (ℤ × ℤ) :=
  (coarse bounds p a b).filter fun z => p^2 ∣ F z.1 z.2

def solutions (F : ℤ → ℤ → ℤ) (bounds : (ℤ × ℤ) × (ℤ × ℤ))
    (p a b : ℤ) : Finset (ℤ × ℤ) :=
  (lifts F bounds p a b).filter fun z => F z.1 z.2 = 0

theorem residueValues_complete (lo hi p r x : ℤ) :
    x ∈ residueValues lo hi p r ↔ lo ≤ x ∧ x ≤ hi ∧ p ∣ x-r := by
  simp [residueValues, and_assoc]

theorem solutions_complete (F : ℤ → ℤ → ℤ) (bounds : (ℤ × ℤ) × (ℤ × ℤ))
    (p a b x y : ℤ) :
    (x,y) ∈ solutions F bounds p a b ↔
      bounds.1.1 ≤ x ∧ x ≤ bounds.1.2 ∧ bounds.2.1 ≤ y ∧ y ≤ bounds.2.2 ∧
      p ∣ x-a ∧ p ∣ y-b ∧ F x y = 0 := by
  simp only [solutions, lifts, coarse, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product,
    Prod.fst, Prod.snd, residueValues_complete]
  constructor
  · rintro ⟨⟨⟨⟨hx0,hx1,hxp⟩,⟨hy0,hy1,hyp⟩⟩,_⟩,hF⟩
    exact ⟨hx0,hx1,hy0,hy1,hxp,hyp,hF⟩
  · rintro ⟨hx0,hx1,hy0,hy1,hxp,hyp,hF⟩
    exact ⟨⟨⟨⟨hx0,hx1,hxp⟩,⟨hy0,hy1,hyp⟩⟩,hF ▸ dvd_zero _⟩,hF⟩

/-- A literal equality is the complete covering obligation. -/
structure CoverPacket (F : ℤ → ℤ → ℤ) (bounds : (ℤ × ℤ) × (ℤ × ℤ)) (p a b : ℤ) where
  points : Finset (ℤ × ℤ)
  checked : solutions F bounds p a b = points

theorem CoverPacket.complete {F bounds p a b} (packet : CoverPacket F bounds p a b)
    (x y : ℤ) : (x,y) ∈ packet.points ↔
      bounds.1.1 ≤ x ∧ x ≤ bounds.1.2 ∧ bounds.2.1 ≤ y ∧ y ≤ bounds.2.2 ∧
      p ∣ x-a ∧ p ∣ y-b ∧ F x y = 0 := by
  rw [← packet.checked]
  exact solutions_complete F bounds p a b x y

theorem relation_on_box {F bounds p a b} (packet : CoverPacket F bounds p a b)
    (R : ℤ → ℤ → ℤ) (hR : ∀ z ∈ packet.points, R z.1 z.2 = 0)
    (x y : ℤ) (hx0 : bounds.1.1 ≤ x) (hx1 : x ≤ bounds.1.2)
    (hy0 : bounds.2.1 ≤ y) (hy1 : y ≤ bounds.2.2)
    (hxp : p ∣ x-a) (hyp : p ∣ y-b) (hF : F x y = 0) : R x y = 0 :=
  hR (x,y) ((packet.complete x y).mpr ⟨hx0,hx1,hy0,hy1,hxp,hyp,hF⟩)

theorem empty_box {F bounds p a b} (packet : CoverPacket F bounds p a b)
    (hempty : packet.points = ∅) (x y : ℤ)
    (hx0 : bounds.1.1 ≤ x) (hx1 : x ≤ bounds.1.2)
    (hy0 : bounds.2.1 ≤ y) (hy1 : y ≤ bounds.2.2)
    (hxp : p ∣ x-a) (hyp : p ∣ y-b) : F x y ≠ 0 := by
  intro hF
  have hm := (packet.complete x y).mpr ⟨hx0,hx1,hy0,hy1,hxp,hyp,hF⟩
  rw [hempty] at hm
  exact Finset.notMem_empty _ hm

/-- The exact polynomial identity binds local expansion to original coordinates. -/
structure TaylorPacket (F : ℤ → ℤ → ℤ) (p a b : ℤ) where
  constant : ℤ
  dx : ℤ
  dy : ℤ
  remainder : ℤ → ℤ → ℤ
  identity : ∀ u v, F (a+p*u) (b+p*v) =
    p*(constant+dx*u+dy*v) + p^2*remainder u v
  vertical_unit : IsCoprime p dy

theorem TaylorPacket.first_lift {F p a b} (packet : TaylorPacket F p a b)
    (hp : p ≠ 0) (u v : ℤ) :
    p^2 ∣ F (a+p*u) (b+p*v) ↔ p ∣ packet.constant+packet.dx*u+packet.dy*v := by
  rw [packet.identity]
  have he : p*(packet.constant+packet.dx*u+packet.dy*v) + p^2*packet.remainder u v =
      p*(packet.constant+packet.dx*u+packet.dy*v+p*packet.remainder u v) := by ring
  rw [he, pow_two, mul_dvd_mul_iff_left hp]
  constructor
  · intro h
    have hs := dvd_sub h (dvd_mul_right p (packet.remainder u v))
    simpa using hs
  · intro h
    exact dvd_add h (dvd_mul_right p (packet.remainder u v))

theorem TaylorPacket.vertical_unique {F p a b} (packet : TaylorPacket F p a b)
    (u v w : ℤ)
    (hv : p ∣ packet.constant+packet.dx*u+packet.dy*v)
    (hw : p ∣ packet.constant+packet.dx*u+packet.dy*w) : p ∣ v-w := by
  apply packet.vertical_unit.dvd_of_dvd_mul_left
  have h := dvd_sub hv hw
  convert h using 1 <;> ring

end PerfectPower.BoundedResiduePatch
