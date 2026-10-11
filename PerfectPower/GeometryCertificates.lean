import Std
namespace PerfectPower.GeometryCertificates
abbrev Edge := Nat × Nat × Int
inductive Walk (edges : List Edge) : Nat → Nat → Int → Prop where
  | nil (u : Nat) : Walk edges u u 0
  | cons {u v t : Nat} {w c : Int} (edge : (u,v,w) ∈ edges)
      (tail : Walk edges v t c) : Walk edges u t (w+c)

theorem potential_lower_bound (edges : List Edge) (p : Nat → Int)
    (h : ∀ e ∈ edges, p e.2.1 ≤ p e.1 + e.2.2)
    {u v : Nat} {c : Int} (walk : Walk edges u v c) : p v ≤ p u + c := by
  induction walk with
  | nil => omega
  | @cons u v t w c edge tail ih =>
    have step := h (u,v,w) edge
    simp only at step
    omega

theorem optimal_walk (edges : List Edge) (p : Nat → Int)
    (h : ∀ e ∈ edges, p e.2.1 ≤ p e.1 + e.2.2)
    {s t : Nat} {cost : Int} (attained : cost = p t - p s)
    {other : Int} (walk : Walk edges s t other) : cost ≤ other := by
  have bound := potential_lower_bound edges p h walk
  omega

theorem closed_walk_endpoint (edges : List Edge) (r : Nat → Prop)
    (closed : ∀ e ∈ edges, r e.1 → r e.2.1)
    {u v : Nat} {c : Int} (walk : Walk edges u v c) (start : r u) : r v := by
  induction walk with
  | nil => exact start
  | @cons u v t w c edge tail ih => exact ih (closed (u,v,w) edge start)

theorem no_walk_outside (edges : List Edge) (r : Nat → Prop)
    (closed : ∀ e ∈ edges, r e.1 → r e.2.1)
    {s t : Nat} (hs : r s) (ht : ¬r t) : ∀ c, ¬Walk edges s t c := by
  intro c walk
  exact ht (closed_walk_endpoint edges r closed walk hs)

#print axioms optimal_walk
#print axioms no_walk_outside
end PerfectPower.GeometryCertificates

namespace PerfectPower.GeometryCertificates
abbrev Point := Int × Int
def side (a b p : Point) : Int :=
  (b.1-a.1)*(p.2-a.2)-(b.2-a.2)*(p.1-a.1)
def separated (first second : List Point) (a b : Point) (sign : Int) : Prop :=
  (sign = 1 ∨ sign = -1) ∧ a ≠ b ∧
  (∀ p ∈ first, 0 ≤ sign * side a b p) ∧
  (∀ p ∈ second, sign * side a b p ≤ 0)
instance (first second : List Point) (a b : Point) (sign : Int) :
    Decidable (separated first second a b sign) := by unfold separated; infer_instance

theorem opposite_strict_sides (a b p : Point) (sign : Int)
    (first : 0 < sign * side a b p) (second : sign * side a b p < 0) : False := by omega

def onSegment (p a b : Point) : Prop :=
  side a b p = 0 ∧ min a.1 b.1 ≤ p.1 ∧ p.1 ≤ max a.1 b.1 ∧
  min a.2 b.2 ≤ p.2 ∧ p.2 ≤ max a.2 b.2
instance (p a b : Point) : Decidable (onSegment p a b) := by unfold onSegment; infer_instance

def signedMultiplicity (atoms : List (Nat × Nat)) (u v : Nat) : Int :=
  Int.ofNat (atoms.count (u,v)) - Int.ofNat (atoms.count (v,u))
#print axioms opposite_strict_sides
end PerfectPower.GeometryCertificates

namespace PerfectPower.GeometryCertificates
/- Homogeneous coordinates clear rational barycentric denominators. -/
def numeratorSide (a b : Point) (x y d : Int) : Int :=
  (b.1-a.1)*(y-d*a.2)-(b.2-a.2)*(x-d*a.1)

theorem weighted_side (a b u v w : Point) (α β γ : Int) :
    numeratorSide a b (α*u.1+β*v.1+γ*w.1) (α*u.2+β*v.2+γ*w.2) (α+β+γ) =
    α*side a b u+β*side a b v+γ*side a b w := by
  simp only [numeratorSide,side,Int.add_mul,Int.mul_add,Int.sub_mul,Int.mul_sub]
  simp only [Int.mul_assoc,Int.mul_left_comm,Int.mul_comm]
  omega

theorem nonnegative_weighted_side (a b u v w : Point) (α β γ : Int)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (hu : 0 ≤ side a b u) (hv : 0 ≤ side a b v) (hw : 0 ≤ side a b w) :
    0 ≤ numeratorSide a b (α*u.1+β*v.1+γ*w.1) (α*u.2+β*v.2+γ*w.2) (α+β+γ) := by
  rw [weighted_side]
  have h1 := Int.mul_nonneg hα hu
  have h2 := Int.mul_nonneg hβ hv
  have h3 := Int.mul_nonneg hγ hw
  omega
#print axioms weighted_side
#print axioms nonnegative_weighted_side
end PerfectPower.GeometryCertificates

namespace PerfectPower.GeometryCertificates
/- Boundary atoms are computed from actual coordinates inside Lean. -/
def atomicLine (points : List Point) (a b : Point) : List (Nat × Nat) :=
  let cuts := points.filter (fun p => decide (onSegment p a b))
  let ordered := if a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2) then cuts else cuts.reverse
  let indices := ordered.map points.idxOf
  indices.zip indices.tail
end PerfectPower.GeometryCertificates
