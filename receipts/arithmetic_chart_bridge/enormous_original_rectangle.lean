import Mathlib.Data.Int.ModEq
import Mathlib.Tactic
import PerfectPower.RationalPowerAtlas
import PerfectPower.ResidueAtlas
import PerfectPower.ResidueAtlasIntersectionFactored
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Atlas_c778187a39c87bda
open PerfectPower.ResidueAtlas
def F (x y : ℤ) : ℤ := (-1) * (x)^0 * (y)^2 + (1) * (x)^1 * (y)^0
theorem prime_checked : Nat.Prime 5 := by norm_num
#print axioms prime_checked
def roots1 : Finset (ℤ × ℤ) := {(0,0), (1,1), (1,4), (4,2), (4,3)}
theorem periodic1 (x y : ℤ) : F x y % 5 = F (x % 5) (y % 5) % 5 := by
  change Int.ModEq 5 (F x y) (F (x % 5) (y % 5))
  have hx : Int.ModEq 5 x (x % 5) := (Int.mod_modEq x 5).symm
  have hy : Int.ModEq 5 y (y % 5) := (Int.mod_modEq y 5).symm
  unfold F
  exact ((((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 2 hy)).add (((Int.ModEq.refl (1)).mul (Int.ModEq.pow 1 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked1 : rootTable F 5 = roots1 := by decide +kernel
def atlas1 : AtlasPacket F 5 := ⟨by norm_num, roots1, checked1, periodic1⟩
theorem complete1 (x y : ℤ) : (x % 5,y % 5) ∈ roots1 ↔ F x y % 5 = 0 := atlas1.complete x y
#print axioms periodic1
#print axioms checked1
#print axioms complete1
def bounds : (ℤ × ℤ) × (ℤ × ℤ) := ((-5000000000000000000000000000000000000000,5000000000000000000000000000000000000000),(-10000000000000000000000000000000000000000,10000000000000000000000000000000000000000))
theorem count_checked : (candidates atlas1 bounds).card = 40000000000000000000000000000000000000006000000000000000000000000000000000000001 := by
  rw [card_candidates]; decide +kernel
#print axioms count_checked
theorem source_survives (x y : ℤ) (hF : F x y = 0) : (x % 5,y % 5) ∈ roots1 := atlas1.source_survives x y hF
#print axioms source_survives
end Atlas_c778187a39c87bda
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Atlas_0a2fac8369bbdd24
open PerfectPower.ResidueAtlas
def F (x y : ℤ) : ℤ := (-1) * (x)^0 * (y)^2 + (1) * (x)^1 * (y)^0
theorem prime_checked : Nat.Prime 3 := by norm_num
#print axioms prime_checked
def roots1 : Finset (ℤ × ℤ) := {(0,0), (1,1), (1,2)}
theorem periodic1 (x y : ℤ) : F x y % 3 = F (x % 3) (y % 3) % 3 := by
  change Int.ModEq 3 (F x y) (F (x % 3) (y % 3))
  have hx : Int.ModEq 3 x (x % 3) := (Int.mod_modEq x 3).symm
  have hy : Int.ModEq 3 y (y % 3) := (Int.mod_modEq y 3).symm
  unfold F
  exact ((((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 2 hy)).add (((Int.ModEq.refl (1)).mul (Int.ModEq.pow 1 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked1 : rootTable F 3 = roots1 := by decide +kernel
def atlas1 : AtlasPacket F 3 := ⟨by norm_num, roots1, checked1, periodic1⟩
theorem complete1 (x y : ℤ) : (x % 3,y % 3) ∈ roots1 ↔ F x y % 3 = 0 := atlas1.complete x y
#print axioms periodic1
#print axioms checked1
#print axioms complete1
def roots2 : Finset (ℤ × ℤ) := {(0,0), (0,3), (0,6), (1,1), (1,8), (4,2), (4,7), (7,4), (7,5)}
theorem periodic2 (x y : ℤ) : F x y % 9 = F (x % 9) (y % 9) % 9 := by
  change Int.ModEq 9 (F x y) (F (x % 9) (y % 9))
  have hx : Int.ModEq 9 x (x % 9) := (Int.mod_modEq x 9).symm
  have hy : Int.ModEq 9 y (y % 9) := (Int.mod_modEq y 9).symm
  unfold F
  exact ((((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 2 hy)).add (((Int.ModEq.refl (1)).mul (Int.ModEq.pow 1 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked2 : rootTable F 9 = roots2 := by decide +kernel
def atlas2 : AtlasPacket F 9 := ⟨by norm_num, roots2, checked2, periodic2⟩
theorem complete2 (x y : ℤ) : (x % 9,y % 9) ∈ roots2 ↔ F x y % 9 = 0 := atlas2.complete x y
#print axioms periodic2
#print axioms checked2
#print axioms complete2
def lift2_0R (u v : ℤ) : ℤ := (-1) * (u)^0 * (v)^2
theorem lift2_0_identity (u v : ℤ) : F (0+3*u) (0+3*v) =
    3*((0)+(1)*u+(0)*v)+3^2*lift2_0R u v := by unfold F lift2_0R; ring
def lift2_0 : LiftPacket F 3 3 0 0 := ⟨0,1,0,lift2_0R,lift2_0_identity⟩
theorem lift2_0_complete (u v : ℤ) : (3*3 : ℤ) ∣ F (0+3*u) (0+3*v) ↔
    (3 : ℤ) ∣ (0)+(1)*u+(0)*v := lift2_0.step (by norm_num) (by norm_num) u v
theorem lift2_0_children : childTable F 3 3 0 0 = {(0,0), (0,3), (0,6)} := by decide +kernel
#print axioms lift2_0_identity
#print axioms lift2_0_complete
#print axioms lift2_0_children
def lift2_1R (u v : ℤ) : ℤ := (-1) * (u)^0 * (v)^2
theorem lift2_1_identity (u v : ℤ) : F (1+3*u) (1+3*v) =
    3*((0)+(1)*u+(-2)*v)+3^2*lift2_1R u v := by unfold F lift2_1R; ring
def lift2_1 : LiftPacket F 3 3 1 1 := ⟨0,1,-2,lift2_1R,lift2_1_identity⟩
theorem lift2_1_complete (u v : ℤ) : (3*3 : ℤ) ∣ F (1+3*u) (1+3*v) ↔
    (3 : ℤ) ∣ (0)+(1)*u+(-2)*v := lift2_1.step (by norm_num) (by norm_num) u v
theorem lift2_1_children : childTable F 3 3 1 1 = {(1,1), (4,7), (7,4)} := by decide +kernel
#print axioms lift2_1_identity
#print axioms lift2_1_complete
#print axioms lift2_1_children
def lift2_2R (u v : ℤ) : ℤ := (-1) * (u)^0 * (v)^2
theorem lift2_2_identity (u v : ℤ) : F (1+3*u) (2+3*v) =
    3*((-1)+(1)*u+(-4)*v)+3^2*lift2_2R u v := by unfold F lift2_2R; ring
def lift2_2 : LiftPacket F 3 3 1 2 := ⟨-1,1,-4,lift2_2R,lift2_2_identity⟩
theorem lift2_2_complete (u v : ℤ) : (3*3 : ℤ) ∣ F (1+3*u) (2+3*v) ↔
    (3 : ℤ) ∣ (-1)+(1)*u+(-4)*v := lift2_2.step (by norm_num) (by norm_num) u v
theorem lift2_2_children : childTable F 3 3 1 2 = {(1,8), (4,2), (7,5)} := by decide +kernel
#print axioms lift2_2_identity
#print axioms lift2_2_complete
#print axioms lift2_2_children
def bounds : (ℤ × ℤ) × (ℤ × ℤ) := ((-5000000000000000000000000000000000000000,5000000000000000000000000000000000000000),(-10000000000000000000000000000000000000000,10000000000000000000000000000000000000000))
theorem count_checked : (candidates atlas2 bounds).card = 22222222222222222222222222222222222222225555555555555555555555555555555555555555 := by
  rw [card_candidates]; decide +kernel
#print axioms count_checked
theorem source_survives (x y : ℤ) (hF : F x y = 0) : (x % 9,y % 9) ∈ roots2 := atlas2.source_survives x y hF
#print axioms source_survives
end Atlas_0a2fac8369bbdd24
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Atlas_39589df76224318a
open PerfectPower.ResidueAtlas
def F (x y : ℤ) : ℤ := (-1) * (x)^0 * (y)^2 + (1) * (x)^1 * (y)^0
theorem prime_checked : Nat.Prime 2 := by norm_num
#print axioms prime_checked
def roots1 : Finset (ℤ × ℤ) := {(0,0), (1,1)}
theorem periodic1 (x y : ℤ) : F x y % 2 = F (x % 2) (y % 2) % 2 := by
  change Int.ModEq 2 (F x y) (F (x % 2) (y % 2))
  have hx : Int.ModEq 2 x (x % 2) := (Int.mod_modEq x 2).symm
  have hy : Int.ModEq 2 y (y % 2) := (Int.mod_modEq y 2).symm
  unfold F
  exact ((((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 2 hy)).add (((Int.ModEq.refl (1)).mul (Int.ModEq.pow 1 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked1 : rootTable F 2 = roots1 := by decide +kernel
def atlas1 : AtlasPacket F 2 := ⟨by norm_num, roots1, checked1, periodic1⟩
theorem complete1 (x y : ℤ) : (x % 2,y % 2) ∈ roots1 ↔ F x y % 2 = 0 := atlas1.complete x y
#print axioms periodic1
#print axioms checked1
#print axioms complete1
def roots2 : Finset (ℤ × ℤ) := {(0,0), (0,2), (1,1), (1,3)}
theorem periodic2 (x y : ℤ) : F x y % 4 = F (x % 4) (y % 4) % 4 := by
  change Int.ModEq 4 (F x y) (F (x % 4) (y % 4))
  have hx : Int.ModEq 4 x (x % 4) := (Int.mod_modEq x 4).symm
  have hy : Int.ModEq 4 y (y % 4) := (Int.mod_modEq y 4).symm
  unfold F
  exact ((((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 2 hy)).add (((Int.ModEq.refl (1)).mul (Int.ModEq.pow 1 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked2 : rootTable F 4 = roots2 := by decide +kernel
def atlas2 : AtlasPacket F 4 := ⟨by norm_num, roots2, checked2, periodic2⟩
theorem complete2 (x y : ℤ) : (x % 4,y % 4) ∈ roots2 ↔ F x y % 4 = 0 := atlas2.complete x y
#print axioms periodic2
#print axioms checked2
#print axioms complete2
def lift2_0R (u v : ℤ) : ℤ := (-1) * (u)^0 * (v)^2
theorem lift2_0_identity (u v : ℤ) : F (0+2*u) (0+2*v) =
    2*((0)+(1)*u+(0)*v)+2^2*lift2_0R u v := by unfold F lift2_0R; ring
def lift2_0 : LiftPacket F 2 2 0 0 := ⟨0,1,0,lift2_0R,lift2_0_identity⟩
theorem lift2_0_complete (u v : ℤ) : (2*2 : ℤ) ∣ F (0+2*u) (0+2*v) ↔
    (2 : ℤ) ∣ (0)+(1)*u+(0)*v := lift2_0.step (by norm_num) (by norm_num) u v
theorem lift2_0_children : childTable F 2 2 0 0 = {(0,0), (0,2)} := by decide +kernel
#print axioms lift2_0_identity
#print axioms lift2_0_complete
#print axioms lift2_0_children
def lift2_1R (u v : ℤ) : ℤ := (-1) * (u)^0 * (v)^2
theorem lift2_1_identity (u v : ℤ) : F (1+2*u) (1+2*v) =
    2*((0)+(1)*u+(-2)*v)+2^2*lift2_1R u v := by unfold F lift2_1R; ring
def lift2_1 : LiftPacket F 2 2 1 1 := ⟨0,1,-2,lift2_1R,lift2_1_identity⟩
theorem lift2_1_complete (u v : ℤ) : (2*2 : ℤ) ∣ F (1+2*u) (1+2*v) ↔
    (2 : ℤ) ∣ (0)+(1)*u+(-2)*v := lift2_1.step (by norm_num) (by norm_num) u v
theorem lift2_1_children : childTable F 2 2 1 1 = {(1,1), (1,3)} := by decide +kernel
#print axioms lift2_1_identity
#print axioms lift2_1_complete
#print axioms lift2_1_children
def roots3 : Finset (ℤ × ℤ) := {(0,0), (0,4), (1,1), (1,3), (1,5), (1,7), (4,2), (4,6)}
theorem periodic3 (x y : ℤ) : F x y % 8 = F (x % 8) (y % 8) % 8 := by
  change Int.ModEq 8 (F x y) (F (x % 8) (y % 8))
  have hx : Int.ModEq 8 x (x % 8) := (Int.mod_modEq x 8).symm
  have hy : Int.ModEq 8 y (y % 8) := (Int.mod_modEq y 8).symm
  unfold F
  exact ((((Int.ModEq.refl (-1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 2 hy)).add (((Int.ModEq.refl (1)).mul (Int.ModEq.pow 1 hx)).mul (Int.ModEq.pow 0 hy)))
theorem checked3 : rootTable F 8 = roots3 := by decide +kernel
def atlas3 : AtlasPacket F 8 := ⟨by norm_num, roots3, checked3, periodic3⟩
theorem complete3 (x y : ℤ) : (x % 8,y % 8) ∈ roots3 ↔ F x y % 8 = 0 := atlas3.complete x y
#print axioms periodic3
#print axioms checked3
#print axioms complete3
def lift3_0R (u v : ℤ) : ℤ := (-1) * (u)^0 * (v)^2
theorem lift3_0_identity (u v : ℤ) : F (0+4*u) (0+4*v) =
    4*((0)+(1)*u+(0)*v)+4^2*lift3_0R u v := by unfold F lift3_0R; ring
def lift3_0 : LiftPacket F 2 4 0 0 := ⟨0,1,0,lift3_0R,lift3_0_identity⟩
theorem lift3_0_complete (u v : ℤ) : (4*2 : ℤ) ∣ F (0+4*u) (0+4*v) ↔
    (2 : ℤ) ∣ (0)+(1)*u+(0)*v := lift3_0.step (by norm_num) (by norm_num) u v
theorem lift3_0_children : childTable F 2 4 0 0 = {(0,0), (0,4)} := by decide +kernel
#print axioms lift3_0_identity
#print axioms lift3_0_complete
#print axioms lift3_0_children
def lift3_1R (u v : ℤ) : ℤ := (-1) * (u)^0 * (v)^2
theorem lift3_1_identity (u v : ℤ) : F (0+4*u) (2+4*v) =
    4*((-1)+(1)*u+(-4)*v)+4^2*lift3_1R u v := by unfold F lift3_1R; ring
def lift3_1 : LiftPacket F 2 4 0 2 := ⟨-1,1,-4,lift3_1R,lift3_1_identity⟩
theorem lift3_1_complete (u v : ℤ) : (4*2 : ℤ) ∣ F (0+4*u) (2+4*v) ↔
    (2 : ℤ) ∣ (-1)+(1)*u+(-4)*v := lift3_1.step (by norm_num) (by norm_num) u v
theorem lift3_1_children : childTable F 2 4 0 2 = {(4,2), (4,6)} := by decide +kernel
#print axioms lift3_1_identity
#print axioms lift3_1_complete
#print axioms lift3_1_children
def lift3_2R (u v : ℤ) : ℤ := (-1) * (u)^0 * (v)^2
theorem lift3_2_identity (u v : ℤ) : F (1+4*u) (1+4*v) =
    4*((0)+(1)*u+(-2)*v)+4^2*lift3_2R u v := by unfold F lift3_2R; ring
def lift3_2 : LiftPacket F 2 4 1 1 := ⟨0,1,-2,lift3_2R,lift3_2_identity⟩
theorem lift3_2_complete (u v : ℤ) : (4*2 : ℤ) ∣ F (1+4*u) (1+4*v) ↔
    (2 : ℤ) ∣ (0)+(1)*u+(-2)*v := lift3_2.step (by norm_num) (by norm_num) u v
theorem lift3_2_children : childTable F 2 4 1 1 = {(1,1), (1,5)} := by decide +kernel
#print axioms lift3_2_identity
#print axioms lift3_2_complete
#print axioms lift3_2_children
def lift3_3R (u v : ℤ) : ℤ := (-1) * (u)^0 * (v)^2
theorem lift3_3_identity (u v : ℤ) : F (1+4*u) (3+4*v) =
    4*((-2)+(1)*u+(-6)*v)+4^2*lift3_3R u v := by unfold F lift3_3R; ring
def lift3_3 : LiftPacket F 2 4 1 3 := ⟨-2,1,-6,lift3_3R,lift3_3_identity⟩
theorem lift3_3_complete (u v : ℤ) : (4*2 : ℤ) ∣ F (1+4*u) (3+4*v) ↔
    (2 : ℤ) ∣ (-2)+(1)*u+(-6)*v := lift3_3.step (by norm_num) (by norm_num) u v
theorem lift3_3_children : childTable F 2 4 1 3 = {(1,3), (1,7)} := by decide +kernel
#print axioms lift3_3_identity
#print axioms lift3_3_complete
#print axioms lift3_3_children
def bounds : (ℤ × ℤ) × (ℤ × ℤ) := ((-5000000000000000000000000000000000000000,5000000000000000000000000000000000000000),(-10000000000000000000000000000000000000000,10000000000000000000000000000000000000000))
theorem count_checked : (candidates atlas3 bounds).card = 25000000000000000000000000000000000000006250000000000000000000000000000000000001 := by
  rw [card_candidates]; decide +kernel
#print axioms count_checked
theorem source_survives (x y : ℤ) (hF : F x y = 0) : (x % 8,y % 8) ∈ roots3 := atlas3.source_survives x y hF
#print axioms source_survives
end Atlas_39589df76224318a
namespace Intersection_12673ce8f8550a3b
open PerfectPower.ResidueAtlasIntersectionFactored
open PerfectPower.ResidueAtlas (Bounds)
def local0 : CoverPacket (fun x y => Atlas_c778187a39c87bda.F x y % 5 = 0) 5 := ofAtlas Atlas_c778187a39c87bda.atlas1
def local1 : CoverPacket (fun x y => Atlas_0a2fac8369bbdd24.F x y % 9 = 0) 9 := ofAtlas Atlas_0a2fac8369bbdd24.atlas2
def local2 : CoverPacket (fun x y => Atlas_39589df76224318a.F x y % 8 = 0) 8 := ofAtlas Atlas_39589df76224318a.atlas3
def group0_0 : CoverPacket (fun x y => Atlas_39589df76224318a.F x y % 8 = 0) 8 := local2
theorem group_roots0 : group0_0.roots = {(0,0), (0,4), (1,1), (1,3), (1,5), (1,7), (4,2), (4,6)} := by decide +kernel
#print axioms group_roots0
def group1_0 : CoverPacket (fun x y => Atlas_0a2fac8369bbdd24.F x y % 9 = 0) 9 := local1
theorem group_roots1 : group1_0.roots = {(0,0), (0,3), (0,6), (1,1), (1,8), (4,2), (4,7), (7,4), (7,5)} := by decide +kernel
#print axioms group_roots1
def group2_0 : CoverPacket (fun x y => Atlas_c778187a39c87bda.F x y % 5 = 0) 5 := local0
theorem group_roots2 : group2_0.roots = {(0,0), (1,1), (1,4), (4,2), (4,3)} := by decide +kernel
#print axioms group_roots2
def stage0 : CoverPacket (fun x y => Atlas_39589df76224318a.F x y % 8 = 0) 8 := group0_0
theorem coprime1 : (8 : ℤ).natAbs.Coprime (9 : ℤ).natAbs := by decide +kernel
theorem bezout1 : (8 : ℤ)*8+(-7)*9=1 := by decide +kernel
def stage1 : CoverPacket (fun x y => (Atlas_39589df76224318a.F x y % 8 = 0) ∧ (Atlas_0a2fac8369bbdd24.F x y % 9 = 0)) 72 := merge stage0 group1_0 8 (-7) coprime1 bezout1
#print axioms coprime1
#print axioms bezout1
theorem coprime2 : (72 : ℤ).natAbs.Coprime (5 : ℤ).natAbs := by decide +kernel
theorem bezout2 : (3 : ℤ)*72+(-43)*5=1 := by decide +kernel
def stage2 : CoverPacket (fun x y => ((Atlas_39589df76224318a.F x y % 8 = 0) ∧ (Atlas_0a2fac8369bbdd24.F x y % 9 = 0)) ∧ (Atlas_c778187a39c87bda.F x y % 5 = 0)) 360 := merge stage1 group2_0 3 (-43) coprime2 bezout2
#print axioms coprime2
#print axioms bezout2
def bounds : Bounds := ((-5000000000000000000000000000000000000000,5000000000000000000000000000000000000000),(-10000000000000000000000000000000000000000,10000000000000000000000000000000000000000))
def S (x y : ℤ) : Prop := Atlas_c778187a39c87bda.F x y = 0 ∧ Atlas_0a2fac8369bbdd24.F x y = 0 ∧ Atlas_39589df76224318a.F x y = 0
instance : DecidablePred (fun z : ℤ × ℤ => S z.1 z.2) := fun z => by unfold S; infer_instance
theorem complete (x y : ℤ) : (x % 360,y % 360) ∈ stage2.roots ↔ ((Atlas_39589df76224318a.F x y % 8 = 0) ∧ (Atlas_0a2fac8369bbdd24.F x y % 9 = 0)) ∧ (Atlas_c778187a39c87bda.F x y % 5 = 0) := stage2.complete x y
theorem roots_count : stage2.roots.card = 360 := by decide +kernel
theorem count_checked : (candidates stage2 bounds).card = 555555555555555555555555555555555555554583333333333333333333333333333333333333 := by rw [card_candidates]; decide +kernel
theorem source_implies (x y : ℤ) (h : S x y) : ((Atlas_39589df76224318a.F x y % 8 = 0) ∧ (Atlas_0a2fac8369bbdd24.F x y % 9 = 0)) ∧ (Atlas_c778187a39c87bda.F x y % 5 = 0) := by
  simp only [S] at h
  rcases h with ⟨h0,h1,h2⟩
  simp only [h0, h1, h2, Int.zero_emod, and_self]
theorem source_survives (x y : ℤ) (h : S x y) : (x % 360,y % 360) ∈ stage2.roots := (stage2.complete x y).mpr (source_implies x y h)
#print axioms complete
#print axioms roots_count
#print axioms count_checked
#print axioms source_implies
#print axioms source_survives
end Intersection_12673ce8f8550a3b
namespace PowerCharts_025a8b2bfc6408fb
open PerfectPower.RationalPowerAtlas
open PerfectPower.ResidueAtlas (Bounds)
def F (x y : ℤ) : ℤ := (-2) * (x)^0 * (y)^2 + (1) * (x)^1 * (y)^0
def bounds : Bounds := ((-10000000000000000000000000000000000000000,10000000000000000000000000000000000000000),(-10000000000000000000000000000000000000000,10000000000000000000000000000000000000000))
def G0 (n y : ℤ) : ℤ := (-1) * (n)^0 * (y)^2 + (1) * (n)^1 * (y)^0
theorem identity0 (n y : ℤ) : F (0+2*n) y=2*G0 n y := by unfold F G0; ring
def chart0 : ChartPacket F G0 2 0 := ⟨by norm_num,identity0⟩
theorem source_transport0 (n y : ℤ) : F (0+2*n) y=0 ↔ G0 n y=0 := chart0.source_iff n y
theorem denominator_transport0 (m n y : ℤ) : 2*m ∣ F (0+2*n) y ↔ m ∣ G0 n y := chart0.congruence_iff m n y
def candidates0 := chartCandidates Intersection_12673ce8f8550a3b.stage2 bounds 2 0
theorem count0 : candidates0.card=555555555555555555555555555555555555554583333333333333333333333333333333333333 := by
  rw [candidates0,chart_count Intersection_12673ce8f8550a3b.stage2 bounds 2 0 (by norm_num)]; decide +kernel
#print axioms identity0
#print axioms source_transport0
#print axioms denominator_transport0
#print axioms count0
def residue (i : Fin 1) : ℤ := 0
def P (i : Fin 1) (x y : ℤ) : Prop := (((Atlas_39589df76224318a.F x y % 8 = 0) ∧ (Atlas_0a2fac8369bbdd24.F x y % 9 = 0)) ∧ (Atlas_c778187a39c87bda.F x y % 5 = 0))
def cover : (i : Fin 1) → PerfectPower.ResidueAtlasIntersectionFactored.CoverPacket (P i) 360 := Fin.cases Intersection_12673ce8f8550a3b.stage2 ((fun i => Fin.elim0 i))
theorem residue_canonical : ∀ i : Fin 1, 0≤residue i ∧ residue i<2 := by decide +kernel
theorem residue_injective : Function.Injective residue := by decide +kernel
def allCandidates := familyCandidates cover bounds 2 residue
theorem population_checked : allCandidates.card=555555555555555555555555555555555555554583333333333333333333333333333333333333 := by
  rw [allCandidates,family_count cover bounds 2 residue (by norm_num) residue_canonical residue_injective]; decide +kernel
#print axioms residue_canonical
#print axioms residue_injective
#print axioms population_checked
end PowerCharts_025a8b2bfc6408fb
