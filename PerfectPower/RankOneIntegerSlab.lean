import PerfectPower.RankOne
import Mathlib.Data.Rat.Floor

/-! Clear the fixed certificate denominators without changing any slab endpoint. -/
namespace PerfectPower.RankOneIntegerSlab
open UnitBox UnitPremises RankOne UnitGenProof

structure Scaled where
  d : ℕ
  lo : ℤ
  hi : ℤ
  j : ℤ
  tlo : ℤ
  thi : ℤ

def Matches (c : Cert) (s : Scaled) : Prop :=
  0 < s.d ∧ c.lo = s.lo / (s.d : ℚ) ∧ c.hi = s.hi / (s.d : ℚ) ∧
  c.J = s.j / (s.d : ℚ) ∧ c.t2lo = s.tlo / (s.d : ℚ) ∧ c.T^2 = s.thi / (s.d : ℚ)

def intsFrac (d : ℕ) (lo hi : ℤ) : List ℤ :=
  let first := -((-lo) / (d : ℤ))
  (List.range ((hi / (d : ℤ) - first + 1).toNat)).map fun i : ℕ => first + (i : ℤ)

def low (x lo hi : ℤ) : ℤ := if 0 ≤ x then x*lo else x*hi
def high (x lo hi : ℤ) : ℤ := if 0 ≤ x then x*hi else x*lo

def bRange (s : Scaled) (cc : ℤ) : List ℤ :=
  intsFrac s.d (low cc s.lo s.hi-s.j) (high cc s.lo s.hi+s.j)
def aRange (P : ℤ) (s : Scaled) (b cc : ℤ) : List ℤ :=
  intsFrac (2*s.d)
    (-2*(s.d : ℤ)+low b s.lo s.hi-2*(s.d : ℤ)*cc*P+low cc s.tlo s.thi)
    (2*(s.d : ℤ)+high b s.lo s.hi-2*(s.d : ℤ)*cc*P+high cc s.tlo s.thi)

def slice (P Q : ℤ) (η : Z3) (c : Cert) (s : Scaled) (l : ℕ) : Bool :=
  (bRange s ((l : ℤ)-c.C)).all fun b => (aRange P s b ((l : ℤ)-c.C)).all fun a =>
    let g : Z3 := (a,b,(l : ℤ)-c.C)
    decide (nrm P Q g ≠ 1 ∧ nrm P Q g ≠ -1) ||
      decide (g ∈ [(1,0,0),(-1,0,0),η,UnitBox.neg η]) || decide (pHi g c.lo c.hi < 1)

theorem intsFrac_eq (d : ℕ) (lo hi : ℤ) :
    ints ((lo : ℚ)/(d : ℚ)) ((hi : ℚ)/(d : ℚ)) = intsFrac d lo hi := by
  simp only [ints,intsFrac,Rat.floor_intCast_div_natCast,Rat.ceil_intCast_div_natCast]

theorem lmin_frac (x lo hi : ℤ) (d : ℕ) :
    lmin x ((lo : ℚ)/d) ((hi : ℚ)/d) = (low x lo hi : ℤ)/(d : ℚ) := by
  by_cases hx : 0 ≤ x
  · simp [lmin,low,hx,show (0 : ℚ) ≤ x by exact_mod_cast hx,mul_div_assoc]
  · have hx' : ¬ (0 : ℚ) ≤ x := by exact_mod_cast hx
    simp [lmin,low,hx,hx',mul_div_assoc]

theorem lmax_frac (x lo hi : ℤ) (d : ℕ) :
    lmax x ((lo : ℚ)/d) ((hi : ℚ)/d) = (high x lo hi : ℤ)/(d : ℚ) := by
  by_cases hx : 0 ≤ x
  · simp [lmax,high,hx,show (0 : ℚ) ≤ x by exact_mod_cast hx,mul_div_assoc]
  · have hx' : ¬ (0 : ℚ) ≤ x := by exact_mod_cast hx
    simp [lmax,high,hx,hx',mul_div_assoc]

theorem bRange_eq {c : Cert} {s : Scaled} (hm : Matches c s) (cc : ℤ) :
    RankOne.bRange c cc = bRange s cc := by
  rcases hm with ⟨hd,hlo,hhi,hj,htlo,hthi⟩
  unfold RankOne.bRange bRange
  rw [hlo,hhi,hj,lmin_frac,lmax_frac]
  rw [← sub_div,← add_div]
  rw [← Int.cast_sub,← Int.cast_add]
  exact intsFrac_eq _ _ _

theorem aRange_eq {c : Cert} {s : Scaled} (hm : Matches c s) (P b cc : ℤ) :
    RankOne.aRange P c b cc = aRange P s b cc := by
  rcases hm with ⟨hd,hlo,hhi,hj,htlo,hthi⟩
  have hd' : (s.d : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  unfold RankOne.aRange aRange
  rw [hlo,hhi,htlo,hthi,lmin_frac,lmax_frac,lmin_frac,lmax_frac]
  have hlow : (-1 : ℚ) + (low b s.lo s.hi : ℤ)/(s.d : ℚ)/2 - (cc : ℚ)*P +
      (low cc s.tlo s.thi : ℤ)/(s.d : ℚ)/2 =
      ((-2*(s.d : ℤ)+low b s.lo s.hi-2*(s.d : ℤ)*cc*P+low cc s.tlo s.thi : ℤ) : ℚ)/(2*s.d : ℕ) := by
    push_cast
    field_simp [hd'] <;> ring
  have hhigh : (1 : ℚ) + (high b s.lo s.hi : ℤ)/(s.d : ℚ)/2 - (cc : ℚ)*P +
      (high cc s.tlo s.thi : ℤ)/(s.d : ℚ)/2 =
      ((2*(s.d : ℤ)+high b s.lo s.hi-2*(s.d : ℤ)*cc*P+high cc s.tlo s.thi : ℤ) : ℚ)/(2*s.d : ℕ) := by
    push_cast
    field_simp [hd'] <;> ring
  rw [hlow,hhigh]
  exact intsFrac_eq _ _ _

theorem slice_eq {c : Cert} {s : Scaled} (hm : Matches c s) (P Q : ℤ) (η : Z3) (l : ℕ) :
    slabSliceB P Q η c l = slice P Q η c s l := by
  simp only [slabSliceB,slice,bRange_eq hm,aRange_eq hm]
end PerfectPower.RankOneIntegerSlab
