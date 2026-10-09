import Std

/-! Small, Mathlib-independent complete bounded integer queries.
The rectangle is part of the theorem, never an inferred global bound. -/
namespace PerfectPower.BoundedNative

def interval (lo hi : Int) : List Int :=
  (List.range (hi - lo + 1).toNat).map fun (n : Nat) => lo + (n : Int)

theorem mem_interval (lo hi x : Int) : x ∈ interval lo hi ↔ lo ≤ x ∧ x ≤ hi := by
  simp only [interval, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨n, hn, rfl⟩
    omega
  · intro h
    refine ⟨(x - lo).toNat, ?_, ?_⟩ <;> omega

def box (xl xu yl yu : Int) : List (Int × Int) :=
  (interval xl xu).flatMap fun x => (interval yl yu).map fun y => (x, y)

theorem mem_box (xl xu yl yu x y : Int) :
    (x,y) ∈ box xl xu yl yu ↔ xl ≤ x ∧ x ≤ xu ∧ yl ≤ y ∧ y ≤ yu := by
  simp only [box, List.mem_flatMap, List.mem_map, mem_interval, Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    rcases hab with ⟨rfl, rfl⟩
    exact ⟨ha.1, ha.2, hb.1, hb.2⟩
  · intro h
    exact ⟨x, ⟨h.1,h.2.1⟩, y, ⟨h.2.2.1,h.2.2.2⟩, rfl, rfl⟩

def horner : List Int → Int → Int
  | [], _ => 0
  | c :: cs, x => c + x * horner cs x

def solutions (cs : List Int) (d : Nat) (xl xu yl yu : Int) : List (Int × Int) :=
  (box xl xu yl yu).filter fun p => decide (p.2 ^ d = horner cs p.1)

theorem complete (cs : List Int) (d : Nat) (xl xu yl yu x y : Int) :
    (x,y) ∈ solutions cs d xl xu yl yu ↔
    xl ≤ x ∧ x ≤ xu ∧ yl ≤ y ∧ y ≤ yu ∧ y ^ d = horner cs x := by
  simp only [solutions, List.mem_filter, decide_eq_true_eq, mem_box]
  omega

theorem literal_complete (cs : List Int) (d : Nat) (xl xu yl yu : Int)
    (points : List (Int × Int)) (h : solutions cs d xl xu yl yu = points) (x y : Int) :
    (x,y) ∈ points ↔
    xl ≤ x ∧ x ≤ xu ∧ yl ≤ y ∧ y ≤ yu ∧ y ^ d = horner cs x := by
  rw [← h]
  exact complete cs d xl xu yl yu x y

/-- Every nonzero exponent bounds the root by the value's absolute magnitude. -/
theorem root_magnitude_bound (y v : Int) (d : Nat) (hd : 0 < d) (h : y ^ d = v) :
    y.natAbs ≤ v.natAbs := by
  have hp := Nat.le_pow (a := y.natAbs) hd
  rw [← Int.natAbs_pow, h] at hp
  exact hp

/-- A finite source-value bound supplies a complete y rectangle automatically. -/
theorem root_coordinate_bound (y v : Int) (d M : Nat) (hd : 0 < d)
    (h : y ^ d = v) (hv : v.natAbs ≤ M) : -(M : Int) ≤ y ∧ y ≤ (M : Int) := by
  have ha := Nat.le_trans (root_magnitude_bound y v d hd h) hv
  omega

theorem root_cap_bound (y v : Int) (d M cap : Nat) (h : y ^ d = v)
    (hv : v.natAbs ≤ M) (hgap : M < (cap+1)^d) :
    -(cap : Int) ≤ y ∧ y ≤ (cap : Int) := by
  have he : y.natAbs^d = v.natAbs := by rw [← Int.natAbs_pow, h]
  have ha : y.natAbs ≤ cap := by
    by_cases hn : y.natAbs ≤ cap
    · exact hn
    · have hp := Nat.pow_le_pow_left (i := d) (show cap+1 ≤ y.natAbs by omega)
      omega
  omega

theorem source_y_bound (cs : List Int) (d : Nat) (xl xu : Int) (M cap : Nat)
    (hvalues : ((interval xl xu).all fun x => decide ((horner cs x).natAbs ≤ M)) = true)
    (hgap : M < (cap+1)^d) (x y : Int) (hx : xl ≤ x ∧ x ≤ xu)
    (hy : y^d = horner cs x) : -(cap : Int) ≤ y ∧ y ≤ (cap : Int) := by
  have hv := List.all_eq_true.mp hvalues x ((mem_interval xl xu x).mpr hx)
  exact root_cap_bound y (horner cs x) d M cap hy (of_decide_eq_true hv) hgap

theorem bounded_source_complete (cs : List Int) (d : Nat) (xl xu : Int) (M cap : Nat)
    (hvalues : ((interval xl xu).all fun x => decide ((horner cs x).natAbs ≤ M)) = true)
    (hgap : M < (cap+1)^d) (points : List (Int × Int))
    (h : solutions cs d xl xu (-(cap : Int)) (cap : Int) = points) (x y : Int) :
    (x,y) ∈ points ↔ xl ≤ x ∧ x ≤ xu ∧ y^d = horner cs x := by
  rw [← h, complete]
  constructor
  · intro hp
    exact ⟨hp.1,hp.2.1,hp.2.2.2.2⟩
  · intro hp
    have hb := source_y_bound cs d xl xu M cap hvalues hgap x y ⟨hp.1,hp.2.1⟩ hp.2.2
    exact ⟨hp.1,hp.2.1,hb.1,hb.2,hp.2.2⟩

end PerfectPower.BoundedNative
