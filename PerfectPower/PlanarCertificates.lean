import Mathlib.Tactic

/-! Exact linear contradiction certificates and exhaustive sign splitting.
Accepted identities hold at every REAL point, including all lower-dimensional
faces. The producer's geometry, LP algorithm and chosen samples are not trusted. -/
namespace PerfectPower.PlanarCertificates
abbrev Plane := ℚ × ℚ × ℚ
abbrev Point := ℝ × ℝ
noncomputable def value (a : Plane) (p : Point) : ℝ :=
  (a.1 : ℝ)*p.1+(a.2.1 : ℝ)*p.2+(a.2.2 : ℝ)
def negate (a : Plane) : Plane := (-a.1,-a.2.1,-a.2.2)
noncomputable def sign (a : Plane) (p : Point) : Int :=
  if value a p < 0 then -1 else if value a p = 0 then 0 else 1

inductive Formula where
  | lt (a : Plane)
  | eq (a : Plane)
  | truth (b : Bool)
  | winding (rays : List (Int × Plane × Plane × Plane))
  | neg (f : Formula)
  | conj (f g : Formula)
  deriving DecidableEq

def Formula.eval (f : Formula) (s : Plane → Int) : Bool := match f with
  | .lt a => decide (s a = -1)
  | .eq a => decide (s a = 0)
  | .truth b => b
  | .winding rays => decide ((rays.map (fun r =>
      if s r.2.1 ≠ -1 ∧ s r.2.2.1 = -1 ∧ s r.2.2.2 = -1 then r.1 else 0)).sum ≠ 0)
  | .neg f => !(f.eval s)
  | .conj f g => f.eval s && g.eval s

def Formula.leaves : Formula → List Plane
  | .lt a | .eq a => [a]
  | .truth _ => []
  | .winding rays => rays.flatMap (fun r => [r.2.1,r.2.2.1,r.2.2.2])
  | .neg f => f.leaves
  | .conj f g => f.leaves ++ g.leaves

theorem eval_congr (f : Formula) (s t : Plane → Int)
    (h : ∀ a ∈ f.leaves, s a = t a) : f.eval s = f.eval t := by
  induction f with
  | lt a => simp only [Formula.eval]; rw [h a (by simp [Formula.leaves])]
  | eq a => simp only [Formula.eval]; rw [h a (by simp [Formula.leaves])]
  | truth b => rfl
  | neg f ih => exact congrArg Bool.not (ih h)
  | conj f g ihf ihg =>
    rw [Formula.eval,ihf (fun a ha => h a (by simp [Formula.leaves,ha])),
      ihg (fun a ha => h a (by simp [Formula.leaves,ha]))]
    rfl
  | winding rays =>
    have hr : ∀ r ∈ rays, s r.2.1 = t r.2.1 ∧ s r.2.2.1 = t r.2.2.1 ∧ s r.2.2.2 = t r.2.2.2 := by
      intro r hr
      have hl : ∀ a ∈ [r.2.1,r.2.2.1,r.2.2.2], s a = t a := by
        intro a ha; apply h a
        simp only [Formula.leaves,List.mem_flatMap]
        exact ⟨r,hr,ha⟩
      exact ⟨hl _ (by simp),hl _ (by simp),hl _ (by simp)⟩
    unfold Formula.eval
    congr 2
    congr 1
    apply List.map_congr_left
    intro r hm
    rcases hr r hm with ⟨h1,h2,h3⟩
    rw [h1,h2,h3]

abbrev Assignment := List (Plane × Int)
def lookup (a : Plane) : Assignment → Option Int
  | [] => none
  | e::es => if a=e.1 then some e.2 else lookup a es
noncomputable def Holds (asgn : Assignment) (p : Point) :=
  ∀ e ∈ asgn, sign e.1 p = e.2

theorem lookup_correct (a : Plane) (asgn : Assignment) (p : Point)
    (h : Holds asgn p) (s : Int) (hs : lookup a asgn = some s) : sign a p = s := by
  induction asgn with
  | nil => simp [lookup] at hs
  | cons e es ih =>
    by_cases he : a=e.1
    · simp [lookup,he] at hs
      subst s
      exact he ▸ h e (by simp)
    · simp [lookup,he] at hs
      exact ih (fun x hx => h x (by simp [hx])) hs

abbrev Constraint := Plane × Bool
-- A constraint requires value ≥ 0; true additionally requires value > 0.
def constraints (asgn : Assignment) : List Constraint := asgn.flatMap fun e =>
  if e.2 = -1 then [(negate e.1,true)]
  else if e.2 = 0 then [(e.1,false),(negate e.1,false)] else [(e.1,true)]
noncomputable def Satisfies (cs : List Constraint) (p : Point) :=
  ∀ c ∈ cs, 0 ≤ value c.1 p ∧ (c.2 = true → 0 < value c.1 p)

theorem negate_value (a : Plane) (p : Point) : value (negate a) p = -value a p := by
  simp [value,negate]; ring

theorem holds_constraints (asgn : Assignment) (p : Point) (h : Holds asgn p) :
    Satisfies (constraints asgn) p := by
  intro c hc
  unfold constraints at hc
  obtain ⟨e,he,hlocal⟩ := List.mem_flatMap.mp hc
  have hs := h e he
  by_cases hn : e.2 = -1
  · simp only [hn,if_true,List.mem_singleton] at hlocal
    cases hlocal
    have hv : value e.1 p < 0 := by
      by_contra hh
      simp only [sign,not_lt.mp hh,if_false] at hs
      split_ifs at hs <;> omega
    simp only [negate_value]
    exact ⟨by linarith,fun _ => by linarith⟩
  · by_cases hz : e.2 = 0
    · simp [hn,hz] at hlocal
      have hv : value e.1 p = 0 := by
        by_contra hh
        unfold sign at hs
        split_ifs at hs <;> omega
      rcases hlocal with hlocal | hlocal
      · cases hlocal; simp [hv]
      · cases hlocal; simp [hv,negate_value]
    · simp [hn,hz] at hlocal
      cases hlocal
      have hv : 0 < value e.1 p := by
        by_cases hneg : value e.1 p < 0
        · have he : e.2 = -1 := by simpa [sign,hneg] using hs.symm
          exact False.elim (hn he)
        by_cases hzero : value e.1 p = 0
        · have he : e.2 = 0 := by simpa [sign,hneg,hzero] using hs.symm
          exact False.elim (hz he)
        exact lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hzero)
      exact ⟨le_of_lt hv,fun _ => hv⟩

def combination (terms : List (Constraint × ℚ)) : Plane :=
  ((terms.map (fun e => e.2*e.1.1.1)).sum,
   (terms.map (fun e => e.2*e.1.1.2.1)).sum,
   (terms.map (fun e => e.2*e.1.1.2.2)).sum)
noncomputable def total (terms : List (Constraint × ℚ)) (p : Point) : ℝ :=
  (terms.map (fun e => (e.2 : ℝ)*value e.1.1 p)).sum

theorem combination_value (ts : List (Constraint × ℚ)) (p : Point) :
    value (combination ts) p = total ts p := by
  induction ts with
  | nil => simp [combination,value,total]
  | cons e es ih =>
    simp only [combination,List.map_cons,List.sum_cons,value,Rat.cast_add,Rat.cast_mul,total] at *
    rw [← ih]
    ring

def contradiction (cs : List Constraint) (terms : List (Constraint × ℚ)) : Prop :=
  (∀ e ∈ terms, e.1 ∈ cs ∧ 0 ≤ e.2) ∧
  (combination terms).1 = 0 ∧ (combination terms).2.1 = 0 ∧
  ((combination terms).2.2 < 0 ∨
    ((combination terms).2.2 = 0 ∧ ∃ e ∈ terms, e.1.2 = true ∧ 0 < e.2))
instance (cs : List Constraint) (terms : List (Constraint × ℚ)) : Decidable (contradiction cs terms) := by
  unfold contradiction; infer_instance

theorem contradiction_sound (cs : List Constraint) (terms : List (Constraint × ℚ)) (p : Point)
    (h : contradiction cs terms) (hp : Satisfies cs p) : False := by
  have hterm : ∀ e ∈ terms, 0 ≤ (e.2 : ℝ)*value e.1.1 p := by
    intro e he
    have hw := (h.1 e he).2
    have hc := (hp e.1 (h.1 e he).1).1
    exact mul_nonneg (by exact_mod_cast hw) hc
  have hn : 0 ≤ total terms p := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hx
    exact hterm e he
  have hv := combination_value terms p
  unfold value at hv
  rw [h.2.1,h.2.2.1] at hv
  simp only [Rat.cast_zero,zero_mul,zero_add] at hv
  rcases h.2.2.2 with hneg | ⟨hz,e,he,hs,hw⟩
  · have hn' : ((combination terms).2.2 : ℝ) < 0 := by exact_mod_cast hneg
    linarith
  · have hstrict := (hp e.1 (h.1 e he).1).2 hs
    have hprod : 0 < (e.2 : ℝ)*value e.1.1 p := mul_pos (by exact_mod_cast hw) hstrict
    have hle : (e.2 : ℝ)*value e.1.1 p ≤ total terms p := by
      apply List.single_le_sum
      · intro x hx
        obtain ⟨e',he',rfl⟩ := List.mem_map.mp hx
        exact hterm e' he'
      · exact List.mem_map.mpr ⟨e,he,rfl⟩
    rw [hz] at hv
    simp only [Rat.cast_zero] at hv
    linarith

inductive Tree where
  | leaf
  | impossible (weights : List (Constraint × ℚ))
  | split (a : Plane) (negative zero positive : Tree)
  deriving DecidableEq

def check (f : Formula) (asgn : Assignment) : Tree → Bool
  | .leaf => decide (∀ a ∈ f.leaves, (lookup a asgn).isSome = true) &&
      f.eval (fun a => (lookup a asgn).getD 0)
  | .impossible weights => decide (contradiction (constraints asgn) weights)
  | .split a n z p => check f ((a,-1)::asgn) n &&
      check f ((a,0)::asgn) z && check f ((a,1)::asgn) p

def checked (f : Formula) (asgn : Assignment) (t : Tree) : Prop := check f asgn t = true
instance (f : Formula) (asgn : Assignment) (t : Tree) : Decidable (checked f asgn t) := by
  unfold checked; infer_instance

theorem checked_split (f : Formula) (asgn : Assignment) (a : Plane) (n z p : Tree)
    (hn : checked f ((a,-1)::asgn) n) (hz : checked f ((a,0)::asgn) z)
    (hp : checked f ((a,1)::asgn) p) : checked f asgn (.split a n z p) := by
  simpa only [checked,check,Bool.and_eq_true] using And.intro (And.intro hn hz) hp

theorem checked_sound (f : Formula) (asgn : Assignment) (t : Tree)
    (h : checked f asgn t) (p : Point) (hp : Holds asgn p) : f.eval (fun a => sign a p) = true := by
  induction t generalizing asgn with
  | leaf =>
    change (decide (∀ a ∈ f.leaves, (lookup a asgn).isSome = true) && _) = true at h
    have hpairs : decide (∀ a ∈ f.leaves, (lookup a asgn).isSome = true) = true ∧
        f.eval (fun a => (lookup a asgn).getD 0) = true := by
      simpa only [Bool.and_eq_true] using h
    have hcovered := of_decide_eq_true hpairs.1
    have hc : ∀ a ∈ f.leaves, sign a p = (lookup a asgn).getD 0 := by
      intro a ha
      have hl := hcovered a ha
      cases hs : lookup a asgn with
      | none => simp [hs] at hl
      | some s => simpa [hs] using lookup_correct a asgn p hp s hs
    rw [eval_congr f _ _ hc]
    exact hpairs.2
  | impossible w => exact False.elim (contradiction_sound _ w p (of_decide_eq_true h) (holds_constraints asgn p hp))
  | split a n z q ihn ihz ihq =>
    change (_ && _ && _) = true at h
    have hlast : (check f ((a,-1)::asgn) n = true ∧ check f ((a,0)::asgn) z = true) ∧
        check f ((a,1)::asgn) q = true := by simpa only [Bool.and_eq_true] using h
    have hfirst := hlast.1
    have hs : sign a p = -1 ∨ sign a p = 0 ∨ sign a p = 1 := by
      unfold sign; split_ifs <;> simp
    rcases hs with hn | hz | hq
    · apply ihn ((a,-1)::asgn) hfirst.1
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact hn
      · exact hp e he
    · apply ihz ((a,0)::asgn) hfirst.2
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact hz
      · exact hp e he
    · apply ihq ((a,1)::asgn) hlast.2
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact hq
      · exact hp e he

theorem universal_identity (f : Formula) (t : Tree) (h : checked f [] t) :
    ∀ p : Point, f.eval (fun a => sign a p) = true := by
  intro p
  exact checked_sound f [] t h p (by intro e he; simp at he)

#print axioms universal_identity
#print axioms contradiction_sound
end PerfectPower.PlanarCertificates
