import PerfectPower.PowerComposition
import PerfectPower.LinearPerturbation
import PerfectPower.SquareLeadingQuartic

namespace PerfectPower.QuarticPowerAtlas
structure Case where
  raw : Bool
  L : ℤ
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  deriving DecidableEq

def valid (C : Case) : Prop := C.L ≠ 0 ∧
  if C.raw then SquareLeadingQuartic.rc C.L C.a C.b C.c ≠ 0 ∨
    SquareLeadingQuartic.rd C.L C.a C.b C.d ≠ 0 else C.c ≠ 0 ∨ C.d ≠ 0
instance (C : Case) : Decidable (valid C) := by unfold valid;infer_instance

def value (C : Case) (x : ℤ) : ℤ :=
  if C.raw then SquareLeadingQuartic.value C.L C.a C.b C.c C.d x
  else LinearPerturbation.value C.L C.a C.b C.c C.d x

def outer (C : Case) : Finset (ℤ × ℤ) :=
  if C.raw then SquareLeadingQuartic.points C.L C.a C.b C.c C.d
  else LinearPerturbation.points C.L C.a C.b C.c C.d

theorem outer_complete (C : Case) (h : valid C) (x y : ℤ) : y^2=value C x ↔ (x,y) ∈ outer C := by
  unfold valid at h
  unfold value outer
  split_ifs with hh
  · exact SquareLeadingQuartic.complete C.L C.a C.b C.c C.d h.1 (by simpa [hh] using h.2) x y
  · exact LinearPerturbation.complete C.L C.a C.b C.c C.d h.1 (by simpa [hh] using h.2) x y

/-- Every valid quartic transports to every nonzero integer power coordinate. -/
theorem complete (C : Case) (h : valid C) (q : ℕ) (hq : q ≠ 0) (x y : ℤ) :
    y^2=value C (x^q) ↔ (x,y) ∈ PowerComposition.lift (outer C) q :=
  PowerComposition.complete (fun x => value C (x^q)) (value C) (outer C) q 2 hq
    (fun _ => rfl) (outer_complete C h) x y

end PerfectPower.QuarticPowerAtlas
