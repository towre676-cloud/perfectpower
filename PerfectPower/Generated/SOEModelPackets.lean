import PerfectPower.SOESemantics

namespace PerfectPower.SOEModelPackets

set_option linter.unusedVariables false

def obs000 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step000 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then none else (none))

def q000 (s : Fin 2) : Fin 1 := if s=0 then 0 else (0)

def out000 (s : Fin 1) : ℕ := 0

def target000 (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a=0 then (none) else (none)

theorem complete000 (s t : Fin 2) : SOESemantics.Equivalent step000 obs000 s t ↔ q000 s=q000 t := by

  apply SOESemantics.quotient_complete step000 target000 obs000 out000 q000

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q000 s ≠ q000 t → SOESemantics.behavior step000 obs000 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step000 obs000 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs001 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step001 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then none else (some 0))

def q001 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out001 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target001 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then none else (some 0))

theorem complete001 (s t : Fin 2) : SOESemantics.Equivalent step001 obs001 s t ↔ q001 s=q001 t := by

  apply SOESemantics.quotient_complete step001 target001 obs001 out001 q001

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q001 s ≠ q001 t → SOESemantics.behavior step001 obs001 s ([1] : List (Fin 2)) ≠ SOESemantics.behavior step001 obs001 t [1] := by decide

    intro s t h; exact ⟨[1], hw s t h⟩

def obs002 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step002 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then none else (some 1))

def q002 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out002 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target002 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then none else (some 1))

theorem complete002 (s t : Fin 2) : SOESemantics.Equivalent step002 obs002 s t ↔ q002 s=q002 t := by

  apply SOESemantics.quotient_complete step002 target002 obs002 out002 q002

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q002 s ≠ q002 t → SOESemantics.behavior step002 obs002 s ([1] : List (Fin 2)) ≠ SOESemantics.behavior step002 obs002 t [1] := by decide

    intro s t h; exact ⟨[1], hw s t h⟩

def obs003 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step003 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then some 0 else (none))

def q003 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out003 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target003 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then some 0 else (none))

theorem complete003 (s t : Fin 2) : SOESemantics.Equivalent step003 obs003 s t ↔ q003 s=q003 t := by

  apply SOESemantics.quotient_complete step003 target003 obs003 out003 q003

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q003 s ≠ q003 t → SOESemantics.behavior step003 obs003 s ([1] : List (Fin 2)) ≠ SOESemantics.behavior step003 obs003 t [1] := by decide

    intro s t h; exact ⟨[1], hw s t h⟩

def obs004 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step004 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then some 0 else (some 0))

def q004 (s : Fin 2) : Fin 1 := if s=0 then 0 else (0)

def out004 (s : Fin 1) : ℕ := 0

def target004 (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a=0 then (none) else (some 0)

theorem complete004 (s t : Fin 2) : SOESemantics.Equivalent step004 obs004 s t ↔ q004 s=q004 t := by

  apply SOESemantics.quotient_complete step004 target004 obs004 out004 q004

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q004 s ≠ q004 t → SOESemantics.behavior step004 obs004 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step004 obs004 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs005 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step005 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then some 0 else (some 1))

def q005 (s : Fin 2) : Fin 1 := if s=0 then 0 else (0)

def out005 (s : Fin 1) : ℕ := 0

def target005 (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a=0 then (none) else (some 0)

theorem complete005 (s t : Fin 2) : SOESemantics.Equivalent step005 obs005 s t ↔ q005 s=q005 t := by

  apply SOESemantics.quotient_complete step005 target005 obs005 out005 q005

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q005 s ≠ q005 t → SOESemantics.behavior step005 obs005 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step005 obs005 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs006 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step006 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then some 1 else (none))

def q006 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out006 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target006 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then some 1 else (none))

theorem complete006 (s t : Fin 2) : SOESemantics.Equivalent step006 obs006 s t ↔ q006 s=q006 t := by

  apply SOESemantics.quotient_complete step006 target006 obs006 out006 q006

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q006 s ≠ q006 t → SOESemantics.behavior step006 obs006 s ([1] : List (Fin 2)) ≠ SOESemantics.behavior step006 obs006 t [1] := by decide

    intro s t h; exact ⟨[1], hw s t h⟩

def obs007 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step007 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then some 1 else (some 0))

def q007 (s : Fin 2) : Fin 1 := if s=0 then 0 else (0)

def out007 (s : Fin 1) : ℕ := 0

def target007 (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a=0 then (none) else (some 0)

theorem complete007 (s t : Fin 2) : SOESemantics.Equivalent step007 obs007 s t ↔ q007 s=q007 t := by

  apply SOESemantics.quotient_complete step007 target007 obs007 out007 q007

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q007 s ≠ q007 t → SOESemantics.behavior step007 obs007 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step007 obs007 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs008 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step008 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then some 1 else (some 1))

def q008 (s : Fin 2) : Fin 1 := if s=0 then 0 else (0)

def out008 (s : Fin 1) : ℕ := 0

def target008 (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a=0 then (none) else (some 0)

theorem complete008 (s t : Fin 2) : SOESemantics.Equivalent step008 obs008 s t ↔ q008 s=q008 t := by

  apply SOESemantics.quotient_complete step008 target008 obs008 out008 q008

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q008 s ≠ q008 t → SOESemantics.behavior step008 obs008 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step008 obs008 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs009 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step009 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then none else (none))

def q009 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out009 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target009 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then none else (none))

theorem complete009 (s t : Fin 2) : SOESemantics.Equivalent step009 obs009 s t ↔ q009 s=q009 t := by

  apply SOESemantics.quotient_complete step009 target009 obs009 out009 q009

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q009 s ≠ q009 t → SOESemantics.behavior step009 obs009 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step009 obs009 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs010 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step010 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then none else (some 0))

def q010 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out010 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target010 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then none else (some 0))

theorem complete010 (s t : Fin 2) : SOESemantics.Equivalent step010 obs010 s t ↔ q010 s=q010 t := by

  apply SOESemantics.quotient_complete step010 target010 obs010 out010 q010

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q010 s ≠ q010 t → SOESemantics.behavior step010 obs010 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step010 obs010 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs011 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step011 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then none else (some 1))

def q011 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out011 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target011 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then none else (some 1))

theorem complete011 (s t : Fin 2) : SOESemantics.Equivalent step011 obs011 s t ↔ q011 s=q011 t := by

  apply SOESemantics.quotient_complete step011 target011 obs011 out011 q011

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q011 s ≠ q011 t → SOESemantics.behavior step011 obs011 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step011 obs011 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs012 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step012 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then some 0 else (none))

def q012 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out012 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target012 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then some 0 else (none))

theorem complete012 (s t : Fin 2) : SOESemantics.Equivalent step012 obs012 s t ↔ q012 s=q012 t := by

  apply SOESemantics.quotient_complete step012 target012 obs012 out012 q012

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q012 s ≠ q012 t → SOESemantics.behavior step012 obs012 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step012 obs012 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs013 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step013 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then some 0 else (some 0))

def q013 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out013 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target013 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then some 0 else (some 0))

theorem complete013 (s t : Fin 2) : SOESemantics.Equivalent step013 obs013 s t ↔ q013 s=q013 t := by

  apply SOESemantics.quotient_complete step013 target013 obs013 out013 q013

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q013 s ≠ q013 t → SOESemantics.behavior step013 obs013 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step013 obs013 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs014 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step014 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then some 0 else (some 1))

def q014 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out014 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target014 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then some 0 else (some 1))

theorem complete014 (s t : Fin 2) : SOESemantics.Equivalent step014 obs014 s t ↔ q014 s=q014 t := by

  apply SOESemantics.quotient_complete step014 target014 obs014 out014 q014

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q014 s ≠ q014 t → SOESemantics.behavior step014 obs014 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step014 obs014 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs015 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step015 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then some 1 else (none))

def q015 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out015 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target015 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then some 1 else (none))

theorem complete015 (s t : Fin 2) : SOESemantics.Equivalent step015 obs015 s t ↔ q015 s=q015 t := by

  apply SOESemantics.quotient_complete step015 target015 obs015 out015 q015

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q015 s ≠ q015 t → SOESemantics.behavior step015 obs015 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step015 obs015 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs016 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step016 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then some 1 else (some 0))

def q016 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out016 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target016 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then some 1 else (some 0))

theorem complete016 (s t : Fin 2) : SOESemantics.Equivalent step016 obs016 s t ↔ q016 s=q016 t := by

  apply SOESemantics.quotient_complete step016 target016 obs016 out016 q016

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q016 s ≠ q016 t → SOESemantics.behavior step016 obs016 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step016 obs016 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs017 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step017 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then some 1 else (some 1))

def q017 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out017 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target017 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then some 1 else (some 1))

theorem complete017 (s t : Fin 2) : SOESemantics.Equivalent step017 obs017 s t ↔ q017 s=q017 t := by

  apply SOESemantics.quotient_complete step017 target017 obs017 out017 q017

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q017 s ≠ q017 t → SOESemantics.behavior step017 obs017 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step017 obs017 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs018 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step018 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then none else (none))

def q018 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out018 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target018 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then none else (none))

theorem complete018 (s t : Fin 2) : SOESemantics.Equivalent step018 obs018 s t ↔ q018 s=q018 t := by

  apply SOESemantics.quotient_complete step018 target018 obs018 out018 q018

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q018 s ≠ q018 t → SOESemantics.behavior step018 obs018 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step018 obs018 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs019 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step019 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then none else (some 0))

def q019 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out019 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target019 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then none else (some 0))

theorem complete019 (s t : Fin 2) : SOESemantics.Equivalent step019 obs019 s t ↔ q019 s=q019 t := by

  apply SOESemantics.quotient_complete step019 target019 obs019 out019 q019

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q019 s ≠ q019 t → SOESemantics.behavior step019 obs019 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step019 obs019 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs020 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step020 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then none else (some 1))

def q020 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out020 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target020 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then none else (some 1))

theorem complete020 (s t : Fin 2) : SOESemantics.Equivalent step020 obs020 s t ↔ q020 s=q020 t := by

  apply SOESemantics.quotient_complete step020 target020 obs020 out020 q020

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q020 s ≠ q020 t → SOESemantics.behavior step020 obs020 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step020 obs020 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs021 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step021 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then some 0 else (none))

def q021 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out021 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target021 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then some 0 else (none))

theorem complete021 (s t : Fin 2) : SOESemantics.Equivalent step021 obs021 s t ↔ q021 s=q021 t := by

  apply SOESemantics.quotient_complete step021 target021 obs021 out021 q021

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q021 s ≠ q021 t → SOESemantics.behavior step021 obs021 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step021 obs021 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs022 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step022 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then some 0 else (some 0))

def q022 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out022 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target022 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then some 0 else (some 0))

theorem complete022 (s t : Fin 2) : SOESemantics.Equivalent step022 obs022 s t ↔ q022 s=q022 t := by

  apply SOESemantics.quotient_complete step022 target022 obs022 out022 q022

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q022 s ≠ q022 t → SOESemantics.behavior step022 obs022 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step022 obs022 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs023 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step023 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then some 0 else (some 1))

def q023 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out023 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target023 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then some 0 else (some 1))

theorem complete023 (s t : Fin 2) : SOESemantics.Equivalent step023 obs023 s t ↔ q023 s=q023 t := by

  apply SOESemantics.quotient_complete step023 target023 obs023 out023 q023

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q023 s ≠ q023 t → SOESemantics.behavior step023 obs023 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step023 obs023 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs024 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step024 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then some 1 else (none))

def q024 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out024 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target024 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then some 1 else (none))

theorem complete024 (s t : Fin 2) : SOESemantics.Equivalent step024 obs024 s t ↔ q024 s=q024 t := by

  apply SOESemantics.quotient_complete step024 target024 obs024 out024 q024

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q024 s ≠ q024 t → SOESemantics.behavior step024 obs024 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step024 obs024 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs025 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step025 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then some 1 else (some 0))

def q025 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out025 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target025 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then some 1 else (some 0))

theorem complete025 (s t : Fin 2) : SOESemantics.Equivalent step025 obs025 s t ↔ q025 s=q025 t := by

  apply SOESemantics.quotient_complete step025 target025 obs025 out025 q025

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q025 s ≠ q025 t → SOESemantics.behavior step025 obs025 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step025 obs025 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs026 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step026 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then some 1 else (some 1))

def q026 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out026 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target026 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then some 1 else (some 1))

theorem complete026 (s t : Fin 2) : SOESemantics.Equivalent step026 obs026 s t ↔ q026 s=q026 t := by

  apply SOESemantics.quotient_complete step026 target026 obs026 out026 q026

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q026 s ≠ q026 t → SOESemantics.behavior step026 obs026 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step026 obs026 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs027 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step027 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then none else (none))

def q027 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out027 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target027 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then none else (none))

theorem complete027 (s t : Fin 2) : SOESemantics.Equivalent step027 obs027 s t ↔ q027 s=q027 t := by

  apply SOESemantics.quotient_complete step027 target027 obs027 out027 q027

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q027 s ≠ q027 t → SOESemantics.behavior step027 obs027 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step027 obs027 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs028 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step028 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then none else (some 0))

def q028 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out028 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target028 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then none else (some 0))

theorem complete028 (s t : Fin 2) : SOESemantics.Equivalent step028 obs028 s t ↔ q028 s=q028 t := by

  apply SOESemantics.quotient_complete step028 target028 obs028 out028 q028

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q028 s ≠ q028 t → SOESemantics.behavior step028 obs028 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step028 obs028 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs029 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step029 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then none else (some 1))

def q029 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out029 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target029 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then none else (some 1))

theorem complete029 (s t : Fin 2) : SOESemantics.Equivalent step029 obs029 s t ↔ q029 s=q029 t := by

  apply SOESemantics.quotient_complete step029 target029 obs029 out029 q029

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q029 s ≠ q029 t → SOESemantics.behavior step029 obs029 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step029 obs029 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs030 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step030 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then some 0 else (none))

def q030 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out030 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target030 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then some 0 else (none))

theorem complete030 (s t : Fin 2) : SOESemantics.Equivalent step030 obs030 s t ↔ q030 s=q030 t := by

  apply SOESemantics.quotient_complete step030 target030 obs030 out030 q030

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q030 s ≠ q030 t → SOESemantics.behavior step030 obs030 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step030 obs030 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs031 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step031 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then some 0 else (some 0))

def q031 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out031 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target031 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then some 0 else (some 0))

theorem complete031 (s t : Fin 2) : SOESemantics.Equivalent step031 obs031 s t ↔ q031 s=q031 t := by

  apply SOESemantics.quotient_complete step031 target031 obs031 out031 q031

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q031 s ≠ q031 t → SOESemantics.behavior step031 obs031 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step031 obs031 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs032 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step032 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then some 0 else (some 1))

def q032 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out032 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target032 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then some 0 else (some 1))

theorem complete032 (s t : Fin 2) : SOESemantics.Equivalent step032 obs032 s t ↔ q032 s=q032 t := by

  apply SOESemantics.quotient_complete step032 target032 obs032 out032 q032

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q032 s ≠ q032 t → SOESemantics.behavior step032 obs032 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step032 obs032 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs033 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step033 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then some 1 else (none))

def q033 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out033 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target033 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then some 1 else (none))

theorem complete033 (s t : Fin 2) : SOESemantics.Equivalent step033 obs033 s t ↔ q033 s=q033 t := by

  apply SOESemantics.quotient_complete step033 target033 obs033 out033 q033

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q033 s ≠ q033 t → SOESemantics.behavior step033 obs033 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step033 obs033 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs034 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step034 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then some 1 else (some 0))

def q034 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out034 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target034 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then some 1 else (some 0))

theorem complete034 (s t : Fin 2) : SOESemantics.Equivalent step034 obs034 s t ↔ q034 s=q034 t := by

  apply SOESemantics.quotient_complete step034 target034 obs034 out034 q034

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q034 s ≠ q034 t → SOESemantics.behavior step034 obs034 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step034 obs034 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs035 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step035 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then some 1 else (some 1))

def q035 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out035 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target035 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then some 1 else (some 1))

theorem complete035 (s t : Fin 2) : SOESemantics.Equivalent step035 obs035 s t ↔ q035 s=q035 t := by

  apply SOESemantics.quotient_complete step035 target035 obs035 out035 q035

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q035 s ≠ q035 t → SOESemantics.behavior step035 obs035 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step035 obs035 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs036 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step036 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then none else (none))

def q036 (s : Fin 2) : Fin 1 := if s=0 then 0 else (0)

def out036 (s : Fin 1) : ℕ := 0

def target036 (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a=0 then (some 0) else (none)

theorem complete036 (s t : Fin 2) : SOESemantics.Equivalent step036 obs036 s t ↔ q036 s=q036 t := by

  apply SOESemantics.quotient_complete step036 target036 obs036 out036 q036

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q036 s ≠ q036 t → SOESemantics.behavior step036 obs036 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step036 obs036 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs037 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step037 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then none else (some 0))

def q037 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out037 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target037 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then none else (some 0))

theorem complete037 (s t : Fin 2) : SOESemantics.Equivalent step037 obs037 s t ↔ q037 s=q037 t := by

  apply SOESemantics.quotient_complete step037 target037 obs037 out037 q037

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q037 s ≠ q037 t → SOESemantics.behavior step037 obs037 s ([1] : List (Fin 2)) ≠ SOESemantics.behavior step037 obs037 t [1] := by decide

    intro s t h; exact ⟨[1], hw s t h⟩

def obs038 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step038 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then none else (some 1))

def q038 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out038 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target038 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then none else (some 1))

theorem complete038 (s t : Fin 2) : SOESemantics.Equivalent step038 obs038 s t ↔ q038 s=q038 t := by

  apply SOESemantics.quotient_complete step038 target038 obs038 out038 q038

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q038 s ≠ q038 t → SOESemantics.behavior step038 obs038 s ([1] : List (Fin 2)) ≠ SOESemantics.behavior step038 obs038 t [1] := by decide

    intro s t h; exact ⟨[1], hw s t h⟩

def obs039 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step039 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then some 0 else (none))

def q039 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out039 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target039 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then some 0 else (none))

theorem complete039 (s t : Fin 2) : SOESemantics.Equivalent step039 obs039 s t ↔ q039 s=q039 t := by

  apply SOESemantics.quotient_complete step039 target039 obs039 out039 q039

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q039 s ≠ q039 t → SOESemantics.behavior step039 obs039 s ([1] : List (Fin 2)) ≠ SOESemantics.behavior step039 obs039 t [1] := by decide

    intro s t h; exact ⟨[1], hw s t h⟩

def obs040 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step040 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then some 0 else (some 0))

def q040 (s : Fin 2) : Fin 1 := if s=0 then 0 else (0)

def out040 (s : Fin 1) : ℕ := 0

def target040 (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a=0 then (some 0) else (some 0)

theorem complete040 (s t : Fin 2) : SOESemantics.Equivalent step040 obs040 s t ↔ q040 s=q040 t := by

  apply SOESemantics.quotient_complete step040 target040 obs040 out040 q040

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q040 s ≠ q040 t → SOESemantics.behavior step040 obs040 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step040 obs040 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs041 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step041 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then some 0 else (some 1))

def q041 (s : Fin 2) : Fin 1 := if s=0 then 0 else (0)

def out041 (s : Fin 1) : ℕ := 0

def target041 (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a=0 then (some 0) else (some 0)

theorem complete041 (s t : Fin 2) : SOESemantics.Equivalent step041 obs041 s t ↔ q041 s=q041 t := by

  apply SOESemantics.quotient_complete step041 target041 obs041 out041 q041

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q041 s ≠ q041 t → SOESemantics.behavior step041 obs041 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step041 obs041 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs042 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step042 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then some 1 else (none))

def q042 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out042 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target042 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then some 1 else (none))

theorem complete042 (s t : Fin 2) : SOESemantics.Equivalent step042 obs042 s t ↔ q042 s=q042 t := by

  apply SOESemantics.quotient_complete step042 target042 obs042 out042 q042

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q042 s ≠ q042 t → SOESemantics.behavior step042 obs042 s ([1] : List (Fin 2)) ≠ SOESemantics.behavior step042 obs042 t [1] := by decide

    intro s t h; exact ⟨[1], hw s t h⟩

def obs043 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step043 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then some 1 else (some 0))

def q043 (s : Fin 2) : Fin 1 := if s=0 then 0 else (0)

def out043 (s : Fin 1) : ℕ := 0

def target043 (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a=0 then (some 0) else (some 0)

theorem complete043 (s t : Fin 2) : SOESemantics.Equivalent step043 obs043 s t ↔ q043 s=q043 t := by

  apply SOESemantics.quotient_complete step043 target043 obs043 out043 q043

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q043 s ≠ q043 t → SOESemantics.behavior step043 obs043 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step043 obs043 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs044 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step044 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then some 1 else (some 1))

def q044 (s : Fin 2) : Fin 1 := if s=0 then 0 else (0)

def out044 (s : Fin 1) : ℕ := 0

def target044 (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a=0 then (some 0) else (some 0)

theorem complete044 (s t : Fin 2) : SOESemantics.Equivalent step044 obs044 s t ↔ q044 s=q044 t := by

  apply SOESemantics.quotient_complete step044 target044 obs044 out044 q044

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q044 s ≠ q044 t → SOESemantics.behavior step044 obs044 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step044 obs044 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs045 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step045 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then none else (none))

def q045 (s : Fin 2) : Fin 1 := if s=0 then 0 else (0)

def out045 (s : Fin 1) : ℕ := 0

def target045 (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a=0 then (some 0) else (none)

theorem complete045 (s t : Fin 2) : SOESemantics.Equivalent step045 obs045 s t ↔ q045 s=q045 t := by

  apply SOESemantics.quotient_complete step045 target045 obs045 out045 q045

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q045 s ≠ q045 t → SOESemantics.behavior step045 obs045 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step045 obs045 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs046 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step046 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then none else (some 0))

def q046 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out046 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target046 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then none else (some 0))

theorem complete046 (s t : Fin 2) : SOESemantics.Equivalent step046 obs046 s t ↔ q046 s=q046 t := by

  apply SOESemantics.quotient_complete step046 target046 obs046 out046 q046

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q046 s ≠ q046 t → SOESemantics.behavior step046 obs046 s ([1] : List (Fin 2)) ≠ SOESemantics.behavior step046 obs046 t [1] := by decide

    intro s t h; exact ⟨[1], hw s t h⟩

def obs047 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step047 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then none else (some 1))

def q047 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out047 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target047 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then none else (some 1))

theorem complete047 (s t : Fin 2) : SOESemantics.Equivalent step047 obs047 s t ↔ q047 s=q047 t := by

  apply SOESemantics.quotient_complete step047 target047 obs047 out047 q047

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q047 s ≠ q047 t → SOESemantics.behavior step047 obs047 s ([1] : List (Fin 2)) ≠ SOESemantics.behavior step047 obs047 t [1] := by decide

    intro s t h; exact ⟨[1], hw s t h⟩

def obs048 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step048 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then some 0 else (none))

def q048 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out048 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target048 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then some 0 else (none))

theorem complete048 (s t : Fin 2) : SOESemantics.Equivalent step048 obs048 s t ↔ q048 s=q048 t := by

  apply SOESemantics.quotient_complete step048 target048 obs048 out048 q048

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q048 s ≠ q048 t → SOESemantics.behavior step048 obs048 s ([1] : List (Fin 2)) ≠ SOESemantics.behavior step048 obs048 t [1] := by decide

    intro s t h; exact ⟨[1], hw s t h⟩

def obs049 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step049 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then some 0 else (some 0))

def q049 (s : Fin 2) : Fin 1 := if s=0 then 0 else (0)

def out049 (s : Fin 1) : ℕ := 0

def target049 (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a=0 then (some 0) else (some 0)

theorem complete049 (s t : Fin 2) : SOESemantics.Equivalent step049 obs049 s t ↔ q049 s=q049 t := by

  apply SOESemantics.quotient_complete step049 target049 obs049 out049 q049

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q049 s ≠ q049 t → SOESemantics.behavior step049 obs049 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step049 obs049 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs050 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step050 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then some 0 else (some 1))

def q050 (s : Fin 2) : Fin 1 := if s=0 then 0 else (0)

def out050 (s : Fin 1) : ℕ := 0

def target050 (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a=0 then (some 0) else (some 0)

theorem complete050 (s t : Fin 2) : SOESemantics.Equivalent step050 obs050 s t ↔ q050 s=q050 t := by

  apply SOESemantics.quotient_complete step050 target050 obs050 out050 q050

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q050 s ≠ q050 t → SOESemantics.behavior step050 obs050 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step050 obs050 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs051 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step051 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then some 1 else (none))

def q051 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out051 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target051 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then some 1 else (none))

theorem complete051 (s t : Fin 2) : SOESemantics.Equivalent step051 obs051 s t ↔ q051 s=q051 t := by

  apply SOESemantics.quotient_complete step051 target051 obs051 out051 q051

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q051 s ≠ q051 t → SOESemantics.behavior step051 obs051 s ([1] : List (Fin 2)) ≠ SOESemantics.behavior step051 obs051 t [1] := by decide

    intro s t h; exact ⟨[1], hw s t h⟩

def obs052 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step052 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then some 1 else (some 0))

def q052 (s : Fin 2) : Fin 1 := if s=0 then 0 else (0)

def out052 (s : Fin 1) : ℕ := 0

def target052 (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a=0 then (some 0) else (some 0)

theorem complete052 (s t : Fin 2) : SOESemantics.Equivalent step052 obs052 s t ↔ q052 s=q052 t := by

  apply SOESemantics.quotient_complete step052 target052 obs052 out052 q052

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q052 s ≠ q052 t → SOESemantics.behavior step052 obs052 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step052 obs052 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs053 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step053 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then some 1 else (some 1))

def q053 (s : Fin 2) : Fin 1 := if s=0 then 0 else (0)

def out053 (s : Fin 1) : ℕ := 0

def target053 (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a=0 then (some 0) else (some 0)

theorem complete053 (s t : Fin 2) : SOESemantics.Equivalent step053 obs053 s t ↔ q053 s=q053 t := by

  apply SOESemantics.quotient_complete step053 target053 obs053 out053 q053

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q053 s ≠ q053 t → SOESemantics.behavior step053 obs053 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step053 obs053 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs054 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step054 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then none else (none))

def q054 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out054 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target054 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then none else (none))

theorem complete054 (s t : Fin 2) : SOESemantics.Equivalent step054 obs054 s t ↔ q054 s=q054 t := by

  apply SOESemantics.quotient_complete step054 target054 obs054 out054 q054

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q054 s ≠ q054 t → SOESemantics.behavior step054 obs054 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step054 obs054 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs055 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step055 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then none else (some 0))

def q055 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out055 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target055 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then none else (some 0))

theorem complete055 (s t : Fin 2) : SOESemantics.Equivalent step055 obs055 s t ↔ q055 s=q055 t := by

  apply SOESemantics.quotient_complete step055 target055 obs055 out055 q055

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q055 s ≠ q055 t → SOESemantics.behavior step055 obs055 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step055 obs055 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs056 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step056 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then none else (some 1))

def q056 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out056 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target056 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then none else (some 1))

theorem complete056 (s t : Fin 2) : SOESemantics.Equivalent step056 obs056 s t ↔ q056 s=q056 t := by

  apply SOESemantics.quotient_complete step056 target056 obs056 out056 q056

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q056 s ≠ q056 t → SOESemantics.behavior step056 obs056 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step056 obs056 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs057 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step057 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then some 0 else (none))

def q057 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out057 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target057 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then some 0 else (none))

theorem complete057 (s t : Fin 2) : SOESemantics.Equivalent step057 obs057 s t ↔ q057 s=q057 t := by

  apply SOESemantics.quotient_complete step057 target057 obs057 out057 q057

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q057 s ≠ q057 t → SOESemantics.behavior step057 obs057 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step057 obs057 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs058 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step058 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then some 0 else (some 0))

def q058 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out058 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target058 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then some 0 else (some 0))

theorem complete058 (s t : Fin 2) : SOESemantics.Equivalent step058 obs058 s t ↔ q058 s=q058 t := by

  apply SOESemantics.quotient_complete step058 target058 obs058 out058 q058

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q058 s ≠ q058 t → SOESemantics.behavior step058 obs058 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step058 obs058 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs059 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step059 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then some 0 else (some 1))

def q059 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out059 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target059 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then some 0 else (some 1))

theorem complete059 (s t : Fin 2) : SOESemantics.Equivalent step059 obs059 s t ↔ q059 s=q059 t := by

  apply SOESemantics.quotient_complete step059 target059 obs059 out059 q059

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q059 s ≠ q059 t → SOESemantics.behavior step059 obs059 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step059 obs059 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs060 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step060 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then some 1 else (none))

def q060 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out060 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target060 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then some 1 else (none))

theorem complete060 (s t : Fin 2) : SOESemantics.Equivalent step060 obs060 s t ↔ q060 s=q060 t := by

  apply SOESemantics.quotient_complete step060 target060 obs060 out060 q060

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q060 s ≠ q060 t → SOESemantics.behavior step060 obs060 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step060 obs060 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs061 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step061 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then some 1 else (some 0))

def q061 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out061 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target061 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then some 1 else (some 0))

theorem complete061 (s t : Fin 2) : SOESemantics.Equivalent step061 obs061 s t ↔ q061 s=q061 t := by

  apply SOESemantics.quotient_complete step061 target061 obs061 out061 q061

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q061 s ≠ q061 t → SOESemantics.behavior step061 obs061 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step061 obs061 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs062 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step062 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then some 1 else (some 1))

def q062 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out062 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target062 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then some 1 else (some 1))

theorem complete062 (s t : Fin 2) : SOESemantics.Equivalent step062 obs062 s t ↔ q062 s=q062 t := by

  apply SOESemantics.quotient_complete step062 target062 obs062 out062 q062

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q062 s ≠ q062 t → SOESemantics.behavior step062 obs062 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step062 obs062 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs063 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step063 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then none else (none))

def q063 (s : Fin 2) : Fin 1 := if s=0 then 0 else (0)

def out063 (s : Fin 1) : ℕ := 0

def target063 (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a=0 then (some 0) else (none)

theorem complete063 (s t : Fin 2) : SOESemantics.Equivalent step063 obs063 s t ↔ q063 s=q063 t := by

  apply SOESemantics.quotient_complete step063 target063 obs063 out063 q063

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q063 s ≠ q063 t → SOESemantics.behavior step063 obs063 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step063 obs063 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs064 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step064 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then none else (some 0))

def q064 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out064 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target064 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then none else (some 0))

theorem complete064 (s t : Fin 2) : SOESemantics.Equivalent step064 obs064 s t ↔ q064 s=q064 t := by

  apply SOESemantics.quotient_complete step064 target064 obs064 out064 q064

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q064 s ≠ q064 t → SOESemantics.behavior step064 obs064 s ([1] : List (Fin 2)) ≠ SOESemantics.behavior step064 obs064 t [1] := by decide

    intro s t h; exact ⟨[1], hw s t h⟩

def obs065 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step065 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then none else (some 1))

def q065 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out065 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target065 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then none else (some 1))

theorem complete065 (s t : Fin 2) : SOESemantics.Equivalent step065 obs065 s t ↔ q065 s=q065 t := by

  apply SOESemantics.quotient_complete step065 target065 obs065 out065 q065

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q065 s ≠ q065 t → SOESemantics.behavior step065 obs065 s ([1] : List (Fin 2)) ≠ SOESemantics.behavior step065 obs065 t [1] := by decide

    intro s t h; exact ⟨[1], hw s t h⟩

def obs066 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step066 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then some 0 else (none))

def q066 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out066 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target066 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then some 0 else (none))

theorem complete066 (s t : Fin 2) : SOESemantics.Equivalent step066 obs066 s t ↔ q066 s=q066 t := by

  apply SOESemantics.quotient_complete step066 target066 obs066 out066 q066

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q066 s ≠ q066 t → SOESemantics.behavior step066 obs066 s ([1] : List (Fin 2)) ≠ SOESemantics.behavior step066 obs066 t [1] := by decide

    intro s t h; exact ⟨[1], hw s t h⟩

def obs067 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step067 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then some 0 else (some 0))

def q067 (s : Fin 2) : Fin 1 := if s=0 then 0 else (0)

def out067 (s : Fin 1) : ℕ := 0

def target067 (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a=0 then (some 0) else (some 0)

theorem complete067 (s t : Fin 2) : SOESemantics.Equivalent step067 obs067 s t ↔ q067 s=q067 t := by

  apply SOESemantics.quotient_complete step067 target067 obs067 out067 q067

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q067 s ≠ q067 t → SOESemantics.behavior step067 obs067 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step067 obs067 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs068 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step068 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then some 0 else (some 1))

def q068 (s : Fin 2) : Fin 1 := if s=0 then 0 else (0)

def out068 (s : Fin 1) : ℕ := 0

def target068 (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a=0 then (some 0) else (some 0)

theorem complete068 (s t : Fin 2) : SOESemantics.Equivalent step068 obs068 s t ↔ q068 s=q068 t := by

  apply SOESemantics.quotient_complete step068 target068 obs068 out068 q068

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q068 s ≠ q068 t → SOESemantics.behavior step068 obs068 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step068 obs068 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs069 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step069 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then some 1 else (none))

def q069 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out069 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target069 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then some 1 else (none))

theorem complete069 (s t : Fin 2) : SOESemantics.Equivalent step069 obs069 s t ↔ q069 s=q069 t := by

  apply SOESemantics.quotient_complete step069 target069 obs069 out069 q069

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q069 s ≠ q069 t → SOESemantics.behavior step069 obs069 s ([1] : List (Fin 2)) ≠ SOESemantics.behavior step069 obs069 t [1] := by decide

    intro s t h; exact ⟨[1], hw s t h⟩

def obs070 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step070 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then some 1 else (some 0))

def q070 (s : Fin 2) : Fin 1 := if s=0 then 0 else (0)

def out070 (s : Fin 1) : ℕ := 0

def target070 (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a=0 then (some 0) else (some 0)

theorem complete070 (s t : Fin 2) : SOESemantics.Equivalent step070 obs070 s t ↔ q070 s=q070 t := by

  apply SOESemantics.quotient_complete step070 target070 obs070 out070 q070

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q070 s ≠ q070 t → SOESemantics.behavior step070 obs070 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step070 obs070 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs071 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step071 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then some 1 else (some 1))

def q071 (s : Fin 2) : Fin 1 := if s=0 then 0 else (0)

def out071 (s : Fin 1) : ℕ := 0

def target071 (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a=0 then (some 0) else (some 0)

theorem complete071 (s t : Fin 2) : SOESemantics.Equivalent step071 obs071 s t ↔ q071 s=q071 t := by

  apply SOESemantics.quotient_complete step071 target071 obs071 out071 q071

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q071 s ≠ q071 t → SOESemantics.behavior step071 obs071 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step071 obs071 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs072 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step072 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then none else (none))

def q072 (s : Fin 2) : Fin 1 := if s=0 then 0 else (0)

def out072 (s : Fin 1) : ℕ := 0

def target072 (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a=0 then (some 0) else (none)

theorem complete072 (s t : Fin 2) : SOESemantics.Equivalent step072 obs072 s t ↔ q072 s=q072 t := by

  apply SOESemantics.quotient_complete step072 target072 obs072 out072 q072

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q072 s ≠ q072 t → SOESemantics.behavior step072 obs072 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step072 obs072 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs073 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step073 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then none else (some 0))

def q073 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out073 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target073 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then none else (some 0))

theorem complete073 (s t : Fin 2) : SOESemantics.Equivalent step073 obs073 s t ↔ q073 s=q073 t := by

  apply SOESemantics.quotient_complete step073 target073 obs073 out073 q073

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q073 s ≠ q073 t → SOESemantics.behavior step073 obs073 s ([1] : List (Fin 2)) ≠ SOESemantics.behavior step073 obs073 t [1] := by decide

    intro s t h; exact ⟨[1], hw s t h⟩

def obs074 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step074 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then none else (some 1))

def q074 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out074 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target074 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then none else (some 1))

theorem complete074 (s t : Fin 2) : SOESemantics.Equivalent step074 obs074 s t ↔ q074 s=q074 t := by

  apply SOESemantics.quotient_complete step074 target074 obs074 out074 q074

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q074 s ≠ q074 t → SOESemantics.behavior step074 obs074 s ([1] : List (Fin 2)) ≠ SOESemantics.behavior step074 obs074 t [1] := by decide

    intro s t h; exact ⟨[1], hw s t h⟩

def obs075 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step075 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then some 0 else (none))

def q075 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out075 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target075 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then some 0 else (none))

theorem complete075 (s t : Fin 2) : SOESemantics.Equivalent step075 obs075 s t ↔ q075 s=q075 t := by

  apply SOESemantics.quotient_complete step075 target075 obs075 out075 q075

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q075 s ≠ q075 t → SOESemantics.behavior step075 obs075 s ([1] : List (Fin 2)) ≠ SOESemantics.behavior step075 obs075 t [1] := by decide

    intro s t h; exact ⟨[1], hw s t h⟩

def obs076 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step076 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then some 0 else (some 0))

def q076 (s : Fin 2) : Fin 1 := if s=0 then 0 else (0)

def out076 (s : Fin 1) : ℕ := 0

def target076 (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a=0 then (some 0) else (some 0)

theorem complete076 (s t : Fin 2) : SOESemantics.Equivalent step076 obs076 s t ↔ q076 s=q076 t := by

  apply SOESemantics.quotient_complete step076 target076 obs076 out076 q076

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q076 s ≠ q076 t → SOESemantics.behavior step076 obs076 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step076 obs076 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs077 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step077 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then some 0 else (some 1))

def q077 (s : Fin 2) : Fin 1 := if s=0 then 0 else (0)

def out077 (s : Fin 1) : ℕ := 0

def target077 (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a=0 then (some 0) else (some 0)

theorem complete077 (s t : Fin 2) : SOESemantics.Equivalent step077 obs077 s t ↔ q077 s=q077 t := by

  apply SOESemantics.quotient_complete step077 target077 obs077 out077 q077

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q077 s ≠ q077 t → SOESemantics.behavior step077 obs077 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step077 obs077 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs078 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step078 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then some 1 else (none))

def q078 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out078 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def target078 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then some 1 else (none))

theorem complete078 (s t : Fin 2) : SOESemantics.Equivalent step078 obs078 s t ↔ q078 s=q078 t := by

  apply SOESemantics.quotient_complete step078 target078 obs078 out078 q078

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q078 s ≠ q078 t → SOESemantics.behavior step078 obs078 s ([1] : List (Fin 2)) ≠ SOESemantics.behavior step078 obs078 t [1] := by decide

    intro s t h; exact ⟨[1], hw s t h⟩

def obs079 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step079 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then some 1 else (some 0))

def q079 (s : Fin 2) : Fin 1 := if s=0 then 0 else (0)

def out079 (s : Fin 1) : ℕ := 0

def target079 (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a=0 then (some 0) else (some 0)

theorem complete079 (s t : Fin 2) : SOESemantics.Equivalent step079 obs079 s t ↔ q079 s=q079 t := by

  apply SOESemantics.quotient_complete step079 target079 obs079 out079 q079

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q079 s ≠ q079 t → SOESemantics.behavior step079 obs079 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step079 obs079 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs080 (s : Fin 2) : ℕ := if s=0 then 0 else (0)

def step080 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then some 1 else (some 1))

def q080 (s : Fin 2) : Fin 1 := if s=0 then 0 else (0)

def out080 (s : Fin 1) : ℕ := 0

def target080 (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a=0 then (some 0) else (some 0)

theorem complete080 (s t : Fin 2) : SOESemantics.Equivalent step080 obs080 s t ↔ q080 s=q080 t := by

  apply SOESemantics.quotient_complete step080 target080 obs080 out080 q080

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q080 s ≠ q080 t → SOESemantics.behavior step080 obs080 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step080 obs080 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs081 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step081 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then none else (none))

def q081 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out081 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target081 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then none else (none))

theorem complete081 (s t : Fin 2) : SOESemantics.Equivalent step081 obs081 s t ↔ q081 s=q081 t := by

  apply SOESemantics.quotient_complete step081 target081 obs081 out081 q081

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q081 s ≠ q081 t → SOESemantics.behavior step081 obs081 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step081 obs081 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs082 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step082 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then none else (some 0))

def q082 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out082 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target082 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then none else (some 0))

theorem complete082 (s t : Fin 2) : SOESemantics.Equivalent step082 obs082 s t ↔ q082 s=q082 t := by

  apply SOESemantics.quotient_complete step082 target082 obs082 out082 q082

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q082 s ≠ q082 t → SOESemantics.behavior step082 obs082 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step082 obs082 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs083 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step083 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then none else (some 1))

def q083 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out083 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target083 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then none else (some 1))

theorem complete083 (s t : Fin 2) : SOESemantics.Equivalent step083 obs083 s t ↔ q083 s=q083 t := by

  apply SOESemantics.quotient_complete step083 target083 obs083 out083 q083

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q083 s ≠ q083 t → SOESemantics.behavior step083 obs083 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step083 obs083 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs084 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step084 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then some 0 else (none))

def q084 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out084 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target084 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then some 0 else (none))

theorem complete084 (s t : Fin 2) : SOESemantics.Equivalent step084 obs084 s t ↔ q084 s=q084 t := by

  apply SOESemantics.quotient_complete step084 target084 obs084 out084 q084

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q084 s ≠ q084 t → SOESemantics.behavior step084 obs084 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step084 obs084 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs085 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step085 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then some 0 else (some 0))

def q085 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out085 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target085 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then some 0 else (some 0))

theorem complete085 (s t : Fin 2) : SOESemantics.Equivalent step085 obs085 s t ↔ q085 s=q085 t := by

  apply SOESemantics.quotient_complete step085 target085 obs085 out085 q085

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q085 s ≠ q085 t → SOESemantics.behavior step085 obs085 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step085 obs085 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs086 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step086 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then some 0 else (some 1))

def q086 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out086 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target086 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then some 0 else (some 1))

theorem complete086 (s t : Fin 2) : SOESemantics.Equivalent step086 obs086 s t ↔ q086 s=q086 t := by

  apply SOESemantics.quotient_complete step086 target086 obs086 out086 q086

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q086 s ≠ q086 t → SOESemantics.behavior step086 obs086 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step086 obs086 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs087 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step087 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then some 1 else (none))

def q087 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out087 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target087 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then some 1 else (none))

theorem complete087 (s t : Fin 2) : SOESemantics.Equivalent step087 obs087 s t ↔ q087 s=q087 t := by

  apply SOESemantics.quotient_complete step087 target087 obs087 out087 q087

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q087 s ≠ q087 t → SOESemantics.behavior step087 obs087 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step087 obs087 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs088 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step088 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then some 1 else (some 0))

def q088 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out088 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target088 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then some 1 else (some 0))

theorem complete088 (s t : Fin 2) : SOESemantics.Equivalent step088 obs088 s t ↔ q088 s=q088 t := by

  apply SOESemantics.quotient_complete step088 target088 obs088 out088 q088

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q088 s ≠ q088 t → SOESemantics.behavior step088 obs088 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step088 obs088 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs089 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step089 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then some 1 else (some 1))

def q089 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out089 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target089 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then some 1 else (some 1))

theorem complete089 (s t : Fin 2) : SOESemantics.Equivalent step089 obs089 s t ↔ q089 s=q089 t := by

  apply SOESemantics.quotient_complete step089 target089 obs089 out089 q089

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q089 s ≠ q089 t → SOESemantics.behavior step089 obs089 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step089 obs089 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs090 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step090 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then none else (none))

def q090 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out090 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target090 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then none else (none))

theorem complete090 (s t : Fin 2) : SOESemantics.Equivalent step090 obs090 s t ↔ q090 s=q090 t := by

  apply SOESemantics.quotient_complete step090 target090 obs090 out090 q090

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q090 s ≠ q090 t → SOESemantics.behavior step090 obs090 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step090 obs090 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs091 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step091 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then none else (some 0))

def q091 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out091 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target091 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then none else (some 0))

theorem complete091 (s t : Fin 2) : SOESemantics.Equivalent step091 obs091 s t ↔ q091 s=q091 t := by

  apply SOESemantics.quotient_complete step091 target091 obs091 out091 q091

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q091 s ≠ q091 t → SOESemantics.behavior step091 obs091 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step091 obs091 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs092 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step092 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then none else (some 1))

def q092 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out092 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target092 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then none else (some 1))

theorem complete092 (s t : Fin 2) : SOESemantics.Equivalent step092 obs092 s t ↔ q092 s=q092 t := by

  apply SOESemantics.quotient_complete step092 target092 obs092 out092 q092

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q092 s ≠ q092 t → SOESemantics.behavior step092 obs092 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step092 obs092 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs093 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step093 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then some 0 else (none))

def q093 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out093 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target093 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then some 0 else (none))

theorem complete093 (s t : Fin 2) : SOESemantics.Equivalent step093 obs093 s t ↔ q093 s=q093 t := by

  apply SOESemantics.quotient_complete step093 target093 obs093 out093 q093

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q093 s ≠ q093 t → SOESemantics.behavior step093 obs093 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step093 obs093 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs094 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step094 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then some 0 else (some 0))

def q094 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out094 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target094 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then some 0 else (some 0))

theorem complete094 (s t : Fin 2) : SOESemantics.Equivalent step094 obs094 s t ↔ q094 s=q094 t := by

  apply SOESemantics.quotient_complete step094 target094 obs094 out094 q094

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q094 s ≠ q094 t → SOESemantics.behavior step094 obs094 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step094 obs094 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs095 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step095 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then some 0 else (some 1))

def q095 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out095 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target095 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then some 0 else (some 1))

theorem complete095 (s t : Fin 2) : SOESemantics.Equivalent step095 obs095 s t ↔ q095 s=q095 t := by

  apply SOESemantics.quotient_complete step095 target095 obs095 out095 q095

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q095 s ≠ q095 t → SOESemantics.behavior step095 obs095 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step095 obs095 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs096 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step096 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then some 1 else (none))

def q096 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out096 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target096 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then some 1 else (none))

theorem complete096 (s t : Fin 2) : SOESemantics.Equivalent step096 obs096 s t ↔ q096 s=q096 t := by

  apply SOESemantics.quotient_complete step096 target096 obs096 out096 q096

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q096 s ≠ q096 t → SOESemantics.behavior step096 obs096 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step096 obs096 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs097 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step097 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then some 1 else (some 0))

def q097 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out097 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target097 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then some 1 else (some 0))

theorem complete097 (s t : Fin 2) : SOESemantics.Equivalent step097 obs097 s t ↔ q097 s=q097 t := by

  apply SOESemantics.quotient_complete step097 target097 obs097 out097 q097

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q097 s ≠ q097 t → SOESemantics.behavior step097 obs097 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step097 obs097 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs098 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step098 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then some 1 else (some 1))

def q098 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out098 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target098 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then some 1 else (some 1))

theorem complete098 (s t : Fin 2) : SOESemantics.Equivalent step098 obs098 s t ↔ q098 s=q098 t := by

  apply SOESemantics.quotient_complete step098 target098 obs098 out098 q098

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q098 s ≠ q098 t → SOESemantics.behavior step098 obs098 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step098 obs098 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs099 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step099 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then none else (none))

def q099 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out099 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target099 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then none else (none))

theorem complete099 (s t : Fin 2) : SOESemantics.Equivalent step099 obs099 s t ↔ q099 s=q099 t := by

  apply SOESemantics.quotient_complete step099 target099 obs099 out099 q099

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q099 s ≠ q099 t → SOESemantics.behavior step099 obs099 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step099 obs099 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs100 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step100 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then none else (some 0))

def q100 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out100 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target100 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then none else (some 0))

theorem complete100 (s t : Fin 2) : SOESemantics.Equivalent step100 obs100 s t ↔ q100 s=q100 t := by

  apply SOESemantics.quotient_complete step100 target100 obs100 out100 q100

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q100 s ≠ q100 t → SOESemantics.behavior step100 obs100 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step100 obs100 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs101 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step101 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then none else (some 1))

def q101 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out101 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target101 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then none else (some 1))

theorem complete101 (s t : Fin 2) : SOESemantics.Equivalent step101 obs101 s t ↔ q101 s=q101 t := by

  apply SOESemantics.quotient_complete step101 target101 obs101 out101 q101

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q101 s ≠ q101 t → SOESemantics.behavior step101 obs101 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step101 obs101 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs102 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step102 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then some 0 else (none))

def q102 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out102 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target102 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then some 0 else (none))

theorem complete102 (s t : Fin 2) : SOESemantics.Equivalent step102 obs102 s t ↔ q102 s=q102 t := by

  apply SOESemantics.quotient_complete step102 target102 obs102 out102 q102

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q102 s ≠ q102 t → SOESemantics.behavior step102 obs102 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step102 obs102 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs103 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step103 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then some 0 else (some 0))

def q103 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out103 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target103 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then some 0 else (some 0))

theorem complete103 (s t : Fin 2) : SOESemantics.Equivalent step103 obs103 s t ↔ q103 s=q103 t := by

  apply SOESemantics.quotient_complete step103 target103 obs103 out103 q103

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q103 s ≠ q103 t → SOESemantics.behavior step103 obs103 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step103 obs103 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs104 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step104 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then some 0 else (some 1))

def q104 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out104 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target104 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then some 0 else (some 1))

theorem complete104 (s t : Fin 2) : SOESemantics.Equivalent step104 obs104 s t ↔ q104 s=q104 t := by

  apply SOESemantics.quotient_complete step104 target104 obs104 out104 q104

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q104 s ≠ q104 t → SOESemantics.behavior step104 obs104 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step104 obs104 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs105 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step105 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then some 1 else (none))

def q105 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out105 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target105 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then some 1 else (none))

theorem complete105 (s t : Fin 2) : SOESemantics.Equivalent step105 obs105 s t ↔ q105 s=q105 t := by

  apply SOESemantics.quotient_complete step105 target105 obs105 out105 q105

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q105 s ≠ q105 t → SOESemantics.behavior step105 obs105 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step105 obs105 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs106 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step106 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then some 1 else (some 0))

def q106 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out106 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target106 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then some 1 else (some 0))

theorem complete106 (s t : Fin 2) : SOESemantics.Equivalent step106 obs106 s t ↔ q106 s=q106 t := by

  apply SOESemantics.quotient_complete step106 target106 obs106 out106 q106

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q106 s ≠ q106 t → SOESemantics.behavior step106 obs106 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step106 obs106 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs107 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step107 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then some 1 else (some 1))

def q107 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out107 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target107 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then some 1 else (some 1))

theorem complete107 (s t : Fin 2) : SOESemantics.Equivalent step107 obs107 s t ↔ q107 s=q107 t := by

  apply SOESemantics.quotient_complete step107 target107 obs107 out107 q107

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q107 s ≠ q107 t → SOESemantics.behavior step107 obs107 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step107 obs107 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs108 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step108 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then none else (none))

def q108 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out108 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target108 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then none else (none))

theorem complete108 (s t : Fin 2) : SOESemantics.Equivalent step108 obs108 s t ↔ q108 s=q108 t := by

  apply SOESemantics.quotient_complete step108 target108 obs108 out108 q108

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q108 s ≠ q108 t → SOESemantics.behavior step108 obs108 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step108 obs108 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs109 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step109 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then none else (some 0))

def q109 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out109 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target109 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then none else (some 0))

theorem complete109 (s t : Fin 2) : SOESemantics.Equivalent step109 obs109 s t ↔ q109 s=q109 t := by

  apply SOESemantics.quotient_complete step109 target109 obs109 out109 q109

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q109 s ≠ q109 t → SOESemantics.behavior step109 obs109 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step109 obs109 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs110 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step110 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then none else (some 1))

def q110 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out110 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target110 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then none else (some 1))

theorem complete110 (s t : Fin 2) : SOESemantics.Equivalent step110 obs110 s t ↔ q110 s=q110 t := by

  apply SOESemantics.quotient_complete step110 target110 obs110 out110 q110

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q110 s ≠ q110 t → SOESemantics.behavior step110 obs110 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step110 obs110 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs111 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step111 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then some 0 else (none))

def q111 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out111 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target111 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then some 0 else (none))

theorem complete111 (s t : Fin 2) : SOESemantics.Equivalent step111 obs111 s t ↔ q111 s=q111 t := by

  apply SOESemantics.quotient_complete step111 target111 obs111 out111 q111

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q111 s ≠ q111 t → SOESemantics.behavior step111 obs111 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step111 obs111 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs112 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step112 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then some 0 else (some 0))

def q112 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out112 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target112 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then some 0 else (some 0))

theorem complete112 (s t : Fin 2) : SOESemantics.Equivalent step112 obs112 s t ↔ q112 s=q112 t := by

  apply SOESemantics.quotient_complete step112 target112 obs112 out112 q112

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q112 s ≠ q112 t → SOESemantics.behavior step112 obs112 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step112 obs112 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs113 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step113 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then some 0 else (some 1))

def q113 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out113 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target113 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then some 0 else (some 1))

theorem complete113 (s t : Fin 2) : SOESemantics.Equivalent step113 obs113 s t ↔ q113 s=q113 t := by

  apply SOESemantics.quotient_complete step113 target113 obs113 out113 q113

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q113 s ≠ q113 t → SOESemantics.behavior step113 obs113 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step113 obs113 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs114 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step114 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then some 1 else (none))

def q114 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out114 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target114 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then some 1 else (none))

theorem complete114 (s t : Fin 2) : SOESemantics.Equivalent step114 obs114 s t ↔ q114 s=q114 t := by

  apply SOESemantics.quotient_complete step114 target114 obs114 out114 q114

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q114 s ≠ q114 t → SOESemantics.behavior step114 obs114 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step114 obs114 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs115 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step115 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then some 1 else (some 0))

def q115 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out115 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target115 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then some 1 else (some 0))

theorem complete115 (s t : Fin 2) : SOESemantics.Equivalent step115 obs115 s t ↔ q115 s=q115 t := by

  apply SOESemantics.quotient_complete step115 target115 obs115 out115 q115

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q115 s ≠ q115 t → SOESemantics.behavior step115 obs115 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step115 obs115 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs116 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step116 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then some 1 else (some 1))

def q116 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out116 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target116 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then some 1 else (some 1))

theorem complete116 (s t : Fin 2) : SOESemantics.Equivalent step116 obs116 s t ↔ q116 s=q116 t := by

  apply SOESemantics.quotient_complete step116 target116 obs116 out116 q116

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q116 s ≠ q116 t → SOESemantics.behavior step116 obs116 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step116 obs116 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs117 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step117 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then none else (none))

def q117 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out117 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target117 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then none else (none))

theorem complete117 (s t : Fin 2) : SOESemantics.Equivalent step117 obs117 s t ↔ q117 s=q117 t := by

  apply SOESemantics.quotient_complete step117 target117 obs117 out117 q117

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q117 s ≠ q117 t → SOESemantics.behavior step117 obs117 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step117 obs117 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs118 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step118 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then none else (some 0))

def q118 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out118 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target118 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then none else (some 0))

theorem complete118 (s t : Fin 2) : SOESemantics.Equivalent step118 obs118 s t ↔ q118 s=q118 t := by

  apply SOESemantics.quotient_complete step118 target118 obs118 out118 q118

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q118 s ≠ q118 t → SOESemantics.behavior step118 obs118 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step118 obs118 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs119 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step119 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then none else (some 1))

def q119 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out119 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target119 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then none else (some 1))

theorem complete119 (s t : Fin 2) : SOESemantics.Equivalent step119 obs119 s t ↔ q119 s=q119 t := by

  apply SOESemantics.quotient_complete step119 target119 obs119 out119 q119

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q119 s ≠ q119 t → SOESemantics.behavior step119 obs119 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step119 obs119 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs120 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step120 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then some 0 else (none))

def q120 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out120 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target120 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then some 0 else (none))

theorem complete120 (s t : Fin 2) : SOESemantics.Equivalent step120 obs120 s t ↔ q120 s=q120 t := by

  apply SOESemantics.quotient_complete step120 target120 obs120 out120 q120

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q120 s ≠ q120 t → SOESemantics.behavior step120 obs120 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step120 obs120 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs121 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step121 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then some 0 else (some 0))

def q121 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out121 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target121 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then some 0 else (some 0))

theorem complete121 (s t : Fin 2) : SOESemantics.Equivalent step121 obs121 s t ↔ q121 s=q121 t := by

  apply SOESemantics.quotient_complete step121 target121 obs121 out121 q121

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q121 s ≠ q121 t → SOESemantics.behavior step121 obs121 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step121 obs121 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs122 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step122 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then some 0 else (some 1))

def q122 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out122 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target122 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then some 0 else (some 1))

theorem complete122 (s t : Fin 2) : SOESemantics.Equivalent step122 obs122 s t ↔ q122 s=q122 t := by

  apply SOESemantics.quotient_complete step122 target122 obs122 out122 q122

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q122 s ≠ q122 t → SOESemantics.behavior step122 obs122 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step122 obs122 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs123 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step123 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then some 1 else (none))

def q123 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out123 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target123 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then some 1 else (none))

theorem complete123 (s t : Fin 2) : SOESemantics.Equivalent step123 obs123 s t ↔ q123 s=q123 t := by

  apply SOESemantics.quotient_complete step123 target123 obs123 out123 q123

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q123 s ≠ q123 t → SOESemantics.behavior step123 obs123 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step123 obs123 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs124 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step124 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then some 1 else (some 0))

def q124 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out124 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target124 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then some 1 else (some 0))

theorem complete124 (s t : Fin 2) : SOESemantics.Equivalent step124 obs124 s t ↔ q124 s=q124 t := by

  apply SOESemantics.quotient_complete step124 target124 obs124 out124 q124

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q124 s ≠ q124 t → SOESemantics.behavior step124 obs124 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step124 obs124 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs125 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step125 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then some 1 else (some 1))

def q125 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out125 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target125 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then some 1 else (some 1))

theorem complete125 (s t : Fin 2) : SOESemantics.Equivalent step125 obs125 s t ↔ q125 s=q125 t := by

  apply SOESemantics.quotient_complete step125 target125 obs125 out125 q125

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q125 s ≠ q125 t → SOESemantics.behavior step125 obs125 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step125 obs125 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs126 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step126 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then none else (none))

def q126 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out126 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target126 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then none else (none))

theorem complete126 (s t : Fin 2) : SOESemantics.Equivalent step126 obs126 s t ↔ q126 s=q126 t := by

  apply SOESemantics.quotient_complete step126 target126 obs126 out126 q126

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q126 s ≠ q126 t → SOESemantics.behavior step126 obs126 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step126 obs126 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs127 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step127 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then none else (some 0))

def q127 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out127 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target127 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then none else (some 0))

theorem complete127 (s t : Fin 2) : SOESemantics.Equivalent step127 obs127 s t ↔ q127 s=q127 t := by

  apply SOESemantics.quotient_complete step127 target127 obs127 out127 q127

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q127 s ≠ q127 t → SOESemantics.behavior step127 obs127 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step127 obs127 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs128 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step128 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then none else (some 1))

def q128 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out128 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target128 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then none else (some 1))

theorem complete128 (s t : Fin 2) : SOESemantics.Equivalent step128 obs128 s t ↔ q128 s=q128 t := by

  apply SOESemantics.quotient_complete step128 target128 obs128 out128 q128

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q128 s ≠ q128 t → SOESemantics.behavior step128 obs128 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step128 obs128 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs129 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step129 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then some 0 else (none))

def q129 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out129 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target129 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then some 0 else (none))

theorem complete129 (s t : Fin 2) : SOESemantics.Equivalent step129 obs129 s t ↔ q129 s=q129 t := by

  apply SOESemantics.quotient_complete step129 target129 obs129 out129 q129

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q129 s ≠ q129 t → SOESemantics.behavior step129 obs129 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step129 obs129 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs130 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step130 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then some 0 else (some 0))

def q130 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out130 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target130 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then some 0 else (some 0))

theorem complete130 (s t : Fin 2) : SOESemantics.Equivalent step130 obs130 s t ↔ q130 s=q130 t := by

  apply SOESemantics.quotient_complete step130 target130 obs130 out130 q130

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q130 s ≠ q130 t → SOESemantics.behavior step130 obs130 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step130 obs130 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs131 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step131 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then some 0 else (some 1))

def q131 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out131 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target131 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then some 0 else (some 1))

theorem complete131 (s t : Fin 2) : SOESemantics.Equivalent step131 obs131 s t ↔ q131 s=q131 t := by

  apply SOESemantics.quotient_complete step131 target131 obs131 out131 q131

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q131 s ≠ q131 t → SOESemantics.behavior step131 obs131 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step131 obs131 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs132 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step132 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then some 1 else (none))

def q132 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out132 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target132 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then some 1 else (none))

theorem complete132 (s t : Fin 2) : SOESemantics.Equivalent step132 obs132 s t ↔ q132 s=q132 t := by

  apply SOESemantics.quotient_complete step132 target132 obs132 out132 q132

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q132 s ≠ q132 t → SOESemantics.behavior step132 obs132 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step132 obs132 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs133 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step133 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then some 1 else (some 0))

def q133 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out133 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target133 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then some 1 else (some 0))

theorem complete133 (s t : Fin 2) : SOESemantics.Equivalent step133 obs133 s t ↔ q133 s=q133 t := by

  apply SOESemantics.quotient_complete step133 target133 obs133 out133 q133

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q133 s ≠ q133 t → SOESemantics.behavior step133 obs133 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step133 obs133 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs134 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step134 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then some 1 else (some 1))

def q134 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out134 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target134 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then some 1 else (some 1))

theorem complete134 (s t : Fin 2) : SOESemantics.Equivalent step134 obs134 s t ↔ q134 s=q134 t := by

  apply SOESemantics.quotient_complete step134 target134 obs134 out134 q134

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q134 s ≠ q134 t → SOESemantics.behavior step134 obs134 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step134 obs134 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs135 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step135 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then none else (none))

def q135 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out135 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target135 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then none else (none))

theorem complete135 (s t : Fin 2) : SOESemantics.Equivalent step135 obs135 s t ↔ q135 s=q135 t := by

  apply SOESemantics.quotient_complete step135 target135 obs135 out135 q135

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q135 s ≠ q135 t → SOESemantics.behavior step135 obs135 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step135 obs135 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs136 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step136 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then none else (some 0))

def q136 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out136 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target136 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then none else (some 0))

theorem complete136 (s t : Fin 2) : SOESemantics.Equivalent step136 obs136 s t ↔ q136 s=q136 t := by

  apply SOESemantics.quotient_complete step136 target136 obs136 out136 q136

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q136 s ≠ q136 t → SOESemantics.behavior step136 obs136 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step136 obs136 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs137 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step137 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then none else (some 1))

def q137 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out137 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target137 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then none else (some 1))

theorem complete137 (s t : Fin 2) : SOESemantics.Equivalent step137 obs137 s t ↔ q137 s=q137 t := by

  apply SOESemantics.quotient_complete step137 target137 obs137 out137 q137

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q137 s ≠ q137 t → SOESemantics.behavior step137 obs137 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step137 obs137 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs138 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step138 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then some 0 else (none))

def q138 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out138 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target138 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then some 0 else (none))

theorem complete138 (s t : Fin 2) : SOESemantics.Equivalent step138 obs138 s t ↔ q138 s=q138 t := by

  apply SOESemantics.quotient_complete step138 target138 obs138 out138 q138

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q138 s ≠ q138 t → SOESemantics.behavior step138 obs138 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step138 obs138 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs139 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step139 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then some 0 else (some 0))

def q139 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out139 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target139 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then some 0 else (some 0))

theorem complete139 (s t : Fin 2) : SOESemantics.Equivalent step139 obs139 s t ↔ q139 s=q139 t := by

  apply SOESemantics.quotient_complete step139 target139 obs139 out139 q139

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q139 s ≠ q139 t → SOESemantics.behavior step139 obs139 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step139 obs139 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs140 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step140 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then some 0 else (some 1))

def q140 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out140 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target140 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then some 0 else (some 1))

theorem complete140 (s t : Fin 2) : SOESemantics.Equivalent step140 obs140 s t ↔ q140 s=q140 t := by

  apply SOESemantics.quotient_complete step140 target140 obs140 out140 q140

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q140 s ≠ q140 t → SOESemantics.behavior step140 obs140 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step140 obs140 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs141 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step141 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then some 1 else (none))

def q141 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out141 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target141 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then some 1 else (none))

theorem complete141 (s t : Fin 2) : SOESemantics.Equivalent step141 obs141 s t ↔ q141 s=q141 t := by

  apply SOESemantics.quotient_complete step141 target141 obs141 out141 q141

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q141 s ≠ q141 t → SOESemantics.behavior step141 obs141 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step141 obs141 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs142 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step142 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then some 1 else (some 0))

def q142 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out142 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target142 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then some 1 else (some 0))

theorem complete142 (s t : Fin 2) : SOESemantics.Equivalent step142 obs142 s t ↔ q142 s=q142 t := by

  apply SOESemantics.quotient_complete step142 target142 obs142 out142 q142

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q142 s ≠ q142 t → SOESemantics.behavior step142 obs142 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step142 obs142 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs143 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step143 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then some 1 else (some 1))

def q143 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out143 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target143 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then some 1 else (some 1))

theorem complete143 (s t : Fin 2) : SOESemantics.Equivalent step143 obs143 s t ↔ q143 s=q143 t := by

  apply SOESemantics.quotient_complete step143 target143 obs143 out143 q143

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q143 s ≠ q143 t → SOESemantics.behavior step143 obs143 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step143 obs143 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs144 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step144 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then none else (none))

def q144 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out144 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target144 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then none else (none))

theorem complete144 (s t : Fin 2) : SOESemantics.Equivalent step144 obs144 s t ↔ q144 s=q144 t := by

  apply SOESemantics.quotient_complete step144 target144 obs144 out144 q144

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q144 s ≠ q144 t → SOESemantics.behavior step144 obs144 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step144 obs144 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs145 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step145 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then none else (some 0))

def q145 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out145 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target145 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then none else (some 0))

theorem complete145 (s t : Fin 2) : SOESemantics.Equivalent step145 obs145 s t ↔ q145 s=q145 t := by

  apply SOESemantics.quotient_complete step145 target145 obs145 out145 q145

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q145 s ≠ q145 t → SOESemantics.behavior step145 obs145 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step145 obs145 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs146 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step146 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then none else (some 1))

def q146 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out146 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target146 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then none else (some 1))

theorem complete146 (s t : Fin 2) : SOESemantics.Equivalent step146 obs146 s t ↔ q146 s=q146 t := by

  apply SOESemantics.quotient_complete step146 target146 obs146 out146 q146

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q146 s ≠ q146 t → SOESemantics.behavior step146 obs146 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step146 obs146 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs147 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step147 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then some 0 else (none))

def q147 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out147 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target147 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then some 0 else (none))

theorem complete147 (s t : Fin 2) : SOESemantics.Equivalent step147 obs147 s t ↔ q147 s=q147 t := by

  apply SOESemantics.quotient_complete step147 target147 obs147 out147 q147

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q147 s ≠ q147 t → SOESemantics.behavior step147 obs147 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step147 obs147 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs148 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step148 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then some 0 else (some 0))

def q148 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out148 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target148 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then some 0 else (some 0))

theorem complete148 (s t : Fin 2) : SOESemantics.Equivalent step148 obs148 s t ↔ q148 s=q148 t := by

  apply SOESemantics.quotient_complete step148 target148 obs148 out148 q148

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q148 s ≠ q148 t → SOESemantics.behavior step148 obs148 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step148 obs148 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs149 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step149 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then some 0 else (some 1))

def q149 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out149 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target149 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then some 0 else (some 1))

theorem complete149 (s t : Fin 2) : SOESemantics.Equivalent step149 obs149 s t ↔ q149 s=q149 t := by

  apply SOESemantics.quotient_complete step149 target149 obs149 out149 q149

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q149 s ≠ q149 t → SOESemantics.behavior step149 obs149 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step149 obs149 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs150 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step150 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then some 1 else (none))

def q150 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out150 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target150 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then some 1 else (none))

theorem complete150 (s t : Fin 2) : SOESemantics.Equivalent step150 obs150 s t ↔ q150 s=q150 t := by

  apply SOESemantics.quotient_complete step150 target150 obs150 out150 q150

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q150 s ≠ q150 t → SOESemantics.behavior step150 obs150 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step150 obs150 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs151 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step151 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then some 1 else (some 0))

def q151 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out151 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target151 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then some 1 else (some 0))

theorem complete151 (s t : Fin 2) : SOESemantics.Equivalent step151 obs151 s t ↔ q151 s=q151 t := by

  apply SOESemantics.quotient_complete step151 target151 obs151 out151 q151

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q151 s ≠ q151 t → SOESemantics.behavior step151 obs151 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step151 obs151 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs152 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step152 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then some 1 else (some 1))

def q152 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out152 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target152 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then some 1 else (some 1))

theorem complete152 (s t : Fin 2) : SOESemantics.Equivalent step152 obs152 s t ↔ q152 s=q152 t := by

  apply SOESemantics.quotient_complete step152 target152 obs152 out152 q152

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q152 s ≠ q152 t → SOESemantics.behavior step152 obs152 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step152 obs152 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs153 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step153 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then none else (none))

def q153 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out153 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target153 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then none else (none))

theorem complete153 (s t : Fin 2) : SOESemantics.Equivalent step153 obs153 s t ↔ q153 s=q153 t := by

  apply SOESemantics.quotient_complete step153 target153 obs153 out153 q153

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q153 s ≠ q153 t → SOESemantics.behavior step153 obs153 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step153 obs153 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs154 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step154 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then none else (some 0))

def q154 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out154 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target154 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then none else (some 0))

theorem complete154 (s t : Fin 2) : SOESemantics.Equivalent step154 obs154 s t ↔ q154 s=q154 t := by

  apply SOESemantics.quotient_complete step154 target154 obs154 out154 q154

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q154 s ≠ q154 t → SOESemantics.behavior step154 obs154 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step154 obs154 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs155 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step155 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then none else (some 1))

def q155 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out155 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target155 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then none else (some 1))

theorem complete155 (s t : Fin 2) : SOESemantics.Equivalent step155 obs155 s t ↔ q155 s=q155 t := by

  apply SOESemantics.quotient_complete step155 target155 obs155 out155 q155

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q155 s ≠ q155 t → SOESemantics.behavior step155 obs155 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step155 obs155 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs156 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step156 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then some 0 else (none))

def q156 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out156 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target156 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then some 0 else (none))

theorem complete156 (s t : Fin 2) : SOESemantics.Equivalent step156 obs156 s t ↔ q156 s=q156 t := by

  apply SOESemantics.quotient_complete step156 target156 obs156 out156 q156

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q156 s ≠ q156 t → SOESemantics.behavior step156 obs156 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step156 obs156 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs157 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step157 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then some 0 else (some 0))

def q157 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out157 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target157 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then some 0 else (some 0))

theorem complete157 (s t : Fin 2) : SOESemantics.Equivalent step157 obs157 s t ↔ q157 s=q157 t := by

  apply SOESemantics.quotient_complete step157 target157 obs157 out157 q157

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q157 s ≠ q157 t → SOESemantics.behavior step157 obs157 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step157 obs157 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs158 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step158 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then some 0 else (some 1))

def q158 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out158 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target158 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then some 0 else (some 1))

theorem complete158 (s t : Fin 2) : SOESemantics.Equivalent step158 obs158 s t ↔ q158 s=q158 t := by

  apply SOESemantics.quotient_complete step158 target158 obs158 out158 q158

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q158 s ≠ q158 t → SOESemantics.behavior step158 obs158 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step158 obs158 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs159 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step159 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then some 1 else (none))

def q159 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out159 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target159 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then some 1 else (none))

theorem complete159 (s t : Fin 2) : SOESemantics.Equivalent step159 obs159 s t ↔ q159 s=q159 t := by

  apply SOESemantics.quotient_complete step159 target159 obs159 out159 q159

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q159 s ≠ q159 t → SOESemantics.behavior step159 obs159 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step159 obs159 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs160 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step160 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then some 1 else (some 0))

def q160 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out160 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target160 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then some 1 else (some 0))

theorem complete160 (s t : Fin 2) : SOESemantics.Equivalent step160 obs160 s t ↔ q160 s=q160 t := by

  apply SOESemantics.quotient_complete step160 target160 obs160 out160 q160

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q160 s ≠ q160 t → SOESemantics.behavior step160 obs160 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step160 obs160 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs161 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def step161 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then some 1 else (some 1))

def q161 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out161 (s : Fin 2) : ℕ := if s=0 then 0 else (1)

def target161 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then some 1 else (some 1))

theorem complete161 (s t : Fin 2) : SOESemantics.Equivalent step161 obs161 s t ↔ q161 s=q161 t := by

  apply SOESemantics.quotient_complete step161 target161 obs161 out161 q161

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q161 s ≠ q161 t → SOESemantics.behavior step161 obs161 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step161 obs161 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs162 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step162 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then none else (none))

def q162 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out162 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target162 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then none else (none))

theorem complete162 (s t : Fin 2) : SOESemantics.Equivalent step162 obs162 s t ↔ q162 s=q162 t := by

  apply SOESemantics.quotient_complete step162 target162 obs162 out162 q162

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q162 s ≠ q162 t → SOESemantics.behavior step162 obs162 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step162 obs162 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs163 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step163 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then none else (some 0))

def q163 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out163 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target163 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then none else (some 0))

theorem complete163 (s t : Fin 2) : SOESemantics.Equivalent step163 obs163 s t ↔ q163 s=q163 t := by

  apply SOESemantics.quotient_complete step163 target163 obs163 out163 q163

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q163 s ≠ q163 t → SOESemantics.behavior step163 obs163 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step163 obs163 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs164 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step164 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then none else (some 1))

def q164 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out164 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target164 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then none else (some 1))

theorem complete164 (s t : Fin 2) : SOESemantics.Equivalent step164 obs164 s t ↔ q164 s=q164 t := by

  apply SOESemantics.quotient_complete step164 target164 obs164 out164 q164

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q164 s ≠ q164 t → SOESemantics.behavior step164 obs164 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step164 obs164 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs165 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step165 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then some 0 else (none))

def q165 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out165 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target165 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then some 0 else (none))

theorem complete165 (s t : Fin 2) : SOESemantics.Equivalent step165 obs165 s t ↔ q165 s=q165 t := by

  apply SOESemantics.quotient_complete step165 target165 obs165 out165 q165

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q165 s ≠ q165 t → SOESemantics.behavior step165 obs165 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step165 obs165 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs166 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step166 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then some 0 else (some 0))

def q166 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out166 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target166 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then some 0 else (some 0))

theorem complete166 (s t : Fin 2) : SOESemantics.Equivalent step166 obs166 s t ↔ q166 s=q166 t := by

  apply SOESemantics.quotient_complete step166 target166 obs166 out166 q166

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q166 s ≠ q166 t → SOESemantics.behavior step166 obs166 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step166 obs166 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs167 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step167 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then some 0 else (some 1))

def q167 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out167 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target167 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then some 0 else (some 1))

theorem complete167 (s t : Fin 2) : SOESemantics.Equivalent step167 obs167 s t ↔ q167 s=q167 t := by

  apply SOESemantics.quotient_complete step167 target167 obs167 out167 q167

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q167 s ≠ q167 t → SOESemantics.behavior step167 obs167 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step167 obs167 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs168 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step168 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then some 1 else (none))

def q168 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out168 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target168 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then some 1 else (none))

theorem complete168 (s t : Fin 2) : SOESemantics.Equivalent step168 obs168 s t ↔ q168 s=q168 t := by

  apply SOESemantics.quotient_complete step168 target168 obs168 out168 q168

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q168 s ≠ q168 t → SOESemantics.behavior step168 obs168 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step168 obs168 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs169 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step169 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then some 1 else (some 0))

def q169 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out169 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target169 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then some 1 else (some 0))

theorem complete169 (s t : Fin 2) : SOESemantics.Equivalent step169 obs169 s t ↔ q169 s=q169 t := by

  apply SOESemantics.quotient_complete step169 target169 obs169 out169 q169

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q169 s ≠ q169 t → SOESemantics.behavior step169 obs169 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step169 obs169 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs170 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step170 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then some 1 else (some 1))

def q170 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out170 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target170 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then some 1 else (some 1))

theorem complete170 (s t : Fin 2) : SOESemantics.Equivalent step170 obs170 s t ↔ q170 s=q170 t := by

  apply SOESemantics.quotient_complete step170 target170 obs170 out170 q170

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q170 s ≠ q170 t → SOESemantics.behavior step170 obs170 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step170 obs170 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs171 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step171 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then none else (none))

def q171 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out171 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target171 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then none else (none))

theorem complete171 (s t : Fin 2) : SOESemantics.Equivalent step171 obs171 s t ↔ q171 s=q171 t := by

  apply SOESemantics.quotient_complete step171 target171 obs171 out171 q171

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q171 s ≠ q171 t → SOESemantics.behavior step171 obs171 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step171 obs171 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs172 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step172 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then none else (some 0))

def q172 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out172 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target172 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then none else (some 0))

theorem complete172 (s t : Fin 2) : SOESemantics.Equivalent step172 obs172 s t ↔ q172 s=q172 t := by

  apply SOESemantics.quotient_complete step172 target172 obs172 out172 q172

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q172 s ≠ q172 t → SOESemantics.behavior step172 obs172 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step172 obs172 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs173 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step173 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then none else (some 1))

def q173 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out173 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target173 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then none else (some 1))

theorem complete173 (s t : Fin 2) : SOESemantics.Equivalent step173 obs173 s t ↔ q173 s=q173 t := by

  apply SOESemantics.quotient_complete step173 target173 obs173 out173 q173

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q173 s ≠ q173 t → SOESemantics.behavior step173 obs173 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step173 obs173 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs174 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step174 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then some 0 else (none))

def q174 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out174 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target174 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then some 0 else (none))

theorem complete174 (s t : Fin 2) : SOESemantics.Equivalent step174 obs174 s t ↔ q174 s=q174 t := by

  apply SOESemantics.quotient_complete step174 target174 obs174 out174 q174

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q174 s ≠ q174 t → SOESemantics.behavior step174 obs174 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step174 obs174 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs175 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step175 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then some 0 else (some 0))

def q175 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out175 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target175 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then some 0 else (some 0))

theorem complete175 (s t : Fin 2) : SOESemantics.Equivalent step175 obs175 s t ↔ q175 s=q175 t := by

  apply SOESemantics.quotient_complete step175 target175 obs175 out175 q175

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q175 s ≠ q175 t → SOESemantics.behavior step175 obs175 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step175 obs175 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs176 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step176 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then some 0 else (some 1))

def q176 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out176 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target176 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then some 0 else (some 1))

theorem complete176 (s t : Fin 2) : SOESemantics.Equivalent step176 obs176 s t ↔ q176 s=q176 t := by

  apply SOESemantics.quotient_complete step176 target176 obs176 out176 q176

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q176 s ≠ q176 t → SOESemantics.behavior step176 obs176 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step176 obs176 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs177 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step177 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then some 1 else (none))

def q177 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out177 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target177 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then some 1 else (none))

theorem complete177 (s t : Fin 2) : SOESemantics.Equivalent step177 obs177 s t ↔ q177 s=q177 t := by

  apply SOESemantics.quotient_complete step177 target177 obs177 out177 q177

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q177 s ≠ q177 t → SOESemantics.behavior step177 obs177 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step177 obs177 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs178 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step178 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then some 1 else (some 0))

def q178 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out178 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target178 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then some 1 else (some 0))

theorem complete178 (s t : Fin 2) : SOESemantics.Equivalent step178 obs178 s t ↔ q178 s=q178 t := by

  apply SOESemantics.quotient_complete step178 target178 obs178 out178 q178

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q178 s ≠ q178 t → SOESemantics.behavior step178 obs178 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step178 obs178 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs179 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step179 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then some 1 else (some 1))

def q179 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out179 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target179 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then some 1 else (some 1))

theorem complete179 (s t : Fin 2) : SOESemantics.Equivalent step179 obs179 s t ↔ q179 s=q179 t := by

  apply SOESemantics.quotient_complete step179 target179 obs179 out179 q179

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q179 s ≠ q179 t → SOESemantics.behavior step179 obs179 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step179 obs179 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs180 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step180 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then none else (none))

def q180 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out180 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target180 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then none else (none))

theorem complete180 (s t : Fin 2) : SOESemantics.Equivalent step180 obs180 s t ↔ q180 s=q180 t := by

  apply SOESemantics.quotient_complete step180 target180 obs180 out180 q180

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q180 s ≠ q180 t → SOESemantics.behavior step180 obs180 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step180 obs180 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs181 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step181 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then none else (some 0))

def q181 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out181 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target181 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then none else (some 0))

theorem complete181 (s t : Fin 2) : SOESemantics.Equivalent step181 obs181 s t ↔ q181 s=q181 t := by

  apply SOESemantics.quotient_complete step181 target181 obs181 out181 q181

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q181 s ≠ q181 t → SOESemantics.behavior step181 obs181 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step181 obs181 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs182 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step182 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then none else (some 1))

def q182 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out182 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target182 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then none else (some 1))

theorem complete182 (s t : Fin 2) : SOESemantics.Equivalent step182 obs182 s t ↔ q182 s=q182 t := by

  apply SOESemantics.quotient_complete step182 target182 obs182 out182 q182

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q182 s ≠ q182 t → SOESemantics.behavior step182 obs182 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step182 obs182 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs183 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step183 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then some 0 else (none))

def q183 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out183 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target183 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then some 0 else (none))

theorem complete183 (s t : Fin 2) : SOESemantics.Equivalent step183 obs183 s t ↔ q183 s=q183 t := by

  apply SOESemantics.quotient_complete step183 target183 obs183 out183 q183

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q183 s ≠ q183 t → SOESemantics.behavior step183 obs183 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step183 obs183 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs184 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step184 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then some 0 else (some 0))

def q184 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out184 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target184 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then some 0 else (some 0))

theorem complete184 (s t : Fin 2) : SOESemantics.Equivalent step184 obs184 s t ↔ q184 s=q184 t := by

  apply SOESemantics.quotient_complete step184 target184 obs184 out184 q184

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q184 s ≠ q184 t → SOESemantics.behavior step184 obs184 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step184 obs184 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs185 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step185 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then some 0 else (some 1))

def q185 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out185 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target185 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then some 0 else (some 1))

theorem complete185 (s t : Fin 2) : SOESemantics.Equivalent step185 obs185 s t ↔ q185 s=q185 t := by

  apply SOESemantics.quotient_complete step185 target185 obs185 out185 q185

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q185 s ≠ q185 t → SOESemantics.behavior step185 obs185 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step185 obs185 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs186 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step186 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then some 1 else (none))

def q186 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out186 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target186 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then some 1 else (none))

theorem complete186 (s t : Fin 2) : SOESemantics.Equivalent step186 obs186 s t ↔ q186 s=q186 t := by

  apply SOESemantics.quotient_complete step186 target186 obs186 out186 q186

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q186 s ≠ q186 t → SOESemantics.behavior step186 obs186 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step186 obs186 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs187 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step187 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then some 1 else (some 0))

def q187 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out187 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target187 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then some 1 else (some 0))

theorem complete187 (s t : Fin 2) : SOESemantics.Equivalent step187 obs187 s t ↔ q187 s=q187 t := by

  apply SOESemantics.quotient_complete step187 target187 obs187 out187 q187

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q187 s ≠ q187 t → SOESemantics.behavior step187 obs187 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step187 obs187 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs188 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step188 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then some 1 else (some 1))

def q188 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out188 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target188 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then some 1 else (some 1))

theorem complete188 (s t : Fin 2) : SOESemantics.Equivalent step188 obs188 s t ↔ q188 s=q188 t := by

  apply SOESemantics.quotient_complete step188 target188 obs188 out188 q188

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q188 s ≠ q188 t → SOESemantics.behavior step188 obs188 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step188 obs188 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs189 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step189 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then none else (none))

def q189 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out189 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target189 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then none else (none))

theorem complete189 (s t : Fin 2) : SOESemantics.Equivalent step189 obs189 s t ↔ q189 s=q189 t := by

  apply SOESemantics.quotient_complete step189 target189 obs189 out189 q189

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q189 s ≠ q189 t → SOESemantics.behavior step189 obs189 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step189 obs189 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs190 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step190 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then none else (some 0))

def q190 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out190 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target190 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then none else (some 0))

theorem complete190 (s t : Fin 2) : SOESemantics.Equivalent step190 obs190 s t ↔ q190 s=q190 t := by

  apply SOESemantics.quotient_complete step190 target190 obs190 out190 q190

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q190 s ≠ q190 t → SOESemantics.behavior step190 obs190 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step190 obs190 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs191 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step191 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then none else (some 1))

def q191 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out191 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target191 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then none else (some 1))

theorem complete191 (s t : Fin 2) : SOESemantics.Equivalent step191 obs191 s t ↔ q191 s=q191 t := by

  apply SOESemantics.quotient_complete step191 target191 obs191 out191 q191

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q191 s ≠ q191 t → SOESemantics.behavior step191 obs191 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step191 obs191 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs192 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step192 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then some 0 else (none))

def q192 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out192 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target192 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then some 0 else (none))

theorem complete192 (s t : Fin 2) : SOESemantics.Equivalent step192 obs192 s t ↔ q192 s=q192 t := by

  apply SOESemantics.quotient_complete step192 target192 obs192 out192 q192

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q192 s ≠ q192 t → SOESemantics.behavior step192 obs192 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step192 obs192 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs193 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step193 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then some 0 else (some 0))

def q193 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out193 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target193 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then some 0 else (some 0))

theorem complete193 (s t : Fin 2) : SOESemantics.Equivalent step193 obs193 s t ↔ q193 s=q193 t := by

  apply SOESemantics.quotient_complete step193 target193 obs193 out193 q193

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q193 s ≠ q193 t → SOESemantics.behavior step193 obs193 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step193 obs193 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs194 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step194 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then some 0 else (some 1))

def q194 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out194 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target194 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then some 0 else (some 1))

theorem complete194 (s t : Fin 2) : SOESemantics.Equivalent step194 obs194 s t ↔ q194 s=q194 t := by

  apply SOESemantics.quotient_complete step194 target194 obs194 out194 q194

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q194 s ≠ q194 t → SOESemantics.behavior step194 obs194 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step194 obs194 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs195 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step195 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then some 1 else (none))

def q195 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out195 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target195 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then some 1 else (none))

theorem complete195 (s t : Fin 2) : SOESemantics.Equivalent step195 obs195 s t ↔ q195 s=q195 t := by

  apply SOESemantics.quotient_complete step195 target195 obs195 out195 q195

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q195 s ≠ q195 t → SOESemantics.behavior step195 obs195 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step195 obs195 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs196 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step196 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then some 1 else (some 0))

def q196 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out196 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target196 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then some 1 else (some 0))

theorem complete196 (s t : Fin 2) : SOESemantics.Equivalent step196 obs196 s t ↔ q196 s=q196 t := by

  apply SOESemantics.quotient_complete step196 target196 obs196 out196 q196

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q196 s ≠ q196 t → SOESemantics.behavior step196 obs196 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step196 obs196 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs197 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step197 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then some 1 else (some 1))

def q197 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out197 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target197 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then some 1 else (some 1))

theorem complete197 (s t : Fin 2) : SOESemantics.Equivalent step197 obs197 s t ↔ q197 s=q197 t := by

  apply SOESemantics.quotient_complete step197 target197 obs197 out197 q197

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q197 s ≠ q197 t → SOESemantics.behavior step197 obs197 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step197 obs197 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs198 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step198 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then none else (none))

def q198 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out198 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target198 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then none else (none))

theorem complete198 (s t : Fin 2) : SOESemantics.Equivalent step198 obs198 s t ↔ q198 s=q198 t := by

  apply SOESemantics.quotient_complete step198 target198 obs198 out198 q198

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q198 s ≠ q198 t → SOESemantics.behavior step198 obs198 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step198 obs198 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs199 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step199 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then none else (some 0))

def q199 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out199 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target199 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then none else (some 0))

theorem complete199 (s t : Fin 2) : SOESemantics.Equivalent step199 obs199 s t ↔ q199 s=q199 t := by

  apply SOESemantics.quotient_complete step199 target199 obs199 out199 q199

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q199 s ≠ q199 t → SOESemantics.behavior step199 obs199 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step199 obs199 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs200 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step200 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then none else (some 1))

def q200 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out200 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target200 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then none else (some 1))

theorem complete200 (s t : Fin 2) : SOESemantics.Equivalent step200 obs200 s t ↔ q200 s=q200 t := by

  apply SOESemantics.quotient_complete step200 target200 obs200 out200 q200

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q200 s ≠ q200 t → SOESemantics.behavior step200 obs200 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step200 obs200 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs201 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step201 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then some 0 else (none))

def q201 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out201 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target201 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then some 0 else (none))

theorem complete201 (s t : Fin 2) : SOESemantics.Equivalent step201 obs201 s t ↔ q201 s=q201 t := by

  apply SOESemantics.quotient_complete step201 target201 obs201 out201 q201

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q201 s ≠ q201 t → SOESemantics.behavior step201 obs201 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step201 obs201 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs202 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step202 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then some 0 else (some 0))

def q202 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out202 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target202 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then some 0 else (some 0))

theorem complete202 (s t : Fin 2) : SOESemantics.Equivalent step202 obs202 s t ↔ q202 s=q202 t := by

  apply SOESemantics.quotient_complete step202 target202 obs202 out202 q202

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q202 s ≠ q202 t → SOESemantics.behavior step202 obs202 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step202 obs202 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs203 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step203 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then some 0 else (some 1))

def q203 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out203 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target203 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then some 0 else (some 1))

theorem complete203 (s t : Fin 2) : SOESemantics.Equivalent step203 obs203 s t ↔ q203 s=q203 t := by

  apply SOESemantics.quotient_complete step203 target203 obs203 out203 q203

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q203 s ≠ q203 t → SOESemantics.behavior step203 obs203 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step203 obs203 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs204 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step204 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then some 1 else (none))

def q204 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out204 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target204 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then some 1 else (none))

theorem complete204 (s t : Fin 2) : SOESemantics.Equivalent step204 obs204 s t ↔ q204 s=q204 t := by

  apply SOESemantics.quotient_complete step204 target204 obs204 out204 q204

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q204 s ≠ q204 t → SOESemantics.behavior step204 obs204 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step204 obs204 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs205 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step205 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then some 1 else (some 0))

def q205 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out205 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target205 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then some 1 else (some 0))

theorem complete205 (s t : Fin 2) : SOESemantics.Equivalent step205 obs205 s t ↔ q205 s=q205 t := by

  apply SOESemantics.quotient_complete step205 target205 obs205 out205 q205

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q205 s ≠ q205 t → SOESemantics.behavior step205 obs205 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step205 obs205 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs206 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step206 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then some 1 else (some 1))

def q206 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out206 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target206 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then some 1 else (some 1))

theorem complete206 (s t : Fin 2) : SOESemantics.Equivalent step206 obs206 s t ↔ q206 s=q206 t := by

  apply SOESemantics.quotient_complete step206 target206 obs206 out206 q206

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q206 s ≠ q206 t → SOESemantics.behavior step206 obs206 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step206 obs206 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs207 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step207 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then none else (none))

def q207 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out207 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target207 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then none else (none))

theorem complete207 (s t : Fin 2) : SOESemantics.Equivalent step207 obs207 s t ↔ q207 s=q207 t := by

  apply SOESemantics.quotient_complete step207 target207 obs207 out207 q207

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q207 s ≠ q207 t → SOESemantics.behavior step207 obs207 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step207 obs207 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs208 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step208 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then none else (some 0))

def q208 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out208 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target208 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then none else (some 0))

theorem complete208 (s t : Fin 2) : SOESemantics.Equivalent step208 obs208 s t ↔ q208 s=q208 t := by

  apply SOESemantics.quotient_complete step208 target208 obs208 out208 q208

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q208 s ≠ q208 t → SOESemantics.behavior step208 obs208 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step208 obs208 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs209 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step209 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then none else (some 1))

def q209 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out209 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target209 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then none else (some 1))

theorem complete209 (s t : Fin 2) : SOESemantics.Equivalent step209 obs209 s t ↔ q209 s=q209 t := by

  apply SOESemantics.quotient_complete step209 target209 obs209 out209 q209

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q209 s ≠ q209 t → SOESemantics.behavior step209 obs209 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step209 obs209 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs210 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step210 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then some 0 else (none))

def q210 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out210 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target210 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then some 0 else (none))

theorem complete210 (s t : Fin 2) : SOESemantics.Equivalent step210 obs210 s t ↔ q210 s=q210 t := by

  apply SOESemantics.quotient_complete step210 target210 obs210 out210 q210

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q210 s ≠ q210 t → SOESemantics.behavior step210 obs210 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step210 obs210 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs211 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step211 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then some 0 else (some 0))

def q211 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out211 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target211 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then some 0 else (some 0))

theorem complete211 (s t : Fin 2) : SOESemantics.Equivalent step211 obs211 s t ↔ q211 s=q211 t := by

  apply SOESemantics.quotient_complete step211 target211 obs211 out211 q211

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q211 s ≠ q211 t → SOESemantics.behavior step211 obs211 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step211 obs211 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs212 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step212 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then some 0 else (some 1))

def q212 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out212 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target212 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then some 0 else (some 1))

theorem complete212 (s t : Fin 2) : SOESemantics.Equivalent step212 obs212 s t ↔ q212 s=q212 t := by

  apply SOESemantics.quotient_complete step212 target212 obs212 out212 q212

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q212 s ≠ q212 t → SOESemantics.behavior step212 obs212 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step212 obs212 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs213 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step213 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then some 1 else (none))

def q213 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out213 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target213 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then some 1 else (none))

theorem complete213 (s t : Fin 2) : SOESemantics.Equivalent step213 obs213 s t ↔ q213 s=q213 t := by

  apply SOESemantics.quotient_complete step213 target213 obs213 out213 q213

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q213 s ≠ q213 t → SOESemantics.behavior step213 obs213 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step213 obs213 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs214 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step214 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then some 1 else (some 0))

def q214 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out214 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target214 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then some 1 else (some 0))

theorem complete214 (s t : Fin 2) : SOESemantics.Equivalent step214 obs214 s t ↔ q214 s=q214 t := by

  apply SOESemantics.quotient_complete step214 target214 obs214 out214 q214

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q214 s ≠ q214 t → SOESemantics.behavior step214 obs214 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step214 obs214 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs215 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step215 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then some 1 else (some 1))

def q215 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out215 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target215 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then some 1 else (some 1))

theorem complete215 (s t : Fin 2) : SOESemantics.Equivalent step215 obs215 s t ↔ q215 s=q215 t := by

  apply SOESemantics.quotient_complete step215 target215 obs215 out215 q215

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q215 s ≠ q215 t → SOESemantics.behavior step215 obs215 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step215 obs215 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs216 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step216 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then none else (none))

def q216 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out216 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target216 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then none else (none))

theorem complete216 (s t : Fin 2) : SOESemantics.Equivalent step216 obs216 s t ↔ q216 s=q216 t := by

  apply SOESemantics.quotient_complete step216 target216 obs216 out216 q216

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q216 s ≠ q216 t → SOESemantics.behavior step216 obs216 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step216 obs216 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs217 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step217 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then none else (some 0))

def q217 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out217 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target217 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then none else (some 0))

theorem complete217 (s t : Fin 2) : SOESemantics.Equivalent step217 obs217 s t ↔ q217 s=q217 t := by

  apply SOESemantics.quotient_complete step217 target217 obs217 out217 q217

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q217 s ≠ q217 t → SOESemantics.behavior step217 obs217 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step217 obs217 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs218 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step218 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then none else (some 1))

def q218 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out218 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target218 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then none else (some 1))

theorem complete218 (s t : Fin 2) : SOESemantics.Equivalent step218 obs218 s t ↔ q218 s=q218 t := by

  apply SOESemantics.quotient_complete step218 target218 obs218 out218 q218

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q218 s ≠ q218 t → SOESemantics.behavior step218 obs218 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step218 obs218 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs219 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step219 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then some 0 else (none))

def q219 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out219 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target219 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then some 0 else (none))

theorem complete219 (s t : Fin 2) : SOESemantics.Equivalent step219 obs219 s t ↔ q219 s=q219 t := by

  apply SOESemantics.quotient_complete step219 target219 obs219 out219 q219

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q219 s ≠ q219 t → SOESemantics.behavior step219 obs219 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step219 obs219 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs220 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step220 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then some 0 else (some 0))

def q220 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out220 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target220 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then some 0 else (some 0))

theorem complete220 (s t : Fin 2) : SOESemantics.Equivalent step220 obs220 s t ↔ q220 s=q220 t := by

  apply SOESemantics.quotient_complete step220 target220 obs220 out220 q220

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q220 s ≠ q220 t → SOESemantics.behavior step220 obs220 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step220 obs220 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs221 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step221 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then some 0 else (some 1))

def q221 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out221 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target221 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then some 0 else (some 1))

theorem complete221 (s t : Fin 2) : SOESemantics.Equivalent step221 obs221 s t ↔ q221 s=q221 t := by

  apply SOESemantics.quotient_complete step221 target221 obs221 out221 q221

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q221 s ≠ q221 t → SOESemantics.behavior step221 obs221 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step221 obs221 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs222 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step222 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then some 1 else (none))

def q222 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out222 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target222 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then some 1 else (none))

theorem complete222 (s t : Fin 2) : SOESemantics.Equivalent step222 obs222 s t ↔ q222 s=q222 t := by

  apply SOESemantics.quotient_complete step222 target222 obs222 out222 q222

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q222 s ≠ q222 t → SOESemantics.behavior step222 obs222 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step222 obs222 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs223 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step223 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then some 1 else (some 0))

def q223 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out223 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target223 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then some 1 else (some 0))

theorem complete223 (s t : Fin 2) : SOESemantics.Equivalent step223 obs223 s t ↔ q223 s=q223 t := by

  apply SOESemantics.quotient_complete step223 target223 obs223 out223 q223

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q223 s ≠ q223 t → SOESemantics.behavior step223 obs223 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step223 obs223 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs224 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step224 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then some 1 else (some 1))

def q224 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out224 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target224 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then some 1 else (some 1))

theorem complete224 (s t : Fin 2) : SOESemantics.Equivalent step224 obs224 s t ↔ q224 s=q224 t := by

  apply SOESemantics.quotient_complete step224 target224 obs224 out224 q224

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q224 s ≠ q224 t → SOESemantics.behavior step224 obs224 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step224 obs224 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs225 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step225 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then none else (none))

def q225 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out225 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target225 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then none else (none))

theorem complete225 (s t : Fin 2) : SOESemantics.Equivalent step225 obs225 s t ↔ q225 s=q225 t := by

  apply SOESemantics.quotient_complete step225 target225 obs225 out225 q225

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q225 s ≠ q225 t → SOESemantics.behavior step225 obs225 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step225 obs225 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs226 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step226 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then none else (some 0))

def q226 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out226 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target226 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then none else (some 0))

theorem complete226 (s t : Fin 2) : SOESemantics.Equivalent step226 obs226 s t ↔ q226 s=q226 t := by

  apply SOESemantics.quotient_complete step226 target226 obs226 out226 q226

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q226 s ≠ q226 t → SOESemantics.behavior step226 obs226 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step226 obs226 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs227 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step227 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then none else (some 1))

def q227 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out227 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target227 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then none else (some 1))

theorem complete227 (s t : Fin 2) : SOESemantics.Equivalent step227 obs227 s t ↔ q227 s=q227 t := by

  apply SOESemantics.quotient_complete step227 target227 obs227 out227 q227

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q227 s ≠ q227 t → SOESemantics.behavior step227 obs227 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step227 obs227 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs228 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step228 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then some 0 else (none))

def q228 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out228 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target228 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then some 0 else (none))

theorem complete228 (s t : Fin 2) : SOESemantics.Equivalent step228 obs228 s t ↔ q228 s=q228 t := by

  apply SOESemantics.quotient_complete step228 target228 obs228 out228 q228

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q228 s ≠ q228 t → SOESemantics.behavior step228 obs228 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step228 obs228 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs229 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step229 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then some 0 else (some 0))

def q229 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out229 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target229 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then some 0 else (some 0))

theorem complete229 (s t : Fin 2) : SOESemantics.Equivalent step229 obs229 s t ↔ q229 s=q229 t := by

  apply SOESemantics.quotient_complete step229 target229 obs229 out229 q229

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q229 s ≠ q229 t → SOESemantics.behavior step229 obs229 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step229 obs229 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs230 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step230 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then some 0 else (some 1))

def q230 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out230 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target230 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then some 0 else (some 1))

theorem complete230 (s t : Fin 2) : SOESemantics.Equivalent step230 obs230 s t ↔ q230 s=q230 t := by

  apply SOESemantics.quotient_complete step230 target230 obs230 out230 q230

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q230 s ≠ q230 t → SOESemantics.behavior step230 obs230 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step230 obs230 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs231 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step231 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then some 1 else (none))

def q231 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out231 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target231 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then some 1 else (none))

theorem complete231 (s t : Fin 2) : SOESemantics.Equivalent step231 obs231 s t ↔ q231 s=q231 t := by

  apply SOESemantics.quotient_complete step231 target231 obs231 out231 q231

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q231 s ≠ q231 t → SOESemantics.behavior step231 obs231 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step231 obs231 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs232 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step232 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then some 1 else (some 0))

def q232 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out232 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target232 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then some 1 else (some 0))

theorem complete232 (s t : Fin 2) : SOESemantics.Equivalent step232 obs232 s t ↔ q232 s=q232 t := by

  apply SOESemantics.quotient_complete step232 target232 obs232 out232 q232

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q232 s ≠ q232 t → SOESemantics.behavior step232 obs232 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step232 obs232 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs233 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step233 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then some 1 else (some 1))

def q233 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out233 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target233 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then some 1 else (some 1))

theorem complete233 (s t : Fin 2) : SOESemantics.Equivalent step233 obs233 s t ↔ q233 s=q233 t := by

  apply SOESemantics.quotient_complete step233 target233 obs233 out233 q233

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q233 s ≠ q233 t → SOESemantics.behavior step233 obs233 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step233 obs233 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs234 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step234 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then none else (none))

def q234 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out234 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target234 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then none else (none))

theorem complete234 (s t : Fin 2) : SOESemantics.Equivalent step234 obs234 s t ↔ q234 s=q234 t := by

  apply SOESemantics.quotient_complete step234 target234 obs234 out234 q234

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q234 s ≠ q234 t → SOESemantics.behavior step234 obs234 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step234 obs234 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs235 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step235 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then none else (some 0))

def q235 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out235 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target235 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then none else (some 0))

theorem complete235 (s t : Fin 2) : SOESemantics.Equivalent step235 obs235 s t ↔ q235 s=q235 t := by

  apply SOESemantics.quotient_complete step235 target235 obs235 out235 q235

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q235 s ≠ q235 t → SOESemantics.behavior step235 obs235 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step235 obs235 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs236 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step236 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then none else (some 1))

def q236 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out236 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target236 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then none else (some 1))

theorem complete236 (s t : Fin 2) : SOESemantics.Equivalent step236 obs236 s t ↔ q236 s=q236 t := by

  apply SOESemantics.quotient_complete step236 target236 obs236 out236 q236

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q236 s ≠ q236 t → SOESemantics.behavior step236 obs236 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step236 obs236 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs237 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step237 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then some 0 else (none))

def q237 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out237 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target237 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then some 0 else (none))

theorem complete237 (s t : Fin 2) : SOESemantics.Equivalent step237 obs237 s t ↔ q237 s=q237 t := by

  apply SOESemantics.quotient_complete step237 target237 obs237 out237 q237

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q237 s ≠ q237 t → SOESemantics.behavior step237 obs237 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step237 obs237 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs238 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step238 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then some 0 else (some 0))

def q238 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out238 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target238 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then some 0 else (some 0))

theorem complete238 (s t : Fin 2) : SOESemantics.Equivalent step238 obs238 s t ↔ q238 s=q238 t := by

  apply SOESemantics.quotient_complete step238 target238 obs238 out238 q238

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q238 s ≠ q238 t → SOESemantics.behavior step238 obs238 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step238 obs238 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs239 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step239 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then some 0 else (some 1))

def q239 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out239 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target239 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then some 0 else (some 1))

theorem complete239 (s t : Fin 2) : SOESemantics.Equivalent step239 obs239 s t ↔ q239 s=q239 t := by

  apply SOESemantics.quotient_complete step239 target239 obs239 out239 q239

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q239 s ≠ q239 t → SOESemantics.behavior step239 obs239 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step239 obs239 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs240 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step240 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then some 1 else (none))

def q240 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out240 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target240 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then some 1 else (none))

theorem complete240 (s t : Fin 2) : SOESemantics.Equivalent step240 obs240 s t ↔ q240 s=q240 t := by

  apply SOESemantics.quotient_complete step240 target240 obs240 out240 q240

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q240 s ≠ q240 t → SOESemantics.behavior step240 obs240 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step240 obs240 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs241 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step241 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then some 1 else (some 0))

def q241 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out241 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target241 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then some 1 else (some 0))

theorem complete241 (s t : Fin 2) : SOESemantics.Equivalent step241 obs241 s t ↔ q241 s=q241 t := by

  apply SOESemantics.quotient_complete step241 target241 obs241 out241 q241

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q241 s ≠ q241 t → SOESemantics.behavior step241 obs241 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step241 obs241 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs242 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def step242 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then some 1 else (some 1))

def q242 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out242 (s : Fin 2) : ℕ := if s=0 then 1 else (0)

def target242 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then some 1 else (some 1))

theorem complete242 (s t : Fin 2) : SOESemantics.Equivalent step242 obs242 s t ↔ q242 s=q242 t := by

  apply SOESemantics.quotient_complete step242 target242 obs242 out242 q242

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q242 s ≠ q242 t → SOESemantics.behavior step242 obs242 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step242 obs242 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs243 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step243 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then none else (none))

def q243 (s : Fin 2) : Fin 1 := if s=0 then 0 else (0)

def out243 (s : Fin 1) : ℕ := 1

def target243 (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a=0 then (none) else (none)

theorem complete243 (s t : Fin 2) : SOESemantics.Equivalent step243 obs243 s t ↔ q243 s=q243 t := by

  apply SOESemantics.quotient_complete step243 target243 obs243 out243 q243

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q243 s ≠ q243 t → SOESemantics.behavior step243 obs243 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step243 obs243 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs244 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step244 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then none else (some 0))

def q244 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out244 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target244 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then none else (some 0))

theorem complete244 (s t : Fin 2) : SOESemantics.Equivalent step244 obs244 s t ↔ q244 s=q244 t := by

  apply SOESemantics.quotient_complete step244 target244 obs244 out244 q244

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q244 s ≠ q244 t → SOESemantics.behavior step244 obs244 s ([1] : List (Fin 2)) ≠ SOESemantics.behavior step244 obs244 t [1] := by decide

    intro s t h; exact ⟨[1], hw s t h⟩

def obs245 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step245 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then none else (some 1))

def q245 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out245 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target245 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then none else (some 1))

theorem complete245 (s t : Fin 2) : SOESemantics.Equivalent step245 obs245 s t ↔ q245 s=q245 t := by

  apply SOESemantics.quotient_complete step245 target245 obs245 out245 q245

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q245 s ≠ q245 t → SOESemantics.behavior step245 obs245 s ([1] : List (Fin 2)) ≠ SOESemantics.behavior step245 obs245 t [1] := by decide

    intro s t h; exact ⟨[1], hw s t h⟩

def obs246 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step246 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then some 0 else (none))

def q246 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out246 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target246 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then some 0 else (none))

theorem complete246 (s t : Fin 2) : SOESemantics.Equivalent step246 obs246 s t ↔ q246 s=q246 t := by

  apply SOESemantics.quotient_complete step246 target246 obs246 out246 q246

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q246 s ≠ q246 t → SOESemantics.behavior step246 obs246 s ([1] : List (Fin 2)) ≠ SOESemantics.behavior step246 obs246 t [1] := by decide

    intro s t h; exact ⟨[1], hw s t h⟩

def obs247 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step247 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then some 0 else (some 0))

def q247 (s : Fin 2) : Fin 1 := if s=0 then 0 else (0)

def out247 (s : Fin 1) : ℕ := 1

def target247 (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a=0 then (none) else (some 0)

theorem complete247 (s t : Fin 2) : SOESemantics.Equivalent step247 obs247 s t ↔ q247 s=q247 t := by

  apply SOESemantics.quotient_complete step247 target247 obs247 out247 q247

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q247 s ≠ q247 t → SOESemantics.behavior step247 obs247 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step247 obs247 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs248 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step248 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then some 0 else (some 1))

def q248 (s : Fin 2) : Fin 1 := if s=0 then 0 else (0)

def out248 (s : Fin 1) : ℕ := 1

def target248 (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a=0 then (none) else (some 0)

theorem complete248 (s t : Fin 2) : SOESemantics.Equivalent step248 obs248 s t ↔ q248 s=q248 t := by

  apply SOESemantics.quotient_complete step248 target248 obs248 out248 q248

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q248 s ≠ q248 t → SOESemantics.behavior step248 obs248 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step248 obs248 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs249 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step249 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then some 1 else (none))

def q249 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out249 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target249 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then some 1 else (none))

theorem complete249 (s t : Fin 2) : SOESemantics.Equivalent step249 obs249 s t ↔ q249 s=q249 t := by

  apply SOESemantics.quotient_complete step249 target249 obs249 out249 q249

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q249 s ≠ q249 t → SOESemantics.behavior step249 obs249 s ([1] : List (Fin 2)) ≠ SOESemantics.behavior step249 obs249 t [1] := by decide

    intro s t h; exact ⟨[1], hw s t h⟩

def obs250 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step250 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then some 1 else (some 0))

def q250 (s : Fin 2) : Fin 1 := if s=0 then 0 else (0)

def out250 (s : Fin 1) : ℕ := 1

def target250 (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a=0 then (none) else (some 0)

theorem complete250 (s t : Fin 2) : SOESemantics.Equivalent step250 obs250 s t ↔ q250 s=q250 t := by

  apply SOESemantics.quotient_complete step250 target250 obs250 out250 q250

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q250 s ≠ q250 t → SOESemantics.behavior step250 obs250 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step250 obs250 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs251 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step251 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (none)) else (if s=0 then some 1 else (some 1))

def q251 (s : Fin 2) : Fin 1 := if s=0 then 0 else (0)

def out251 (s : Fin 1) : ℕ := 1

def target251 (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a=0 then (none) else (some 0)

theorem complete251 (s t : Fin 2) : SOESemantics.Equivalent step251 obs251 s t ↔ q251 s=q251 t := by

  apply SOESemantics.quotient_complete step251 target251 obs251 out251 q251

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q251 s ≠ q251 t → SOESemantics.behavior step251 obs251 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step251 obs251 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs252 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step252 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then none else (none))

def q252 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out252 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target252 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then none else (none))

theorem complete252 (s t : Fin 2) : SOESemantics.Equivalent step252 obs252 s t ↔ q252 s=q252 t := by

  apply SOESemantics.quotient_complete step252 target252 obs252 out252 q252

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q252 s ≠ q252 t → SOESemantics.behavior step252 obs252 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step252 obs252 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs253 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step253 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then none else (some 0))

def q253 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out253 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target253 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then none else (some 0))

theorem complete253 (s t : Fin 2) : SOESemantics.Equivalent step253 obs253 s t ↔ q253 s=q253 t := by

  apply SOESemantics.quotient_complete step253 target253 obs253 out253 q253

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q253 s ≠ q253 t → SOESemantics.behavior step253 obs253 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step253 obs253 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs254 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step254 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then none else (some 1))

def q254 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out254 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target254 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then none else (some 1))

theorem complete254 (s t : Fin 2) : SOESemantics.Equivalent step254 obs254 s t ↔ q254 s=q254 t := by

  apply SOESemantics.quotient_complete step254 target254 obs254 out254 q254

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q254 s ≠ q254 t → SOESemantics.behavior step254 obs254 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step254 obs254 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs255 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step255 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then some 0 else (none))

def q255 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out255 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target255 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then some 0 else (none))

theorem complete255 (s t : Fin 2) : SOESemantics.Equivalent step255 obs255 s t ↔ q255 s=q255 t := by

  apply SOESemantics.quotient_complete step255 target255 obs255 out255 q255

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q255 s ≠ q255 t → SOESemantics.behavior step255 obs255 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step255 obs255 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs256 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step256 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then some 0 else (some 0))

def q256 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out256 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target256 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then some 0 else (some 0))

theorem complete256 (s t : Fin 2) : SOESemantics.Equivalent step256 obs256 s t ↔ q256 s=q256 t := by

  apply SOESemantics.quotient_complete step256 target256 obs256 out256 q256

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q256 s ≠ q256 t → SOESemantics.behavior step256 obs256 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step256 obs256 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs257 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step257 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then some 0 else (some 1))

def q257 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out257 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target257 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then some 0 else (some 1))

theorem complete257 (s t : Fin 2) : SOESemantics.Equivalent step257 obs257 s t ↔ q257 s=q257 t := by

  apply SOESemantics.quotient_complete step257 target257 obs257 out257 q257

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q257 s ≠ q257 t → SOESemantics.behavior step257 obs257 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step257 obs257 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs258 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step258 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then some 1 else (none))

def q258 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out258 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target258 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then some 1 else (none))

theorem complete258 (s t : Fin 2) : SOESemantics.Equivalent step258 obs258 s t ↔ q258 s=q258 t := by

  apply SOESemantics.quotient_complete step258 target258 obs258 out258 q258

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q258 s ≠ q258 t → SOESemantics.behavior step258 obs258 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step258 obs258 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs259 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step259 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then some 1 else (some 0))

def q259 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out259 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target259 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then some 1 else (some 0))

theorem complete259 (s t : Fin 2) : SOESemantics.Equivalent step259 obs259 s t ↔ q259 s=q259 t := by

  apply SOESemantics.quotient_complete step259 target259 obs259 out259 q259

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q259 s ≠ q259 t → SOESemantics.behavior step259 obs259 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step259 obs259 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs260 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step260 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then some 1 else (some 1))

def q260 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out260 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target260 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 0)) else (if s=0 then some 1 else (some 1))

theorem complete260 (s t : Fin 2) : SOESemantics.Equivalent step260 obs260 s t ↔ q260 s=q260 t := by

  apply SOESemantics.quotient_complete step260 target260 obs260 out260 q260

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q260 s ≠ q260 t → SOESemantics.behavior step260 obs260 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step260 obs260 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs261 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step261 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then none else (none))

def q261 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out261 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target261 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then none else (none))

theorem complete261 (s t : Fin 2) : SOESemantics.Equivalent step261 obs261 s t ↔ q261 s=q261 t := by

  apply SOESemantics.quotient_complete step261 target261 obs261 out261 q261

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q261 s ≠ q261 t → SOESemantics.behavior step261 obs261 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step261 obs261 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs262 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step262 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then none else (some 0))

def q262 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out262 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target262 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then none else (some 0))

theorem complete262 (s t : Fin 2) : SOESemantics.Equivalent step262 obs262 s t ↔ q262 s=q262 t := by

  apply SOESemantics.quotient_complete step262 target262 obs262 out262 q262

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q262 s ≠ q262 t → SOESemantics.behavior step262 obs262 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step262 obs262 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs263 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step263 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then none else (some 1))

def q263 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out263 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target263 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then none else (some 1))

theorem complete263 (s t : Fin 2) : SOESemantics.Equivalent step263 obs263 s t ↔ q263 s=q263 t := by

  apply SOESemantics.quotient_complete step263 target263 obs263 out263 q263

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q263 s ≠ q263 t → SOESemantics.behavior step263 obs263 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step263 obs263 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs264 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step264 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then some 0 else (none))

def q264 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out264 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target264 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then some 0 else (none))

theorem complete264 (s t : Fin 2) : SOESemantics.Equivalent step264 obs264 s t ↔ q264 s=q264 t := by

  apply SOESemantics.quotient_complete step264 target264 obs264 out264 q264

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q264 s ≠ q264 t → SOESemantics.behavior step264 obs264 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step264 obs264 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs265 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step265 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then some 0 else (some 0))

def q265 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out265 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target265 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then some 0 else (some 0))

theorem complete265 (s t : Fin 2) : SOESemantics.Equivalent step265 obs265 s t ↔ q265 s=q265 t := by

  apply SOESemantics.quotient_complete step265 target265 obs265 out265 q265

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q265 s ≠ q265 t → SOESemantics.behavior step265 obs265 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step265 obs265 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs266 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step266 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then some 0 else (some 1))

def q266 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out266 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target266 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then some 0 else (some 1))

theorem complete266 (s t : Fin 2) : SOESemantics.Equivalent step266 obs266 s t ↔ q266 s=q266 t := by

  apply SOESemantics.quotient_complete step266 target266 obs266 out266 q266

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q266 s ≠ q266 t → SOESemantics.behavior step266 obs266 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step266 obs266 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs267 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step267 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then some 1 else (none))

def q267 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out267 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target267 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then some 1 else (none))

theorem complete267 (s t : Fin 2) : SOESemantics.Equivalent step267 obs267 s t ↔ q267 s=q267 t := by

  apply SOESemantics.quotient_complete step267 target267 obs267 out267 q267

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q267 s ≠ q267 t → SOESemantics.behavior step267 obs267 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step267 obs267 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs268 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step268 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then some 1 else (some 0))

def q268 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out268 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target268 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then some 1 else (some 0))

theorem complete268 (s t : Fin 2) : SOESemantics.Equivalent step268 obs268 s t ↔ q268 s=q268 t := by

  apply SOESemantics.quotient_complete step268 target268 obs268 out268 q268

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q268 s ≠ q268 t → SOESemantics.behavior step268 obs268 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step268 obs268 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs269 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step269 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then some 1 else (some 1))

def q269 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out269 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target269 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then none else (some 1)) else (if s=0 then some 1 else (some 1))

theorem complete269 (s t : Fin 2) : SOESemantics.Equivalent step269 obs269 s t ↔ q269 s=q269 t := by

  apply SOESemantics.quotient_complete step269 target269 obs269 out269 q269

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q269 s ≠ q269 t → SOESemantics.behavior step269 obs269 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step269 obs269 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs270 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step270 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then none else (none))

def q270 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out270 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target270 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then none else (none))

theorem complete270 (s t : Fin 2) : SOESemantics.Equivalent step270 obs270 s t ↔ q270 s=q270 t := by

  apply SOESemantics.quotient_complete step270 target270 obs270 out270 q270

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q270 s ≠ q270 t → SOESemantics.behavior step270 obs270 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step270 obs270 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs271 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step271 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then none else (some 0))

def q271 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out271 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target271 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then none else (some 0))

theorem complete271 (s t : Fin 2) : SOESemantics.Equivalent step271 obs271 s t ↔ q271 s=q271 t := by

  apply SOESemantics.quotient_complete step271 target271 obs271 out271 q271

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q271 s ≠ q271 t → SOESemantics.behavior step271 obs271 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step271 obs271 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs272 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step272 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then none else (some 1))

def q272 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out272 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target272 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then none else (some 1))

theorem complete272 (s t : Fin 2) : SOESemantics.Equivalent step272 obs272 s t ↔ q272 s=q272 t := by

  apply SOESemantics.quotient_complete step272 target272 obs272 out272 q272

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q272 s ≠ q272 t → SOESemantics.behavior step272 obs272 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step272 obs272 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs273 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step273 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then some 0 else (none))

def q273 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out273 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target273 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then some 0 else (none))

theorem complete273 (s t : Fin 2) : SOESemantics.Equivalent step273 obs273 s t ↔ q273 s=q273 t := by

  apply SOESemantics.quotient_complete step273 target273 obs273 out273 q273

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q273 s ≠ q273 t → SOESemantics.behavior step273 obs273 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step273 obs273 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs274 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step274 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then some 0 else (some 0))

def q274 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out274 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target274 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then some 0 else (some 0))

theorem complete274 (s t : Fin 2) : SOESemantics.Equivalent step274 obs274 s t ↔ q274 s=q274 t := by

  apply SOESemantics.quotient_complete step274 target274 obs274 out274 q274

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q274 s ≠ q274 t → SOESemantics.behavior step274 obs274 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step274 obs274 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs275 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step275 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then some 0 else (some 1))

def q275 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out275 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target275 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then some 0 else (some 1))

theorem complete275 (s t : Fin 2) : SOESemantics.Equivalent step275 obs275 s t ↔ q275 s=q275 t := by

  apply SOESemantics.quotient_complete step275 target275 obs275 out275 q275

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q275 s ≠ q275 t → SOESemantics.behavior step275 obs275 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step275 obs275 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs276 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step276 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then some 1 else (none))

def q276 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out276 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target276 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then some 1 else (none))

theorem complete276 (s t : Fin 2) : SOESemantics.Equivalent step276 obs276 s t ↔ q276 s=q276 t := by

  apply SOESemantics.quotient_complete step276 target276 obs276 out276 q276

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q276 s ≠ q276 t → SOESemantics.behavior step276 obs276 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step276 obs276 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs277 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step277 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then some 1 else (some 0))

def q277 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out277 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target277 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then some 1 else (some 0))

theorem complete277 (s t : Fin 2) : SOESemantics.Equivalent step277 obs277 s t ↔ q277 s=q277 t := by

  apply SOESemantics.quotient_complete step277 target277 obs277 out277 q277

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q277 s ≠ q277 t → SOESemantics.behavior step277 obs277 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step277 obs277 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs278 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step278 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then some 1 else (some 1))

def q278 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out278 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target278 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (none)) else (if s=0 then some 1 else (some 1))

theorem complete278 (s t : Fin 2) : SOESemantics.Equivalent step278 obs278 s t ↔ q278 s=q278 t := by

  apply SOESemantics.quotient_complete step278 target278 obs278 out278 q278

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q278 s ≠ q278 t → SOESemantics.behavior step278 obs278 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step278 obs278 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs279 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step279 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then none else (none))

def q279 (s : Fin 2) : Fin 1 := if s=0 then 0 else (0)

def out279 (s : Fin 1) : ℕ := 1

def target279 (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a=0 then (some 0) else (none)

theorem complete279 (s t : Fin 2) : SOESemantics.Equivalent step279 obs279 s t ↔ q279 s=q279 t := by

  apply SOESemantics.quotient_complete step279 target279 obs279 out279 q279

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q279 s ≠ q279 t → SOESemantics.behavior step279 obs279 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step279 obs279 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs280 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step280 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then none else (some 0))

def q280 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out280 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target280 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then none else (some 0))

theorem complete280 (s t : Fin 2) : SOESemantics.Equivalent step280 obs280 s t ↔ q280 s=q280 t := by

  apply SOESemantics.quotient_complete step280 target280 obs280 out280 q280

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q280 s ≠ q280 t → SOESemantics.behavior step280 obs280 s ([1] : List (Fin 2)) ≠ SOESemantics.behavior step280 obs280 t [1] := by decide

    intro s t h; exact ⟨[1], hw s t h⟩

def obs281 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step281 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then none else (some 1))

def q281 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out281 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target281 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then none else (some 1))

theorem complete281 (s t : Fin 2) : SOESemantics.Equivalent step281 obs281 s t ↔ q281 s=q281 t := by

  apply SOESemantics.quotient_complete step281 target281 obs281 out281 q281

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q281 s ≠ q281 t → SOESemantics.behavior step281 obs281 s ([1] : List (Fin 2)) ≠ SOESemantics.behavior step281 obs281 t [1] := by decide

    intro s t h; exact ⟨[1], hw s t h⟩

def obs282 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step282 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then some 0 else (none))

def q282 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out282 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target282 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then some 0 else (none))

theorem complete282 (s t : Fin 2) : SOESemantics.Equivalent step282 obs282 s t ↔ q282 s=q282 t := by

  apply SOESemantics.quotient_complete step282 target282 obs282 out282 q282

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q282 s ≠ q282 t → SOESemantics.behavior step282 obs282 s ([1] : List (Fin 2)) ≠ SOESemantics.behavior step282 obs282 t [1] := by decide

    intro s t h; exact ⟨[1], hw s t h⟩

def obs283 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step283 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then some 0 else (some 0))

def q283 (s : Fin 2) : Fin 1 := if s=0 then 0 else (0)

def out283 (s : Fin 1) : ℕ := 1

def target283 (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a=0 then (some 0) else (some 0)

theorem complete283 (s t : Fin 2) : SOESemantics.Equivalent step283 obs283 s t ↔ q283 s=q283 t := by

  apply SOESemantics.quotient_complete step283 target283 obs283 out283 q283

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q283 s ≠ q283 t → SOESemantics.behavior step283 obs283 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step283 obs283 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs284 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step284 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then some 0 else (some 1))

def q284 (s : Fin 2) : Fin 1 := if s=0 then 0 else (0)

def out284 (s : Fin 1) : ℕ := 1

def target284 (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a=0 then (some 0) else (some 0)

theorem complete284 (s t : Fin 2) : SOESemantics.Equivalent step284 obs284 s t ↔ q284 s=q284 t := by

  apply SOESemantics.quotient_complete step284 target284 obs284 out284 q284

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q284 s ≠ q284 t → SOESemantics.behavior step284 obs284 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step284 obs284 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs285 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step285 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then some 1 else (none))

def q285 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out285 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target285 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then some 1 else (none))

theorem complete285 (s t : Fin 2) : SOESemantics.Equivalent step285 obs285 s t ↔ q285 s=q285 t := by

  apply SOESemantics.quotient_complete step285 target285 obs285 out285 q285

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q285 s ≠ q285 t → SOESemantics.behavior step285 obs285 s ([1] : List (Fin 2)) ≠ SOESemantics.behavior step285 obs285 t [1] := by decide

    intro s t h; exact ⟨[1], hw s t h⟩

def obs286 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step286 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then some 1 else (some 0))

def q286 (s : Fin 2) : Fin 1 := if s=0 then 0 else (0)

def out286 (s : Fin 1) : ℕ := 1

def target286 (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a=0 then (some 0) else (some 0)

theorem complete286 (s t : Fin 2) : SOESemantics.Equivalent step286 obs286 s t ↔ q286 s=q286 t := by

  apply SOESemantics.quotient_complete step286 target286 obs286 out286 q286

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q286 s ≠ q286 t → SOESemantics.behavior step286 obs286 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step286 obs286 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs287 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step287 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 0)) else (if s=0 then some 1 else (some 1))

def q287 (s : Fin 2) : Fin 1 := if s=0 then 0 else (0)

def out287 (s : Fin 1) : ℕ := 1

def target287 (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a=0 then (some 0) else (some 0)

theorem complete287 (s t : Fin 2) : SOESemantics.Equivalent step287 obs287 s t ↔ q287 s=q287 t := by

  apply SOESemantics.quotient_complete step287 target287 obs287 out287 q287

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q287 s ≠ q287 t → SOESemantics.behavior step287 obs287 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step287 obs287 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs288 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step288 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then none else (none))

def q288 (s : Fin 2) : Fin 1 := if s=0 then 0 else (0)

def out288 (s : Fin 1) : ℕ := 1

def target288 (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a=0 then (some 0) else (none)

theorem complete288 (s t : Fin 2) : SOESemantics.Equivalent step288 obs288 s t ↔ q288 s=q288 t := by

  apply SOESemantics.quotient_complete step288 target288 obs288 out288 q288

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q288 s ≠ q288 t → SOESemantics.behavior step288 obs288 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step288 obs288 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs289 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step289 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then none else (some 0))

def q289 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out289 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target289 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then none else (some 0))

theorem complete289 (s t : Fin 2) : SOESemantics.Equivalent step289 obs289 s t ↔ q289 s=q289 t := by

  apply SOESemantics.quotient_complete step289 target289 obs289 out289 q289

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q289 s ≠ q289 t → SOESemantics.behavior step289 obs289 s ([1] : List (Fin 2)) ≠ SOESemantics.behavior step289 obs289 t [1] := by decide

    intro s t h; exact ⟨[1], hw s t h⟩

def obs290 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step290 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then none else (some 1))

def q290 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out290 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target290 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then none else (some 1))

theorem complete290 (s t : Fin 2) : SOESemantics.Equivalent step290 obs290 s t ↔ q290 s=q290 t := by

  apply SOESemantics.quotient_complete step290 target290 obs290 out290 q290

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q290 s ≠ q290 t → SOESemantics.behavior step290 obs290 s ([1] : List (Fin 2)) ≠ SOESemantics.behavior step290 obs290 t [1] := by decide

    intro s t h; exact ⟨[1], hw s t h⟩

def obs291 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step291 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then some 0 else (none))

def q291 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out291 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target291 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then some 0 else (none))

theorem complete291 (s t : Fin 2) : SOESemantics.Equivalent step291 obs291 s t ↔ q291 s=q291 t := by

  apply SOESemantics.quotient_complete step291 target291 obs291 out291 q291

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q291 s ≠ q291 t → SOESemantics.behavior step291 obs291 s ([1] : List (Fin 2)) ≠ SOESemantics.behavior step291 obs291 t [1] := by decide

    intro s t h; exact ⟨[1], hw s t h⟩

def obs292 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step292 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then some 0 else (some 0))

def q292 (s : Fin 2) : Fin 1 := if s=0 then 0 else (0)

def out292 (s : Fin 1) : ℕ := 1

def target292 (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a=0 then (some 0) else (some 0)

theorem complete292 (s t : Fin 2) : SOESemantics.Equivalent step292 obs292 s t ↔ q292 s=q292 t := by

  apply SOESemantics.quotient_complete step292 target292 obs292 out292 q292

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q292 s ≠ q292 t → SOESemantics.behavior step292 obs292 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step292 obs292 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs293 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step293 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then some 0 else (some 1))

def q293 (s : Fin 2) : Fin 1 := if s=0 then 0 else (0)

def out293 (s : Fin 1) : ℕ := 1

def target293 (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a=0 then (some 0) else (some 0)

theorem complete293 (s t : Fin 2) : SOESemantics.Equivalent step293 obs293 s t ↔ q293 s=q293 t := by

  apply SOESemantics.quotient_complete step293 target293 obs293 out293 q293

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q293 s ≠ q293 t → SOESemantics.behavior step293 obs293 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step293 obs293 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs294 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step294 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then some 1 else (none))

def q294 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out294 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target294 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then some 1 else (none))

theorem complete294 (s t : Fin 2) : SOESemantics.Equivalent step294 obs294 s t ↔ q294 s=q294 t := by

  apply SOESemantics.quotient_complete step294 target294 obs294 out294 q294

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q294 s ≠ q294 t → SOESemantics.behavior step294 obs294 s ([1] : List (Fin 2)) ≠ SOESemantics.behavior step294 obs294 t [1] := by decide

    intro s t h; exact ⟨[1], hw s t h⟩

def obs295 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step295 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then some 1 else (some 0))

def q295 (s : Fin 2) : Fin 1 := if s=0 then 0 else (0)

def out295 (s : Fin 1) : ℕ := 1

def target295 (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a=0 then (some 0) else (some 0)

theorem complete295 (s t : Fin 2) : SOESemantics.Equivalent step295 obs295 s t ↔ q295 s=q295 t := by

  apply SOESemantics.quotient_complete step295 target295 obs295 out295 q295

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q295 s ≠ q295 t → SOESemantics.behavior step295 obs295 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step295 obs295 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs296 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step296 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 0 else (some 1)) else (if s=0 then some 1 else (some 1))

def q296 (s : Fin 2) : Fin 1 := if s=0 then 0 else (0)

def out296 (s : Fin 1) : ℕ := 1

def target296 (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a=0 then (some 0) else (some 0)

theorem complete296 (s t : Fin 2) : SOESemantics.Equivalent step296 obs296 s t ↔ q296 s=q296 t := by

  apply SOESemantics.quotient_complete step296 target296 obs296 out296 q296

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q296 s ≠ q296 t → SOESemantics.behavior step296 obs296 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step296 obs296 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs297 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step297 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then none else (none))

def q297 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out297 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target297 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then none else (none))

theorem complete297 (s t : Fin 2) : SOESemantics.Equivalent step297 obs297 s t ↔ q297 s=q297 t := by

  apply SOESemantics.quotient_complete step297 target297 obs297 out297 q297

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q297 s ≠ q297 t → SOESemantics.behavior step297 obs297 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step297 obs297 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs298 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step298 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then none else (some 0))

def q298 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out298 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target298 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then none else (some 0))

theorem complete298 (s t : Fin 2) : SOESemantics.Equivalent step298 obs298 s t ↔ q298 s=q298 t := by

  apply SOESemantics.quotient_complete step298 target298 obs298 out298 q298

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q298 s ≠ q298 t → SOESemantics.behavior step298 obs298 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step298 obs298 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs299 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step299 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then none else (some 1))

def q299 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out299 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target299 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then none else (some 1))

theorem complete299 (s t : Fin 2) : SOESemantics.Equivalent step299 obs299 s t ↔ q299 s=q299 t := by

  apply SOESemantics.quotient_complete step299 target299 obs299 out299 q299

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q299 s ≠ q299 t → SOESemantics.behavior step299 obs299 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step299 obs299 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs300 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step300 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then some 0 else (none))

def q300 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out300 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target300 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then some 0 else (none))

theorem complete300 (s t : Fin 2) : SOESemantics.Equivalent step300 obs300 s t ↔ q300 s=q300 t := by

  apply SOESemantics.quotient_complete step300 target300 obs300 out300 q300

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q300 s ≠ q300 t → SOESemantics.behavior step300 obs300 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step300 obs300 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs301 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step301 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then some 0 else (some 0))

def q301 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out301 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target301 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then some 0 else (some 0))

theorem complete301 (s t : Fin 2) : SOESemantics.Equivalent step301 obs301 s t ↔ q301 s=q301 t := by

  apply SOESemantics.quotient_complete step301 target301 obs301 out301 q301

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q301 s ≠ q301 t → SOESemantics.behavior step301 obs301 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step301 obs301 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs302 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step302 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then some 0 else (some 1))

def q302 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out302 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target302 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then some 0 else (some 1))

theorem complete302 (s t : Fin 2) : SOESemantics.Equivalent step302 obs302 s t ↔ q302 s=q302 t := by

  apply SOESemantics.quotient_complete step302 target302 obs302 out302 q302

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q302 s ≠ q302 t → SOESemantics.behavior step302 obs302 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step302 obs302 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs303 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step303 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then some 1 else (none))

def q303 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out303 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target303 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then some 1 else (none))

theorem complete303 (s t : Fin 2) : SOESemantics.Equivalent step303 obs303 s t ↔ q303 s=q303 t := by

  apply SOESemantics.quotient_complete step303 target303 obs303 out303 q303

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q303 s ≠ q303 t → SOESemantics.behavior step303 obs303 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step303 obs303 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs304 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step304 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then some 1 else (some 0))

def q304 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out304 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target304 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then some 1 else (some 0))

theorem complete304 (s t : Fin 2) : SOESemantics.Equivalent step304 obs304 s t ↔ q304 s=q304 t := by

  apply SOESemantics.quotient_complete step304 target304 obs304 out304 q304

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q304 s ≠ q304 t → SOESemantics.behavior step304 obs304 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step304 obs304 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs305 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step305 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then some 1 else (some 1))

def q305 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out305 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target305 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (none)) else (if s=0 then some 1 else (some 1))

theorem complete305 (s t : Fin 2) : SOESemantics.Equivalent step305 obs305 s t ↔ q305 s=q305 t := by

  apply SOESemantics.quotient_complete step305 target305 obs305 out305 q305

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q305 s ≠ q305 t → SOESemantics.behavior step305 obs305 s ([0] : List (Fin 2)) ≠ SOESemantics.behavior step305 obs305 t [0] := by decide

    intro s t h; exact ⟨[0], hw s t h⟩

def obs306 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step306 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then none else (none))

def q306 (s : Fin 2) : Fin 1 := if s=0 then 0 else (0)

def out306 (s : Fin 1) : ℕ := 1

def target306 (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a=0 then (some 0) else (none)

theorem complete306 (s t : Fin 2) : SOESemantics.Equivalent step306 obs306 s t ↔ q306 s=q306 t := by

  apply SOESemantics.quotient_complete step306 target306 obs306 out306 q306

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q306 s ≠ q306 t → SOESemantics.behavior step306 obs306 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step306 obs306 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs307 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step307 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then none else (some 0))

def q307 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out307 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target307 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then none else (some 0))

theorem complete307 (s t : Fin 2) : SOESemantics.Equivalent step307 obs307 s t ↔ q307 s=q307 t := by

  apply SOESemantics.quotient_complete step307 target307 obs307 out307 q307

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q307 s ≠ q307 t → SOESemantics.behavior step307 obs307 s ([1] : List (Fin 2)) ≠ SOESemantics.behavior step307 obs307 t [1] := by decide

    intro s t h; exact ⟨[1], hw s t h⟩

def obs308 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step308 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then none else (some 1))

def q308 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out308 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target308 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then none else (some 1))

theorem complete308 (s t : Fin 2) : SOESemantics.Equivalent step308 obs308 s t ↔ q308 s=q308 t := by

  apply SOESemantics.quotient_complete step308 target308 obs308 out308 q308

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q308 s ≠ q308 t → SOESemantics.behavior step308 obs308 s ([1] : List (Fin 2)) ≠ SOESemantics.behavior step308 obs308 t [1] := by decide

    intro s t h; exact ⟨[1], hw s t h⟩

def obs309 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step309 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then some 0 else (none))

def q309 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out309 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target309 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then some 0 else (none))

theorem complete309 (s t : Fin 2) : SOESemantics.Equivalent step309 obs309 s t ↔ q309 s=q309 t := by

  apply SOESemantics.quotient_complete step309 target309 obs309 out309 q309

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q309 s ≠ q309 t → SOESemantics.behavior step309 obs309 s ([1] : List (Fin 2)) ≠ SOESemantics.behavior step309 obs309 t [1] := by decide

    intro s t h; exact ⟨[1], hw s t h⟩

def obs310 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step310 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then some 0 else (some 0))

def q310 (s : Fin 2) : Fin 1 := if s=0 then 0 else (0)

def out310 (s : Fin 1) : ℕ := 1

def target310 (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a=0 then (some 0) else (some 0)

theorem complete310 (s t : Fin 2) : SOESemantics.Equivalent step310 obs310 s t ↔ q310 s=q310 t := by

  apply SOESemantics.quotient_complete step310 target310 obs310 out310 q310

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q310 s ≠ q310 t → SOESemantics.behavior step310 obs310 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step310 obs310 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs311 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step311 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then some 0 else (some 1))

def q311 (s : Fin 2) : Fin 1 := if s=0 then 0 else (0)

def out311 (s : Fin 1) : ℕ := 1

def target311 (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a=0 then (some 0) else (some 0)

theorem complete311 (s t : Fin 2) : SOESemantics.Equivalent step311 obs311 s t ↔ q311 s=q311 t := by

  apply SOESemantics.quotient_complete step311 target311 obs311 out311 q311

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q311 s ≠ q311 t → SOESemantics.behavior step311 obs311 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step311 obs311 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs312 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step312 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then some 1 else (none))

def q312 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out312 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target312 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then some 1 else (none))

theorem complete312 (s t : Fin 2) : SOESemantics.Equivalent step312 obs312 s t ↔ q312 s=q312 t := by

  apply SOESemantics.quotient_complete step312 target312 obs312 out312 q312

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q312 s ≠ q312 t → SOESemantics.behavior step312 obs312 s ([1] : List (Fin 2)) ≠ SOESemantics.behavior step312 obs312 t [1] := by decide

    intro s t h; exact ⟨[1], hw s t h⟩

def obs313 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step313 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then some 1 else (some 0))

def q313 (s : Fin 2) : Fin 1 := if s=0 then 0 else (0)

def out313 (s : Fin 1) : ℕ := 1

def target313 (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a=0 then (some 0) else (some 0)

theorem complete313 (s t : Fin 2) : SOESemantics.Equivalent step313 obs313 s t ↔ q313 s=q313 t := by

  apply SOESemantics.quotient_complete step313 target313 obs313 out313 q313

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q313 s ≠ q313 t → SOESemantics.behavior step313 obs313 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step313 obs313 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs314 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step314 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 0)) else (if s=0 then some 1 else (some 1))

def q314 (s : Fin 2) : Fin 1 := if s=0 then 0 else (0)

def out314 (s : Fin 1) : ℕ := 1

def target314 (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a=0 then (some 0) else (some 0)

theorem complete314 (s t : Fin 2) : SOESemantics.Equivalent step314 obs314 s t ↔ q314 s=q314 t := by

  apply SOESemantics.quotient_complete step314 target314 obs314 out314 q314

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q314 s ≠ q314 t → SOESemantics.behavior step314 obs314 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step314 obs314 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs315 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step315 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then none else (none))

def q315 (s : Fin 2) : Fin 1 := if s=0 then 0 else (0)

def out315 (s : Fin 1) : ℕ := 1

def target315 (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a=0 then (some 0) else (none)

theorem complete315 (s t : Fin 2) : SOESemantics.Equivalent step315 obs315 s t ↔ q315 s=q315 t := by

  apply SOESemantics.quotient_complete step315 target315 obs315 out315 q315

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q315 s ≠ q315 t → SOESemantics.behavior step315 obs315 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step315 obs315 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs316 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step316 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then none else (some 0))

def q316 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out316 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target316 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then none else (some 0))

theorem complete316 (s t : Fin 2) : SOESemantics.Equivalent step316 obs316 s t ↔ q316 s=q316 t := by

  apply SOESemantics.quotient_complete step316 target316 obs316 out316 q316

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q316 s ≠ q316 t → SOESemantics.behavior step316 obs316 s ([1] : List (Fin 2)) ≠ SOESemantics.behavior step316 obs316 t [1] := by decide

    intro s t h; exact ⟨[1], hw s t h⟩

def obs317 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step317 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then none else (some 1))

def q317 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out317 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target317 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then none else (some 1))

theorem complete317 (s t : Fin 2) : SOESemantics.Equivalent step317 obs317 s t ↔ q317 s=q317 t := by

  apply SOESemantics.quotient_complete step317 target317 obs317 out317 q317

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q317 s ≠ q317 t → SOESemantics.behavior step317 obs317 s ([1] : List (Fin 2)) ≠ SOESemantics.behavior step317 obs317 t [1] := by decide

    intro s t h; exact ⟨[1], hw s t h⟩

def obs318 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step318 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then some 0 else (none))

def q318 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out318 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target318 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then some 0 else (none))

theorem complete318 (s t : Fin 2) : SOESemantics.Equivalent step318 obs318 s t ↔ q318 s=q318 t := by

  apply SOESemantics.quotient_complete step318 target318 obs318 out318 q318

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q318 s ≠ q318 t → SOESemantics.behavior step318 obs318 s ([1] : List (Fin 2)) ≠ SOESemantics.behavior step318 obs318 t [1] := by decide

    intro s t h; exact ⟨[1], hw s t h⟩

def obs319 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step319 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then some 0 else (some 0))

def q319 (s : Fin 2) : Fin 1 := if s=0 then 0 else (0)

def out319 (s : Fin 1) : ℕ := 1

def target319 (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a=0 then (some 0) else (some 0)

theorem complete319 (s t : Fin 2) : SOESemantics.Equivalent step319 obs319 s t ↔ q319 s=q319 t := by

  apply SOESemantics.quotient_complete step319 target319 obs319 out319 q319

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q319 s ≠ q319 t → SOESemantics.behavior step319 obs319 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step319 obs319 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs320 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step320 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then some 0 else (some 1))

def q320 (s : Fin 2) : Fin 1 := if s=0 then 0 else (0)

def out320 (s : Fin 1) : ℕ := 1

def target320 (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a=0 then (some 0) else (some 0)

theorem complete320 (s t : Fin 2) : SOESemantics.Equivalent step320 obs320 s t ↔ q320 s=q320 t := by

  apply SOESemantics.quotient_complete step320 target320 obs320 out320 q320

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q320 s ≠ q320 t → SOESemantics.behavior step320 obs320 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step320 obs320 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs321 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step321 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then some 1 else (none))

def q321 (s : Fin 2) : Fin 2 := if s=0 then 0 else (1)

def out321 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def target321 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then some 1 else (none))

theorem complete321 (s t : Fin 2) : SOESemantics.Equivalent step321 obs321 s t ↔ q321 s=q321 t := by

  apply SOESemantics.quotient_complete step321 target321 obs321 out321 q321

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q321 s ≠ q321 t → SOESemantics.behavior step321 obs321 s ([1] : List (Fin 2)) ≠ SOESemantics.behavior step321 obs321 t [1] := by decide

    intro s t h; exact ⟨[1], hw s t h⟩

def obs322 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step322 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then some 1 else (some 0))

def q322 (s : Fin 2) : Fin 1 := if s=0 then 0 else (0)

def out322 (s : Fin 1) : ℕ := 1

def target322 (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a=0 then (some 0) else (some 0)

theorem complete322 (s t : Fin 2) : SOESemantics.Equivalent step322 obs322 s t ↔ q322 s=q322 t := by

  apply SOESemantics.quotient_complete step322 target322 obs322 out322 q322

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q322 s ≠ q322 t → SOESemantics.behavior step322 obs322 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step322 obs322 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

def obs323 (s : Fin 2) : ℕ := if s=0 then 1 else (1)

def step323 (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then (if s=0 then some 1 else (some 1)) else (if s=0 then some 1 else (some 1))

def q323 (s : Fin 2) : Fin 1 := if s=0 then 0 else (0)

def out323 (s : Fin 1) : ℕ := 1

def target323 (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a=0 then (some 0) else (some 0)

theorem complete323 (s t : Fin 2) : SOESemantics.Equivalent step323 obs323 s t ↔ q323 s=q323 t := by

  apply SOESemantics.quotient_complete step323 target323 obs323 out323 q323

  · decide

  · decide

  · have hw : ∀ s t : Fin 2, q323 s ≠ q323 t → SOESemantics.behavior step323 obs323 s ([] : List (Fin 2)) ≠ SOESemantics.behavior step323 obs323 t [] := by decide

    intro s t h; exact ⟨[], hw s t h⟩

end PerfectPower.SOEModelPackets
