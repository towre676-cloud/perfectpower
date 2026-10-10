import PerfectPower.SOESemantics
import Mathlib.Data.Rat.Lemmas
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace PerfectPower.BlastAlignment

/-- Features count literal matches, mismatches, gap openings and gap residues. -/
structure Features where
  identities : ℕ
  substitutions : ℕ
  openings : ℕ
  residues : ℕ
  deriving DecidableEq

/-- Signed rational coefficients; the gap convention counts every gap residue. -/
structure Weights where
  identities : ℚ
  substitutions : ℚ
  openings : ℚ
  residues : ℚ

 def score (f : Features) (w : Weights) : ℚ :=
  f.identities * w.identities + f.substitutions * w.substitutions +
    f.openings * w.openings + f.residues * w.residues

 def combine (f g : Features) : Features :=
  ⟨f.identities + g.identities, f.substitutions + g.substitutions,
    f.openings + g.openings, f.residues + g.residues⟩

 def shift (w d : Weights) (t : ℚ) : Weights :=
  ⟨w.identities + t * d.identities, w.substitutions + t * d.substitutions,
    w.openings + t * d.openings, w.residues + t * d.residues⟩

 theorem score_combine (f g : Features) (w : Weights) :
    score (combine f g) w = score f w + score g w := by
  simp only [score, combine, Nat.cast_add]
  ring

 theorem score_shift (f : Features) (w d : Weights) (t : ℚ) :
    score f (shift w d t) = score f w + t * score f d := by
  simp only [score, shift]
  ring

/-- A rational halfspace certificate proves pairwise optimality on a score line. -/
 theorem line_comparison (f g : Features) (w d : Weights) (t : ℚ)
    (h : 0 ≤ score f w - score g w + t * (score f d - score g d)) :
    score g (shift w d t) ≤ score f (shift w d t) := by
  rw [score_shift, score_shift]
  nlinarith

/-- Every competitor must be covered; an omitted alignment is not excluded. -/
 theorem supported_winner (candidates : List Features) (f : Features)
    (w d : Weights) (t : ℚ)
    (h : ∀ g ∈ candidates, 0 ≤ score f w - score g w + t * (score f d - score g d)) :
    ∀ g ∈ candidates, score g (shift w d t) ≤ score f (shift w d t) := by
  intro g hg
  exact line_comparison f g w d t (h g hg)

 def total : List Features → Features
  | [] => ⟨0, 0, 0, 0⟩
  | f :: fs => combine f (total fs)

/-- Exact additive path scoring, independent of any biological interpretation. -/
 theorem score_total (path : List Features) (w : Weights) :
    score (total path) w = (path.map (fun f => score f w)).sum := by
  induction path with
  | nil => simp [total, score]
  | cons f fs ih => simp [total, score_combine, ih]

/-- Strictly decreasing natural ranks bound every executable action word. -/
theorem path_length_bound {S A : Type*} (step : S → A → Option S)
    (rank : S → ℕ) (decreases : ∀ s a t, step s a = some t → rank t < rank s)
    (s t : S) (word : List A) (hrun : SOESemantics.run step s word = some t) :
    word.length ≤ rank s := by
  induction word generalizing s with
  | nil => simp
  | cons a word ih =>
    cases hs : step s a with
    | none => simp [SOESemantics.run, hs] at hrun
    | some u =>
      have hu : SOESemantics.run step u word = some t := by
        simpa [SOESemantics.run, hs] using hrun
      have hlen := ih u hu
      have hlt := decreases s a u hs
      simp only [List.length_cons]
      omega

#print axioms path_length_bound
#print axioms score_combine
#print axioms score_shift
#print axioms line_comparison
#print axioms supported_winner
#print axioms score_total
end PerfectPower.BlastAlignment
