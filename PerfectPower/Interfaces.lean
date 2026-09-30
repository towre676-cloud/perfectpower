import PerfectPower.ThueLocal
import PerfectPower.SqrtTwoBridges
import PerfectPower.PellGeneral

/-!
# Proved interfaces: restricted transport, composition and bounds, sequence shifts, unit exponents mod 3

* **Restricted transport** (`restricted_transport`).  An obligation is an equation *with its
  restrictions* (readout divisibility, lattice or congruence conditions).  Along a unimodular `T`,
  a restriction `R` on the source becomes its pullback `R ∘ T` on the target: every restricted
  source solution is `T (u, v)` for a target solution satisfying `R (T (u, v))`.  Emptiness of
  the *unrestricted* target implies emptiness of every restricted source.  So the existing empty
  obligations need no restriction bookkeeping, but solution-carrying ones do.
* **Composition and bound transport** (`evalF_compF_mul`, `detM_mul`, `bound_transport`).  Edges
  compose by the matrix product, with multiplicative determinant.  A coordinate bound `B` on the
  target solutions transports to `(|t₁| + |t₂|) B` on the source, row by row.
* **Sequence shifts** (`shift`, `shift_shift`, `split_prefix`, `A048624_shift_unique`).  A sequence
  is an observation together with a start.
  - Shifts compose.
  - Dropping a prefix loses exactly that prefix, and `split_prefix` reconstructs the sequence from
    `(prefix, shifted tail)`.
  - For A048624 three claims are separated. (i) The 16 listed terms equal `B_{n+2}`, a finite check
    (`A048624_terms_match`). (ii) Shift 2 is the **only** shift `s ∈ ℕ` whose first term matches
    `B_s`, by strict monotonicity of the Pell coordinate (`A048624_shift_unique`): not just among
    tested shifts. (iii) Reading the dead entry as that shifted sequence is an adopted
    interpretation; the entry's text defines nothing more.
* **Unit exponents mod 3** (`orbit_mod_three`).  Every orbit point `ε^n ρ` is `(ε³)^q (ε^r ρ)` with
  `r = n mod 3`: the orbit of `ρ` is the union of three orbits of the *cube* of the unit, from the
  seeds `ρ, ερ, ε²ρ`.  This is the finite quotient the positive-`k` branch needs.  It is only the
  exponent normalization: complete seed or ideal-class coverage, exceptional primes and the
  integral readout of each reduced branch are separate obligations (`MORDELL_BRANCH.md` §7).
-/

namespace PerfectPower.Interfaces

open PerfectPower ThueLocal

/-! ### Restricted transport -/

/-- **Restrictions pull back along unimodular substitutions.** -/
theorem restricted_transport (F : Form) (T : Mat) (hdet : detM T = 1 ∨ detM T = -1) (M : ℤ)
    (R : ℤ → ℤ → Prop) (a b : ℤ) (h : evalF F a b = M) (hR : R a b) :
    ∃ u v, evalF (compF F T) u v = M ∧
      R (T.1.1 * u + T.1.2 * v) (T.2.1 * u + T.2.2 * v) := by
  obtain ⟨u, v, huv, ha, hb⟩ := sols_transport F T hdet M a b h
  exact ⟨u, v, huv, ha ▸ hb ▸ hR⟩

/-- An empty unrestricted target empties every restricted source. -/
theorem restricted_empty (F G : Form) (T : Mat) (hdet : detM T = 1 ∨ detM T = -1)
    (hG : compF F T = G) (M : ℤ) (hempty : ∀ u v, evalF G u v ≠ M) (R : ℤ → ℤ → Prop) :
    ¬ ∃ a b, evalF F a b = M ∧ R a b := fun ⟨a, b, h, _⟩ =>
  empty_transport F G T hdet hG M hempty a b h

/-! ### Composition and bound transport -/

/-- Matrix product `T S` (apply `S`, then `T`, to the variables). -/
def mulM (T S : Mat) : Mat :=
  ((T.1.1 * S.1.1 + T.1.2 * S.2.1, T.1.1 * S.1.2 + T.1.2 * S.2.2),
   (T.2.1 * S.1.1 + T.2.2 * S.2.1, T.2.1 * S.1.2 + T.2.2 * S.2.2))

/-- **Substitutions compose**: `(F ∘ T) ∘ S = F ∘ (T S)` as functions. -/
theorem evalF_compF_mul (F : Form) (T S : Mat) (u v : ℤ) :
    evalF (compF (compF F T) S) u v = evalF (compF F (mulM T S)) u v := by
  simp only [evalF_compF, mulM]
  congr 1 <;> ring

/-- Determinants multiply, so unimodular edges compose to unimodular edges. -/
theorem detM_mul (T S : Mat) : detM (mulM T S) = detM T * detM S := by
  simp only [detM, mulM]; ring

/-- **Bound transport**: if `|u|, |v| ≤ B` then each coordinate of `T (u, v)` is at most
`(|t₁| + |t₂|) B` for its row `(t₁, t₂)`.  A solution bound for the target of an edge gives an
explicit bound for the source. -/
theorem bound_transport (t₁ t₂ u v B : ℤ) (hu : |u| ≤ B) (hv : |v| ≤ B) :
    |t₁ * u + t₂ * v| ≤ (|t₁| + |t₂|) * B := by
  calc |t₁ * u + t₂ * v| ≤ |t₁ * u| + |t₂ * v| := abs_add_le _ _
    _ = |t₁| * |u| + |t₂| * |v| := by rw [abs_mul, abs_mul]
    _ ≤ |t₁| * B + |t₂| * B := by
        gcongr
    _ = (|t₁| + |t₂|) * B := by ring

/-! ### Sequence shifts -/

/-- The sequence read from index `s` on. -/
def shift {α : Type*} (s : ℕ) (f : ℕ → α) : ℕ → α := fun n => f (n + s)

theorem shift_zero {α : Type*} (f : ℕ → α) : shift 0 f = f := rfl

/-- Shifts compose. -/
theorem shift_shift {α : Type*} (s t : ℕ) (f : ℕ → α) : shift s (shift t f) = shift (s + t) f := by
  funext n; simp only [shift]; congr 1; ring

/-- The prefix a shift drops. -/
def prefixOf {α : Type*} (s : ℕ) (f : ℕ → α) : List α := (List.range s).map f

/-- **Dropping a prefix is reversible only with the prefix**: `f` is recovered from
`(prefixOf s f, shift s f)`. -/
theorem split_prefix {α : Type*} [Inhabited α] (s : ℕ) (f : ℕ → α) (n : ℕ) :
    f n = if n < s then (prefixOf s f).getD n default else shift s f (n - s) := by
  split_ifs with h
  · simp [prefixOf, List.getD_eq_getElem?_getD, h]
  · simp only [shift]; congr 1; omega

/-- A048624's 16 listed terms (`%S`, `%T` of the committed `.seq` file). -/
def A048624_terms : List ℤ :=
  [2, 5, 12, 29, 70, 169, 408, 985, 2378, 5741, 13860, 33461, 80782, 195025, 470832, 1136689]

/-- (i) The listed terms are `B_{n+2}` (a finite check). -/
theorem A048624_terms_match :
    A048624_terms = (List.range 16).map (fun n => SqrtTwoOrbit.B (n + 2)) := by decide

/-- (ii) **Shift 2 is the only shift of the Pell coordinate matching the first term**, among all
`s ∈ ℕ`. -/
theorem A048624_shift_unique (s : ℕ) (h : SqrtTwoOrbit.B (0 + s) = 2) : s = 2 := by
  rw [zero_add] at h
  rcases s with _ | t
  · simp [SqrtTwoOrbit.B, SqrtTwoOrbit.AB] at h
  · have h1 : SqrtTwoOrbit.B (1 + 1) = 2 := by decide
    have hinj := SqrtTwoOrbit.B_mono.injective (a₁ := t) (a₂ := 1) (by simpa using h.trans h1.symm)
    omega

/-- Together: any shift of `B` reproducing the listed terms is the shift by 2. -/
theorem A048624_shift_of_terms (s : ℕ)
    (h : A048624_terms = (List.range 16).map (fun n => SqrtTwoOrbit.B (n + s))) : s = 2 :=
  A048624_shift_unique s (by
    have := congrArg (fun l => l.getD 0 0) h
    simpa [A048624_terms] using this.symm)

/-! ### Unit exponents modulo 3 -/

/-- **Every orbit point is a cube-unit power of one of three seeds**: `ε^n ρ = (ε³)^q (ε^r ρ)`,
`n = 3q + r`, `r < 3`. -/
theorem orbit_mod_three (D x₁ y₁ : ℤ) (ρ : ℤ × ℤ) (n : ℕ) :
    unitOrbit D x₁ y₁ ρ n =
      ((unitAct D x₁ y₁)^[3])^[n / 3] (unitOrbit D x₁ y₁ ρ (n % 3)) := by
  simp only [unitOrbit]
  rw [← Function.iterate_mul, ← Function.iterate_add_apply]
  congr 1
  omega

end PerfectPower.Interfaces
