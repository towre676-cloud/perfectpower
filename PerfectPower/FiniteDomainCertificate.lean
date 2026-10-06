import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! A finite-domain transcript language. Its semantics retains the original
predicate through unions, intersections, filters and polynomial images.
Ranks are zero based; a selected value is certified by membership and rank. -/
namespace PerfectPower.FiniteDomainCertificate

/-- Finite-domain transcript syntax with exact integer semantics. -/
inductive Domain where
  | literal (values : Finset ℤ)
  | union (left right : Domain)
  | inter (left right : Domain)
  | filter (source : Domain) (predicate : ℤ → Prop) (decide : DecidablePred predicate)
  | image (source : Domain) (map : ℤ → ℤ)

/-- The original predicate denoted by a transcript. -/
def meaning : Domain → ℤ → Prop
  | .literal S, x => x ∈ S
  | .union A B, x => meaning A x ∨ meaning B x
  | .inter A B, x => meaning A x ∧ meaning B x
  | .filter A p _, x => meaning A x ∧ p x
  | .image A f, x => ∃ y, meaning A y ∧ f y = x

/-- Evaluate a transcript as a deduplicated finite set. -/
def evaluate : Domain → Finset ℤ
  | .literal S => S
  | .union A B => evaluate A ∪ evaluate B
  | .inter A B => evaluate A ∩ evaluate B
  | .filter A p hp => @Finset.filter ℤ p hp (evaluate A)
  | .image A f => (evaluate A).image f

theorem evaluate_complete (D : Domain) (x : ℤ) : x ∈ evaluate D ↔ meaning D x := by
  induction D generalizing x with
  | literal S => rfl
  | union A B ha hb => simp [evaluate, meaning, ha, hb]
  | inter A B ha hb => simp [evaluate, meaning, ha, hb]
  | filter A p hp ha => simp [evaluate, meaning, ha]
  | image A f ha => simp [evaluate, meaning, ha]

/-- Number of distinct accepted integers strictly below a value. -/
def rank (S : Finset ℤ) (x : ℤ) : ℕ := (S.filter (· < x)).card

theorem rank_strict (S : Finset ℤ) (x y : ℤ) (hx : x ∈ S) (hxy : x < y) :
    rank S x < rank S y := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro z hz
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,
      lt_trans (Finset.mem_filter.mp hz).2 hxy⟩
  · intro he
    have hmem : x ∈ S.filter (· < y) := Finset.mem_filter.mpr ⟨hx, hxy⟩
    rw [← he] at hmem
    exact (lt_irrefl x) (Finset.mem_filter.mp hmem).2

/-- The membership/rank transcript certifies a unique selected value even for
nonmonotone polynomial images, where duplicate values must be removed. -/
theorem select_unique (S : Finset ℤ) (i : ℕ) (x y : ℤ)
    (hx : x ∈ S) (hy : y ∈ S) (hrx : rank S x = i) (hry : rank S y = i) : x = y := by
  rcases lt_trichotomy x y with h | h | h
  · have := rank_strict S x y hx h
    omega
  · exact h
  · have := rank_strict S y x hy h
    omega

/-- A transcript assembled from local cells certifies the source predicate,
provided each leaf's source equivalence has been checked. -/
theorem source_select_unique (D : Domain) (P : ℤ → Prop)
    (hP : ∀ x, meaning D x ↔ P x) (i : ℕ) (x : ℤ)
    (hx : x ∈ evaluate D) (hr : rank (evaluate D) x = i) :
    P x ∧ ∀ y, P y → rank (evaluate D) y = i → y = x := by
  refine ⟨(hP x).mp ((evaluate_complete D x).mp hx), ?_⟩
  intro y hy hry
  exact select_unique (evaluate D) i y x
    ((evaluate_complete D y).mpr ((hP y).mpr hy)) hx hry hr

end PerfectPower.FiniteDomainCertificate
