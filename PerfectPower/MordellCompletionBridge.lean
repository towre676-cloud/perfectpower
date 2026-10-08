import Mathlib

/-! Proof interfaces for the computational Mordell completion packets.

The prime-saturation composition and finite enumeration proofs below are kernel
theorems. They do not turn an eclib status bit into a global index bound, or a
Sage list into an unbounded completeness theorem. Those inputs remain explicit.
-/
namespace PerfectPower.MordellCompletionBridge

variable {G K : Type*} [AddCommGroup G] [AddCommGroup K]

/-- Divisibility closure at one prime, in the actual point group. -/
def PrimeSaturated (H : AddSubgroup G) (p : ℕ) : Prop :=
  ∀ g : G, p • g ∈ H → g ∈ H

/-- A global bound on a positive denominator for every coset.
This is a mathematical proposition, not a receipt Boolean. -/
def BoundedIndex (H : AddSubgroup G) (B : ℕ) : Prop :=
  ∀ g : G, ∃ n : ℕ, 0 < n ∧ n ≤ B ∧ n • g ∈ H

/-- A proved finite quotient supplies a genuine global denominator bound. -/
theorem boundedIndex_of_finite_quotient (H : AddSubgroup G) [Finite (G ⧸ H)] :
    BoundedIndex H (Nat.card (G ⧸ H)) := by
  intro g
  let q : G ⧸ H := QuotientAddGroup.mk g
  refine ⟨addOrderOf q, addOrderOf_pos q,
    Nat.le_of_dvd (Nat.card_pos) (addOrderOf_dvd_natCard q), ?_⟩
  apply (QuotientAddGroup.eq_zero_iff _).mp
  change (QuotientAddGroup.mk' H) (addOrderOf q • g) = 0
  rw [map_nsmul]
  exact addOrderOf_nsmul_eq_zero q

/-- The global prime-support input includes exceptional reduction primes.
It separates existence of multiples (rank) from their possible prime factors. -/
def PrimeSupport (H : AddSubgroup G) (S : Finset ℕ) : Prop :=
  ∀ g : G, ∃ n : ℕ, 0 < n ∧ n • g ∈ H ∧
    ∀ p : ℕ, p.Prime → p ∣ n → p ∈ S

/-- Prime-saturation checks compose for an arbitrary proved prime-support set. -/
theorem mem_of_supported_multiple (H : AddSubgroup G) (S : Finset ℕ)
    (hsat : ∀ p ∈ S, p.Prime → PrimeSaturated H p)
    (n : ℕ) (hn : 0 < n)
    (hsupport : ∀ p : ℕ, p.Prime → p ∣ n → p ∈ S)
    (g : G) (hg : n • g ∈ H) : g ∈ H := by
  induction n using Nat.strong_induction_on generalizing g with
  | h n ih =>
    by_cases h1 : n = 1
    · simpa [h1] using hg
    · obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd h1
      have hpS := hsupport p hp hpn
      obtain ⟨m, hm⟩ := hpn
      have hp2 := hp.two_le
      have hm0 : 0 < m := by nlinarith
      have hmn : m < n := by nlinarith
      have hmg : m • (p • g) ∈ H := by
        simpa [smul_smul, hm, Nat.mul_comm] using hg
      have hpg : p • g ∈ H := ih m hmn hm0 (by
        intro q hq hqm
        apply hsupport q hq
        rw [hm]
        exact dvd_mul_of_dvd_right hqm p) (p • g) hmg
      exact hsat p hpS hp g hpg

/-- Rank/multiple existence, global prime support and local saturation give closure. -/
theorem eq_top_of_prime_support (H : AddSubgroup G) (S : Finset ℕ)
    (hsupport : PrimeSupport H S)
    (hsat : ∀ p ∈ S, p.Prime → PrimeSaturated H p) : H = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨n, hn, hg, hp⟩ := hsupport g
  exact mem_of_supported_multiple H S hsat n hn hp g hg

/-- Checking all primes up to a proved global bound closes every bounded multiple. -/
theorem mem_of_bounded_multiple (H : AddSubgroup G) (B : ℕ)
    (hsat : ∀ p : ℕ, p.Prime → p ≤ B → PrimeSaturated H p)
    (n : ℕ) (hn : 0 < n) (hB : n ≤ B) (g : G) (hg : n • g ∈ H) : g ∈ H := by
  induction n using Nat.strong_induction_on generalizing g with
  | h n ih =>
    by_cases h1 : n = 1
    · simpa [h1] using hg
    · obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd h1
      obtain ⟨m, hm⟩ := hpn
      have hp2 := hp.two_le
      have hm0 : 0 < m := by nlinarith
      have hmn : m < n := by nlinarith
      have hpB : p ≤ B := by nlinarith
      have hmg : m • (p • g) ∈ H := by
        simpa [smul_smul, hm, Nat.mul_comm] using hg
      have hpg : p • g ∈ H := ih m hmn hm0 (by omega) (p • g) hmg
      exact hsat p hp hpB g hpg

/-- A proved global denominator bound plus local saturation proves a full subgroup. -/
theorem eq_top_of_bounded_index (H : AddSubgroup G) (B : ℕ)
    (hindex : BoundedIndex H B)
    (hsat : ∀ p : ℕ, p.Prime → p ≤ B → PrimeSaturated H p) : H = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨n, hn, hB, hg⟩ := hindex g
  exact mem_of_bounded_multiple H B hsat n hn hB g hg

/-- An exact homomorphic reduction obstruction excludes rational divisibility. -/
theorem not_divisible_of_reduction (f : G →+ K) (p : ℕ) (g : G)
    (hlocal : ¬ ∃ z : K, p • z = f g) : ¬ ∃ z : G, p • z = g := by
  rintro ⟨z, hz⟩
  apply hlocal
  refine ⟨f z, ?_⟩
  rw [← f.map_nsmul, hz]

/-- Local separation from p times the reduced subgroup implies p-saturation.
The reduction maps and their relation to the rational point group are premises. -/
theorem prime_saturated_of_reduction_separation (H : AddSubgroup G) (p : ℕ)
    (hsep : ∀ g : G, g ∉ H → ∃ f : G →+ K,
      ∀ h : G, h ∈ H → f h ≠ p • f g) : PrimeSaturated H p := by
  intro g hg
  by_contra hnot
  obtain ⟨f, hf⟩ := hsep g hnot
  exact hf (p • g) hg (f.map_nsmul g p)

/-- An exhaustive finite box, independent of the algorithm proposing its bound. -/
def integralBox (k X Y : ℤ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-X) X).product (Finset.Icc (-Y) Y)).filter
    fun xy => xy.2 ^ 2 = xy.1 ^ 3 + k

/-- The finite enumeration is complete exactly within its declared coordinate box. -/
theorem mem_integralBox_iff (k X Y x y : ℤ) :
    (x, y) ∈ integralBox k X Y ↔
      -X ≤ x ∧ x ≤ X ∧ -Y ≤ y ∧ y ≤ Y ∧ y ^ 2 = x ^ 3 + k := by
  simp [integralBox, Finset.mem_product, and_assoc]

/-- A proved global coordinate bound upgrades finite enumeration to completeness. -/
theorem integralBox_complete (k X Y : ℤ)
    (hbound : ∀ x y : ℤ, y ^ 2 = x ^ 3 + k →
      -X ≤ x ∧ x ≤ X ∧ -Y ≤ y ∧ y ≤ Y) :
    ∀ x y : ℤ, y ^ 2 = x ^ 3 + k → (x, y) ∈ integralBox k X Y := by
  intro x y hxy
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hbound x y hxy
  exact (mem_integralBox_iff k X Y x y).mpr ⟨hx0, hx1, hy0, hy1, hxy⟩

/-- A list matching the finite enumeration inherits completeness from a global bound. -/
theorem integralList_complete (k X Y : ℤ) (L : Finset (ℤ × ℤ))
    (hbound : ∀ x y : ℤ, y ^ 2 = x ^ 3 + k →
      -X ≤ x ∧ x ≤ X ∧ -Y ≤ y ∧ y ≤ Y)
    (henum : integralBox k X Y = L) :
    ∀ x y : ℤ, y ^ 2 = x ^ 3 + k → (x, y) ∈ L := by
  rw [← henum]
  exact integralBox_complete k X Y hbound

end PerfectPower.MordellCompletionBridge
