import PerfectPower.PellExact
import PerfectPower.RadicalAsymp
import PerfectPower.ProfileG
import PerfectPower.Rigid
import Mathlib.Algebra.Squarefree.Basic

namespace PerfectPower

open Polynomial

/-! ### The atlas interface: exact counts for the infinite types, an explicit premise for the rest

Input a polynomial and an exponent; the atlas gives one of

* **power type**: `F = G^d` over `ℤ`, every `n` is a hit (`atlas_power`), or `F = c G^d` with `c`
  not a `d`-th power, finitely many hits (`power_type_finite`);
* **radical type**: `A(N) = κ N^{1/t} + O(1)` with `κ = (R/v)(v/z₀)^{1/t}` (`atlas_radical`, from
  `radical_asymptotic_int`; `κ = 0` exactly when the final congruence modulo `v` has no residue);
* **Pell type**: `A(N) = κ log N + O(1)` with `κ = (∑_ρ g_ρ / P_ρ) / log ε` over the canonical
  orbit roots (`atlas_pell`, from `PellExact.pell_exact_count`);
* **finite type**: finitely many hits, *assuming* the precisely stated premise
  `SuperellipticSiegel` (`atlas_finite`).  That premise is Siegel's theorem applied to the curve
  `y^d = F(x)` through the geometric half of Theorem G (Kummer theory and Riemann–Hurwitz for the
  normalisation).  Neither is formalised; the combinatorial half (`chi_neg_iff`) is.

The reductions from a general `F` to the normalised radical family `c (v n - u)^r G(n)^d` and to the
quadratic Pell family (Theorems B and C of the research notes) are paper proofs; the theorems below
start from the normalised forms. -/

/-- A squarefree (Yun) decomposition `F = c ∏_j S_j^j`, with `S_j` squarefree and pairwise coprime;
the multiplicity profile lists `j` once for each root of `S_j` (i.e. `deg S_j` times). -/
structure YunDecomposition (F : ℤ[X]) where
  /-- The leading factor. -/
  lead : ℤ
  /-- `part j` is the product of the roots of multiplicity `j` (index from `1`). -/
  part : ℕ → Polynomial ℤ
  /-- Only multiplicities `1, …, m` occur. -/
  m : ℕ
  lead_ne : lead ≠ 0
  part_sq : ∀ j, Squarefree (part j)
  part_cop : ∀ i j, i ≠ j → IsCoprime (part i) (part j)
  eq_prod : F = Polynomial.C lead * ∏ j ∈ Finset.range m, part (j + 1) ^ (j + 1)

/-- The multiplicity profile of a Yun decomposition. -/
def YunDecomposition.profile {F : ℤ[X]} (Y : YunDecomposition F) : List ℕ :=
  (List.range Y.m).flatMap fun j => List.replicate (Y.part (j + 1)).natDegree (j + 1)

/-- **The premise for the finite type**: for every polynomial and exponent whose multiplicity
profile gives a negative Euler characteristic `χ = d'(1 - S)`, the hit set is finite.  This is
Siegel's theorem (standard form) for the affine curve `y^d = F(x)`, composed with the geometric
half of Theorem G.  It is stated here as a hypothesis, never as an axiom. -/
def SuperellipticSiegel : Prop :=
  ∀ (F : ℤ[X]) (Y : YunDecomposition F) (d : ℕ), 2 ≤ d → chiInt d Y.profile < 0 →
    (hitSet (fun n => F.eval (n : ℤ)) d 0).Finite

/-- **Finite type.**  Under `SuperellipticSiegel`, every profile that is not of power, radical or
Pell type has finitely many hits. -/
theorem atlas_finite (hS : SuperellipticSiegel) {F : ℤ[X]} (Y : YunDecomposition F) {d : ℕ}
    (hd : 2 ≤ d) (hex : exceptionalProfile (Y.profile.map (tOf d)) = false) :
    (hitSet (fun n => F.eval (n : ℤ)) d 0).Finite :=
  hS F Y d hd ((chi_neg_iff (by omega) Y.profile).mpr hex)

/-- **Power type.**  If `F = G^d` over `ℤ`, every index is a hit. -/
theorem atlas_power {d : ℕ} {F G : ℤ[X]} (h : F = G ^ d) (n : ℕ) : IsHit d (F.eval (n : ℤ)) :=
  ⟨G.eval (n : ℤ), by rw [h, eval_pow]⟩

open scoped Classical in
/-- **Radical type** (normalised form), re-exported: see `radical_asymptotic_int`. -/
theorem atlas_radical {c z₀ r d u v Z : ℕ} (hd : 0 < d) (hc : c ≠ 0) (hz₀ : z₀ ≠ 0)
    (hv : 0 < v) (h₀ : ∃ w : ℕ, c * z₀ ^ r = w ^ d)
    (hmin : ∀ p, z₀.factorization p < d / Nat.gcd r d) (G : ℕ → ℤ)
    (hG : ∀ N, (Finset.filter (fun n => G n = 0) (Finset.Icc 1 N)).card ≤ Z) :
    ∃ κ K : ℝ, 0 ≤ κ ∧ ∀ N : ℕ,
      |((Finset.filter (fun n : ℕ => IsHit d ((c : ℤ) * ((v : ℤ) * n - u) ^ r * G n ^ d))
          (Finset.Icc 1 N)).card : ℝ) - κ * (N : ℝ) ^ (((d / Nat.gcd r d : ℕ) : ℝ)⁻¹)| ≤ K := by
  classical
  set t := d / Nat.gcd r d
  set R := (Finset.filter (fun w => v ∣ z₀ * w ^ t + u) (Finset.Icc 1 v)).card
  refine ⟨(R : ℝ) / v * ((v : ℝ) / z₀) ^ ((t : ℝ)⁻¹),
    2 * R + (R : ℝ) / v * (((u : ℝ) / z₀) ^ ((t : ℝ)⁻¹) + 1) + u + Z, by positivity, fun N => ?_⟩
  have := radical_asymptotic_int (u := u) hd hc hz₀ hv h₀ hmin G hG N
  simp only at this
  convert this using 3

open scoped Classical in
/-- **Pell type** (quadratic form), re-exported: see `PellExact.pell_exact_count`. -/
theorem atlas_pell {A B C u v : ℤ} (hA : 0 < A) (hu1 : 1 < u) (hv : 0 < v)
    (hu : u ^ 2 - 4 * A * v ^ 2 = 1) :
    ∃ κ K : ℝ, 0 ≤ κ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      |((Finset.filter (fun n : ℕ => IsHit 2 (A * (n : ℤ) ^ 2 + B * n + C))
          (Finset.Icc 1 N)).card : ℝ) - κ * Real.log N| ≤ K := by
  classical
  obtain ⟨R, P, g, -, -, -, K, N₀, hK⟩ := PellExact.pell_exact_count (B := B) (C := C) hA hu1 hv hu
  refine ⟨(∑ ρ ∈ R, (g ρ : ℝ) / P ρ) / Real.log (PellExact.eps (4 * A) u v), K, ?_, N₀, ?_⟩
  · apply div_nonneg (Finset.sum_nonneg fun ρ _ => by positivity)
    exact (Real.log_pos (PellExact.one_lt_eps (D := 4 * A) hu1 hv.le)).le
  · intro N hN
    convert hK N hN using 3

end PerfectPower
