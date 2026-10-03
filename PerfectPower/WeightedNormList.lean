import PerfectPower.RankOneNorm
import PerfectPower.WeightedSkolem

/-! Complete finite lists for nonempty norm orbits, with checked bounds in both directions. -/
namespace PerfectPower.WeightedNormList
open UnitBox UnitPremises RankOne NormRepProof

theorem bound_of_data {p : ℕ} [Fact p.Prime] (hp3 : 3 ≤ p)
    (P Q : ℤ) (g γ : Z3) {M : ℕ} (hM : 0 < M)
    (D : Matrix (Fin 3) (Fin 3) ℤ) (hA : Mx P Q g ^ M = 1+p • D)
    (hcls : ∀ r, r < M → ¬ (p : ℤ) ∣ (Mx P Q g ^ r * Mx P Q γ) 2 0 ∨
      ((Mx P Q g ^ r * Mx P Q γ) 2 0 = 0 ∧
        ¬ (p : ℤ) ∣ (D * (Mx P Q g ^ r * Mx P Q γ)) 2 0))
    (n : ℕ) (hn : (mul P Q γ (pow P Q g n)).2.2 = 0) : n < M := by
  apply WeightedSkolem.weighted_corner_zeros hp3 hM hA hcls n
  rw [← Mx_pow,← Mx_mul,mul_comm', (Mx_col P Q _).2.2]
  exact hn

def candidates (P Q : ℤ) (η ε : Z3) (L : List Z3) (M M' : ℕ) : List Z3 :=
  L.flatMap fun γ =>
    ((List.range M).map fun n => mul P Q γ (pow P Q η n)) ++
    ((List.range M').map fun n => mul P Q γ (pow P Q ε n))

def solutions (P Q : ℤ) (N : ℕ) (η ε : Z3) (L : List Z3) (M M' : ℕ) : List Z3 :=
  (candidates P Q η ε L M M').filter fun w =>
    decide ((nrm P Q w = N ∨ nrm P Q w = -N) ∧ w.2.2 = 0)

theorem complete (P Q : ℤ) (N : ℕ) (η ε : Z3) (L : List Z3) (M M' : ℕ)
    (hgen : ∀ w, nrm P Q w = N ∨ nrm P Q w = -N →
      ∃ n : ℤ, ∃ γ ∈ L, w = mul P Q γ (zp P Q η ε n))
    (hforward : ∀ γ ∈ L, ∀ n, (mul P Q γ (pow P Q η n)).2.2 = 0 → n < M)
    (hbackward : ∀ γ ∈ L, ∀ n, (mul P Q γ (pow P Q ε n)).2.2 = 0 → n < M')
    (w : Z3) :
    ((nrm P Q w = N ∨ nrm P Q w = -N) ∧ w.2.2 = 0) ↔
      w ∈ solutions P Q N η ε L M M' := by
  simp only [solutions,List.mem_filter,decide_eq_true_eq]
  constructor
  · intro hw
    refine ⟨?_,hw⟩
    obtain ⟨n,γ,hγ,rfl⟩ := hgen w hw.1
    simp only [candidates,List.mem_flatMap,List.mem_append,List.mem_map,List.mem_range]
    refine ⟨γ,hγ,?_⟩
    unfold zp at *
    split_ifs at * with hn
    · exact Or.inl ⟨n.toNat,hforward γ hγ _ hw.2,rfl⟩
    · exact Or.inr ⟨(-n).toNat,hbackward γ hγ _ hw.2,rfl⟩
  · exact And.right

theorem complete_of_cert {P Q : ℤ} {N : ℕ} {η ε : Z3} {L : List Z3}
    {c : Cert} {R0 : ℚ} {M M' : ℕ}
    (h1 : mul P Q η ε = (1,0,0)) (h2 : mul P Q ε η = (1,0,0))
    (hnη : nrm P Q η = 1) (hnε : nrm P Q ε = 1)
    (hc : RankOneNorm.condNB P Q η c N R0 = true)
    (hbox : RankOneNorm.slabNB P Q c N R0 L = true) (hN : 0 < N)
    (hforward : ∀ γ ∈ L, ∀ n, (mul P Q γ (pow P Q η n)).2.2 = 0 → n < M)
    (hbackward : ∀ γ ∈ L, ∀ n, (mul P Q γ (pow P Q ε n)).2.2 = 0 → n < M')
    (w : Z3) :
    ((nrm P Q w = N ∨ nrm P Q w = -N) ∧ w.2.2 = 0) ↔
      w ∈ solutions P Q N η ε L M M' :=
  complete P Q N η ε L M M'
    (RankOneNorm.normN_eq h1 h2 hnη hnε hc hbox hN) hforward hbackward w
end PerfectPower.WeightedNormList
