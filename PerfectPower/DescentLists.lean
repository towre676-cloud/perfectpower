import PerfectPower.ThueLocal

/-!
# Descent that carries solutions

`ThueLocal.descB` proves that `F(a, b) = M` has **no** solution: every child of a split must be
empty.  Point-carrying obligations need the same split with **complete lists** at the leaves:

  `S(F, M) = p · S(F, M/p³) ∪ ⋃_λ T_λ S(G_λ, M/p^{s_λ})`,

where the zero child exists only when `p³ ∣ M`, and every primitive solution lies on a listed line
`T_λ` with `F ∘ T_λ = p^{s_λ} G_λ` (the same residue cover as `descB`).

* A node is a lifting leaf (no solution, `lvl`), a **given** leaf whose complete list is supplied
  (`KindL.given k`, the `k`-th list), or a split.
* `candL` computes the candidate list bottom-up: the zero child scaled by `p`, and each line
  child mapped by its matrix.
* **`descL_complete`**: if `descL` holds and every given leaf's list is complete, then every
  solution of every node is in its candidate list.  So the root's solutions are exactly the
  candidates that satisfy it (`root_iff`): soundness is a filter, checked by evaluation.

The given lists are hypotheses (`LeafComplete`).  For a leaf that is a Thue equation, a complete
list comes from a class theorem (`UnitBox.thue_list`, under that class's premises).
-/

namespace PerfectPower.DescentLists

open PerfectPower ThueLocal

/-- Node kinds: a lifting leaf (no solution), a leaf with a supplied list, or a split. -/
inductive KindL
  | leaf (e : ℕ)
  | given (k : ℕ)
  | split (zero : Option ℕ) (lines : List (Option ℕ × ℕ × ℕ))
  deriving DecidableEq, Repr

/-- Apply a matrix to a pair. -/
def app (T : Mat) (uv : ℤ × ℤ) : ℤ × ℤ := (T.1.1 * uv.1 + T.1.2 * uv.2, T.2.1 * uv.1 + T.2.2 * uv.2)

/-- One node's check: the same conditions as `ThueLocal.nodeB`, and a given leaf is accepted. -/
def nodeL (p : ℕ) (nodes : List (Form × ℤ × KindL)) (i : ℕ) : Bool :=
  match nodes[i]? with
  | none => false
  | some (F, M, KindL.leaf e) => decide (lvl F M p e = [])
  | some (_, _, KindL.given _) => true
  | some (F, M, KindL.split zero lines) =>
    decide (M % p = 0) &&
    (match zero with
      | none => decide (M % ((p : ℤ) ^ 3) ≠ 0)
      | some j => decide (i < j) && decide (M % ((p : ℤ) ^ 3) = 0) &&
          decide (nodes[j]?.map (fun n => (n.1, n.2.1)) = some (F, M / (p : ℤ) ^ 3))) &&
    ((List.range p).all fun a0 => (List.range p).all fun b0 =>
      decide (a0 = 0 ∧ b0 = 0) || decide (evalF F a0 b0 % p ≠ 0) ||
        lines.any fun ln => onLine p a0 b0 ln.1) &&
    lines.all fun ln =>
      decide (i < ln.2.2) && dvdF ((p : ℤ) ^ ln.2.1) (compF F (lineMat p ln.1)) &&
        decide (M % ((p : ℤ) ^ ln.2.1) = 0) &&
        decide (nodes[ln.2.2]?.map (fun n => (n.1, n.2.1)) =
          some (divF (compF F (lineMat p ln.1)) ((p : ℤ) ^ ln.2.1), M / (p : ℤ) ^ ln.2.1))

/-- The whole certificate. -/
def descL (p : ℕ) (nodes : List (Form × ℤ × KindL)) : Bool :=
  decide (0 < p) && (List.range nodes.length).all (nodeL p nodes)

/-- The candidate list of node `i` (fuel bounds the depth; children come after parents). -/
def candL (p : ℕ) (nodes : List (Form × ℤ × KindL)) (leaves : List (List (ℤ × ℤ))) :
    ℕ → ℕ → List (ℤ × ℤ)
  | 0, _ => []
  | f + 1, i =>
    match nodes[i]? with
    | none => []
    | some (_, _, KindL.leaf _) => []
    | some (_, _, KindL.given k) => leaves.getD k []
    | some (_, _, KindL.split zero lines) =>
      (match zero with
        | none => []
        | some j => (candL p nodes leaves f j).map fun uv => ((p : ℤ) * uv.1, (p : ℤ) * uv.2)) ++
      lines.flatMap fun ln => (candL p nodes leaves f ln.2.2).map (app (lineMat p ln.1))

/-- Every given leaf's list is complete. -/
def LeafComplete (nodes : List (Form × ℤ × KindL)) (leaves : List (List (ℤ × ℤ))) : Prop :=
  ∀ (i : ℕ) (F : Form) (M : ℤ) (k : ℕ), nodes[i]? = some (F, M, KindL.given k) →
    ∀ a b, evalF F a b = M → (a, b) ∈ leaves.getD k []

/-- **One node is complete given its children.** -/
theorem nodeL_step (p : ℕ) (hp : 0 < p) (nodes : List (Form × ℤ × KindL))
    (leaves : List (List (ℤ × ℤ))) (hleaf : LeafComplete nodes leaves) (f i : ℕ)
    (hi : nodeL p nodes i = true)
    (child : ∀ j : ℕ, i < j → ∀ m : Form × ℤ × KindL, nodes[j]? = some m →
      ∀ a b : ℤ, evalF m.1 a b = m.2.1 → (a, b) ∈ candL p nodes leaves f j) :
    ∀ n : Form × ℤ × KindL, nodes[i]? = some n →
      ∀ a b : ℤ, evalF n.1 a b = n.2.1 → (a, b) ∈ candL p nodes leaves (f + 1) i := by
  intro n hn a b hab
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp
  obtain ⟨F, M, kind⟩ := n
  simp only at hab
  unfold nodeL at hi
  rw [hn] at hi
  cases kind with
  | leaf e =>
    simp only [decide_eq_true_eq] at hi
    exact absurd hab (no_solution_of_lvl F M p e hp hi a b)
  | given k =>
    simp only [candL, hn]
    exact hleaf i F M k hn a b hab
  | split zero lines =>
    simp only [candL, hn, List.mem_append, List.mem_flatMap, List.mem_map]
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
      Bool.or_eq_true, List.any_eq_true] at hi
    obtain ⟨⟨⟨hMp, hz⟩, hcover⟩, hlines⟩ := hi
    by_cases hab0 : (p : ℤ) ∣ a ∧ (p : ℤ) ∣ b
    · left
      obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩⟩ := hab0
      rw [evalF_scale] at hab
      cases zero with
      | none =>
        simp only [decide_eq_true_eq] at hz
        exact absurd (by rw [← hab]; simp) hz
      | some j =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hz
        obtain ⟨⟨hij, hM3⟩, hnj⟩ := hz
        cases hnode : nodes[j]? with
        | none => rw [hnode] at hnj; simp at hnj
        | some m =>
          rw [hnode] at hnj
          simp only [Option.map_some, Option.some.injEq] at hnj
          have hm := child j hij m hnode a' b'
          rw [(Prod.mk.inj hnj).1, (Prod.mk.inj hnj).2] at hm
          dsimp only
          rw [List.mem_map]
          refine ⟨(a', b'), hm ?_, rfl⟩
          rw [← hab, Int.mul_ediv_cancel_left _ (by positivity)]
    · right
      have hA0 := Int.emod_nonneg a hpz.ne'
      have hA1 := Int.emod_lt_of_pos a hpz
      have hB0 := Int.emod_nonneg b hpz.ne'
      have hB1 := Int.emod_lt_of_pos b hpz
      have hc := hcover (a % p).toNat (by omega) (b % p).toNat (by omega)
      have ca : (((a % p).toNat : ℕ) : ℤ) = a % p := Int.toNat_of_nonneg hA0
      have cb : (((b % p).toNat : ℕ) : ℤ) = b % p := Int.toNat_of_nonneg hB0
      rcases hc with (⟨h0a, h0b⟩ | hnz) | ⟨ln, hln, hon⟩
      · exact absurd ⟨Int.dvd_of_emod_eq_zero (by omega), Int.dvd_of_emod_eq_zero (by omega)⟩ hab0
      · exfalso
        apply hnz
        rw [ca, cb]
        have := evalF_modEq F (Int.mod_modEq a p) (Int.mod_modEq b p)
        rw [hab] at this
        rw [this]; exact hMp
      · have hl := hlines ln hln
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hl
        obtain ⟨⟨⟨hil, hdv⟩, hMs⟩, hnl⟩ := hl
        obtain ⟨u, v, hu, hv⟩ : ∃ u v : ℤ, a = (lineMat p ln.1).1.1 * u + (lineMat p ln.1).1.2 * v ∧
            b = (lineMat p ln.1).2.1 * u + (lineMat p ln.1).2.2 * v := by
          obtain ⟨l?, s, j⟩ := ln
          cases l? with
          | some l =>
            simp only [onLine, decide_eq_true_eq] at hon
            rw [ca, cb] at hon
            have hmod : a ≡ l * b [ZMOD p] := by
              unfold Int.ModEq
              rw [Int.emod_emod] at hon
              rw [hon, Int.mul_emod, Int.emod_emod, ← Int.mul_emod]
            obtain ⟨c, hc⟩ := Int.ModEq.dvd hmod.symm
            exact ⟨b, c, show a = (l : ℤ) * b + (p : ℤ) * c by linarith,
              show b = 1 * b + 0 * c by ring⟩
          | none =>
            simp only [onLine, decide_eq_true_eq] at hon
            rw [cb] at hon
            rw [Int.emod_emod] at hon
            obtain ⟨w, hw⟩ := Int.dvd_of_emod_eq_zero hon
            exact ⟨a, w, show a = 1 * a + 0 * w by ring, show b = 0 * a + (p : ℤ) * w by linarith⟩
        have hT : evalF (compF F (lineMat p ln.1)) u v = M := by
          rw [evalF_compF, ← hu, ← hv, hab]
        rw [evalF_divF (by positivity) hdv] at hT
        cases hnode : nodes[ln.2.2]? with
        | none => rw [hnode] at hnl; simp at hnl
        | some m =>
          rw [hnode] at hnl
          simp only [Option.map_some, Option.some.injEq] at hnl
          have hm := child ln.2.2 hil m hnode u v
          rw [(Prod.mk.inj hnl).1, (Prod.mk.inj hnl).2] at hm
          refine ⟨ln, hln, (u, v), hm ?_, ?_⟩
          · rw [← hT, Int.mul_ediv_cancel_left _ (by positivity)]
          · simp only [app, Prod.mk.injEq]; exact ⟨hu.symm, hv.symm⟩

/-- **Completeness of a solution-carrying certificate**: with complete given leaves, every
solution of node `i` is a candidate (fuel `f ≥ length − i`). -/
theorem descL_complete (p : ℕ) (nodes : List (Form × ℤ × KindL)) (leaves : List (List (ℤ × ℤ)))
    (h : descL p nodes = true) (hleaf : LeafComplete nodes leaves) :
    ∀ f i, nodes.length - i ≤ f → ∀ n, nodes[i]? = some n →
      ∀ a b : ℤ, evalF n.1 a b = n.2.1 → (a, b) ∈ candL p nodes leaves f i := by
  simp only [descL, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨hp, hall⟩ := h
  intro f
  induction f with
  | zero =>
    intro i hi n hn
    rw [List.getElem?_eq_none (by omega)] at hn; simp at hn
  | succ f ih =>
    intro i hi n hn
    have hlt : i < nodes.length := by
      by_contra hc; push_neg at hc; rw [List.getElem?_eq_none hc] at hn; simp at hn
    exact nodeL_step p hp nodes leaves hleaf f i (hall i hlt)
      (fun j hj m hm => ih j (by omega) m hm) _ hn

/-- **The root's solutions, exactly**: `F(a, b) = M` iff `(a, b)` is a candidate satisfying it. -/
theorem root_iff (p : ℕ) (F : Form) (M : ℤ) (kind : KindL) (rest : List (Form × ℤ × KindL))
    (leaves : List (List (ℤ × ℤ))) (h : descL p ((F, M, kind) :: rest) = true)
    (hleaf : LeafComplete ((F, M, kind) :: rest) leaves) (a b : ℤ) :
    evalF F a b = M ↔ (a, b) ∈ (candL p ((F, M, kind) :: rest) leaves (rest.length + 1) 0).filter
      (fun uv => decide (evalF F uv.1 uv.2 = M)) := by
  rw [List.mem_filter, decide_eq_true_eq]
  constructor
  · intro hab
    exact ⟨descL_complete p _ leaves h hleaf _ 0 (by simp) _ rfl a b hab, hab⟩
  · exact fun h => h.2

end PerfectPower.DescentLists
