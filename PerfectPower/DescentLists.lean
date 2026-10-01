import PerfectPower.ThueLocal

/-!
# Descent that carries solutions

`ThueLocal.descB` proves that `F(a, b) = M` has **no** solution: every child of a split must be
empty.  Point-carrying obligations need the same split with **complete lists** at the leaves.  At a
split node with prime `p ∣ M`,

  `S(F, M) = 1_{p³ ∣ M} · p S(F, M/p³) ∪ ⋃_λ T_λ S(G_λ, M/p^{s_λ})`,

where every primitive solution lies on a listed line `T_λ` with `F ∘ T_λ = p^{s_λ} G_λ` (the
residue cover of `descB`).

* **Every node carries its own prime.**  A split uses its prime `p`.  A lifting leaf
  (`KindL.leaf q e`) is empty modulo `q^e` for its own `q`.  This matches the measured descent
  (`python/descent_residual.py`), which splits at the least prime of the current right side and
  prunes children by lifting at other primes.
* A **given** leaf `KindL.given c T Tinv s` cites a source equation `sources[c] = (F₀, L₀)` with
  `F₀ = 1 ⇒ (a, b) ∈ L₀`.  The checker verifies `F₀ ∘ T = s · G`, `M = s = ±1` and
  `Tinv · T = I`.  The leaf's list is then `Tinv L₀`, the source list carried back.
* `candL` composes the candidate list bottom-up: the zero child scaled by `p`, and each line child
  mapped by its matrix.
* **`root_iff`**: if `descL` holds and the sources are complete (`SourcesComplete`), then the
  root's solutions are exactly `rootSet`.  This is the candidate `Finset` (duplicates from
  overlapping branches removed), filtered by evaluation.
-/

namespace PerfectPower.DescentLists

open PerfectPower ThueLocal

/-- Node kinds: a lifting leaf at prime `q` (no solution), a leaf carried from a source equation,
or a split at prime `p`. -/
inductive KindL
  | leaf (q e : ℕ)
  | given (c : ℕ) (T Tinv : Mat) (s : ℤ)
  | split (p : ℕ) (zero : Option ℕ) (lines : List (Option ℕ × ℕ × ℕ))
  deriving DecidableEq, Repr

/-- Apply a matrix to a pair. -/
def app (T : Mat) (uv : ℤ × ℤ) : ℤ × ℤ := (T.1.1 * uv.1 + T.1.2 * uv.2, T.2.1 * uv.1 + T.2.2 * uv.2)

/-- The matrix product. -/
def mulM (S T : Mat) : Mat :=
  ((S.1.1 * T.1.1 + S.1.2 * T.2.1, S.1.1 * T.1.2 + S.1.2 * T.2.2),
   (S.2.1 * T.1.1 + S.2.2 * T.2.1, S.2.1 * T.1.2 + S.2.2 * T.2.2))

/-- `s · G`, coefficientwise. -/
def scaleF (s : ℤ) (G : Form) : Form := (s * G.1, s * G.2.1, s * G.2.2.1, s * G.2.2.2)

lemma app_mulM (S T : Mat) (x : ℤ × ℤ) : app S (app T x) = app (mulM S T) x := by
  simp only [app, mulM, Prod.mk.injEq]; constructor <;> ring

lemma evalF_scaleF (s : ℤ) (G : Form) (u v : ℤ) : evalF (scaleF s G) u v = s * evalF G u v := by
  simp only [evalF, scaleF]; ring

/-- One node's check. -/
def nodeL (sources : List (Form × List (ℤ × ℤ))) (nodes : List (Form × ℤ × KindL)) (i : ℕ) : Bool :=
  match nodes[i]? with
  | none => false
  | some (F, M, KindL.leaf q e) => decide (0 < q) && decide (lvl F M q e = [])
  | some (F, M, KindL.given c T Tinv s) =>
    decide ((sources[c]?.map fun x => compF x.1 T) = some (scaleF s F)) &&
      decide (M = s) && decide (s = 1 ∨ s = -1) && decide (mulM Tinv T = ((1, 0), (0, 1)))
  | some (F, M, KindL.split p zero lines) =>
    decide (0 < p) && decide (M % p = 0) &&
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
def descL (sources : List (Form × List (ℤ × ℤ))) (nodes : List (Form × ℤ × KindL)) : Bool :=
  (List.range nodes.length).all (nodeL sources nodes)

/-- The candidate list of node `i` (fuel bounds the depth; children come after parents). -/
def candL (sources : List (Form × List (ℤ × ℤ))) (nodes : List (Form × ℤ × KindL)) :
    ℕ → ℕ → List (ℤ × ℤ)
  | 0, _ => []
  | f + 1, i =>
    match nodes[i]? with
    | none => []
    | some (_, _, KindL.leaf _ _) => []
    | some (_, _, KindL.given c _ Tinv _) => ((sources[c]?.map Prod.snd).getD []).map (app Tinv)
    | some (_, _, KindL.split p zero lines) =>
      (match zero with
        | none => []
        | some j => (candL sources nodes f j).map fun uv => ((p : ℤ) * uv.1, (p : ℤ) * uv.2)) ++
      lines.flatMap fun ln => (candL sources nodes f ln.2.2).map (app (lineMat p ln.1))

/-- Every source list is complete for its equation `F₀ = 1`. -/
def SourcesComplete (sources : List (Form × List (ℤ × ℤ))) : Prop :=
  ∀ (c : ℕ) (F : Form) (L : List (ℤ × ℤ)), sources[c]? = some (F, L) →
    ∀ a b, evalF F a b = 1 → (a, b) ∈ L

/-- **One node is complete given its children.** -/
theorem nodeL_step (sources : List (Form × List (ℤ × ℤ))) (hsrc : SourcesComplete sources)
    (nodes : List (Form × ℤ × KindL)) (f i : ℕ) (hi : nodeL sources nodes i = true)
    (child : ∀ j : ℕ, i < j → ∀ m : Form × ℤ × KindL, nodes[j]? = some m →
      ∀ a b : ℤ, evalF m.1 a b = m.2.1 → (a, b) ∈ candL sources nodes f j) :
    ∀ n : Form × ℤ × KindL, nodes[i]? = some n →
      ∀ a b : ℤ, evalF n.1 a b = n.2.1 → (a, b) ∈ candL sources nodes (f + 1) i := by
  intro n hn a b hab
  obtain ⟨F, M, kind⟩ := n
  simp only at hab
  unfold nodeL at hi
  rw [hn] at hi
  cases kind with
  | leaf q e =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hi
    exact absurd hab (no_solution_of_lvl F M q e hi.1 hi.2 a b)
  | given c T Tinv s =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hi
    obtain ⟨⟨⟨hF, hM⟩, hs⟩, hinv⟩ := hi
    simp only [candL, hn]
    cases hc : sources[c]? with
    | none => rw [hc] at hF; simp at hF
    | some x =>
      rw [hc] at hF
      simp only [Option.map_some, Option.some.injEq] at hF
      obtain ⟨F0, L0⟩ := x
      simp only [Option.map_some, Option.getD_some, List.mem_map]
      have h1 : evalF F0 (app T (a, b)).1 (app T (a, b)).2 = 1 := by
        have := evalF_compF F0 T a b
        rw [hF, evalF_scaleF, hab, hM] at this
        simp only [app]
        rcases hs with rfl | rfl <;> simp_all
      refine ⟨app T (a, b), hsrc c F0 L0 hc _ _ h1, ?_⟩
      rw [app_mulM, hinv]; simp [app]
  | split p zero lines =>
    simp only [candL, hn, List.mem_append, List.mem_flatMap, List.mem_map]
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
      Bool.or_eq_true, List.any_eq_true] at hi
    obtain ⟨⟨⟨⟨hp, hMp⟩, hz⟩, hcover⟩, hlines⟩ := hi
    have hpz : (0 : ℤ) < p := by exact_mod_cast hp
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

/-- **Completeness of a solution-carrying certificate**: with complete sources, every solution of
node `i` is a candidate (fuel `f ≥ length − i`). -/
theorem descL_complete (sources : List (Form × List (ℤ × ℤ))) (hsrc : SourcesComplete sources)
    (nodes : List (Form × ℤ × KindL)) (h : descL sources nodes = true) :
    ∀ f i, nodes.length - i ≤ f → ∀ n, nodes[i]? = some n →
      ∀ a b : ℤ, evalF n.1 a b = n.2.1 → (a, b) ∈ candL sources nodes f i := by
  simp only [descL, List.all_eq_true, List.mem_range] at h
  intro f
  induction f with
  | zero =>
    intro i hi n hn
    rw [List.getElem?_eq_none (by omega)] at hn; simp at hn
  | succ f ih =>
    intro i hi n hn
    have hlt : i < nodes.length := by
      by_contra hc; push_neg at hc; rw [List.getElem?_eq_none hc] at hn; simp at hn
    exact nodeL_step sources hsrc nodes f i (h i hlt)
      (fun j hj m hm => ih j (by omega) m hm) _ hn

/-- The root's solution set: the candidates, without duplicates, that satisfy the root. -/
def rootSet (sources : List (Form × List (ℤ × ℤ))) (F : Form) (M : ℤ) (kind : KindL)
    (rest : List (Form × ℤ × KindL)) : Finset (ℤ × ℤ) :=
  ((candL sources ((F, M, kind) :: rest) (rest.length + 1) 0).toFinset).filter
    (fun uv => evalF F uv.1 uv.2 = M)

/-- **The root's solutions, exactly**: `F(a, b) = M` iff `(a, b) ∈ rootSet`, a `Finset`, so its
cardinality is the number of solutions. -/
theorem root_iff (sources : List (Form × List (ℤ × ℤ))) (hsrc : SourcesComplete sources)
    (F : Form) (M : ℤ) (kind : KindL) (rest : List (Form × ℤ × KindL))
    (h : descL sources ((F, M, kind) :: rest) = true) (a b : ℤ) :
    evalF F a b = M ↔ (a, b) ∈ rootSet sources F M kind rest := by
  rw [rootSet, Finset.mem_filter, List.mem_toFinset]
  constructor
  · intro hab
    exact ⟨descL_complete sources hsrc _ h _ 0 (by simp) _ rfl a b hab, hab⟩
  · exact fun h => h.2

/-- A source given by a class theorem `F₀ = 1 ↔ (a, b) ∈ L₀` is complete. -/
lemma sources_cons {F0 : Form} {L0 : List (ℤ × ℤ)} {rest : List (Form × List (ℤ × ℤ))}
    (h0 : ∀ a b, evalF F0 a b = 1 → (a, b) ∈ L0) (hr : SourcesComplete rest) :
    SourcesComplete ((F0, L0) :: rest) := by
  intro c F L hc
  cases c with
  | zero => simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hc
            obtain ⟨rfl, rfl⟩ := hc; exact h0
  | succ c => exact hr c F L (by simpa using hc)

lemma sources_nil : SourcesComplete [] := by
  intro c F L hc; simp at hc

end PerfectPower.DescentLists
