import Mathlib.Data.Int.GCD
import Mathlib.Tactic

/-!
# Binary cubic equations: unimodular transport and p-adic lifting obstructions

A node of the Thue workload is an equation `F(a, b) = M` for an integral binary cubic form
`F = (c₀, c₁, c₂, c₃)`, `F(a, b) = c₀ a³ + c₁ a² b + c₂ a b² + c₃ b³`.

* **Transport** (`compF`, `evalF_compF`, `sols_transport`, `empty_transport`).  For
  `T ∈ GL₂(ℤ)` (`det T = ± 1`) put `G = F ∘ T`.  Then `(u, v) ↦ T (u, v)` is a bijection from the
  solutions of `G = M` onto those of `F = M`, with inverse `T⁻¹` (integral because `det T = ± 1`).
  The certificate is the matrix and the coefficient identity `compF F T = G`, checked by
  evaluation: no search is repeated.  In particular emptiness transports.
* **p-adic lifting** (`lvl`, `mem_lvl`, `no_solution_of_lvl`).  `lvl F M p e` lists the residue
  pairs mod `p^e` with `F ≡ M (mod p^e)`, computed level by level: each pair mod `p^e` lifts to
  the `p²` pairs above it, and a lift is kept when the congruence holds mod `p^(e+1)`.  Every
  integral solution reduces into every level (`mem_lvl`), so an empty level proves that
  `F(a, b) = M` has **no integral solution**.  The tree is recomputed by the kernel; nothing
  from the search is trusted.
-/

namespace PerfectPower.ThueLocal

/-- A binary cubic form `(c₀, c₁, c₂, c₃)`. -/
abbrev Form := ℤ × ℤ × ℤ × ℤ

/-- `F(a, b) = c₀ a³ + c₁ a² b + c₂ a b² + c₃ b³`. -/
def evalF (F : Form) (a b : ℤ) : ℤ :=
  F.1 * a ^ 3 + F.2.1 * a ^ 2 * b + F.2.2.1 * a * b ^ 2 + F.2.2.2 * b ^ 3

/-- A `2 × 2` integer matrix `((t₁₁, t₁₂), (t₂₁, t₂₂))`. -/
abbrev Mat := (ℤ × ℤ) × (ℤ × ℤ)

/-- The determinant of a `2 × 2` integer matrix. -/
def detM (T : Mat) : ℤ := T.1.1 * T.2.2 - T.1.2 * T.2.1

/-- The coefficients of `F(t₁₁ u + t₁₂ v, t₂₁ u + t₂₂ v)`. -/
def compF (F : Form) (T : Mat) : Form :=
  let (c0, c1, c2, c3) := F
  let ((x, y), (z, w)) := T
  (c0 * x ^ 3 + c1 * x ^ 2 * z + c2 * x * z ^ 2 + c3 * z ^ 3,
   3 * c0 * x ^ 2 * y + c1 * (x ^ 2 * w + 2 * x * y * z) + c2 * (2 * x * z * w + y * z ^ 2) +
     3 * c3 * z ^ 2 * w,
   3 * c0 * x * y ^ 2 + c1 * (2 * x * y * w + y ^ 2 * z) + c2 * (x * w ^ 2 + 2 * y * z * w) +
     3 * c3 * z * w ^ 2,
   c0 * y ^ 3 + c1 * y ^ 2 * w + c2 * y * w ^ 2 + c3 * w ^ 3)

theorem evalF_compF (F : Form) (T : Mat) (u v : ℤ) :
    evalF (compF F T) u v = evalF F (T.1.1 * u + T.1.2 * v) (T.2.1 * u + T.2.2 * v) := by
  obtain ⟨c0, c1, c2, c3⟩ := F
  obtain ⟨⟨x, y⟩, ⟨z, w⟩⟩ := T
  simp only [evalF, compF]
  ring

/-- **Transport of solutions** along a unimodular substitution: every solution of `F = M` is
`T (u, v)` for a solution `(u, v)` of `F ∘ T = M`. -/
theorem sols_transport (F : Form) (T : Mat) (hdet : detM T = 1 ∨ detM T = -1) (M a b : ℤ)
    (h : evalF F a b = M) :
    ∃ u v, evalF (compF F T) u v = M ∧ a = T.1.1 * u + T.1.2 * v ∧ b = T.2.1 * u + T.2.2 * v := by
  obtain ⟨⟨x, y⟩, ⟨z, w⟩⟩ := T
  simp only [detM] at hdet
  -- the inverse is `det · ((w, -y), (-z, x))`
  set d := x * w - y * z
  have hd2 : d * d = 1 := by rcases hdet with h | h <;> rw [h] <;> norm_num
  refine ⟨d * (w * a - y * b), d * (-z * a + x * b), ?_, ?_, ?_⟩
  · rw [evalF_compF]
    have e1 : x * (d * (w * a - y * b)) + y * (d * (-z * a + x * b)) = a := by
      linear_combination (a) * hd2
    have e2 : z * (d * (w * a - y * b)) + w * (d * (-z * a + x * b)) = b := by
      linear_combination (b) * hd2
    simp only at e1 e2 ⊢
    rw [e1, e2, h]
  · linear_combination (-a) * hd2
  · linear_combination (-b) * hd2

/-- **Emptiness transports**: if `F ∘ T = G` has no solution, neither has `F = M`. -/
theorem empty_transport (F G : Form) (T : Mat) (hdet : detM T = 1 ∨ detM T = -1)
    (hG : compF F T = G) (M : ℤ) (hempty : ∀ u v, evalF G u v ≠ M) (a b : ℤ) :
    evalF F a b ≠ M := by
  intro h
  obtain ⟨u, v, huv, -, -⟩ := sols_transport F T hdet M a b h
  rw [hG] at huv
  exact hempty u v huv

/-! ### p-adic lifting -/

lemma evalF_modEq (F : Form) {a b a' b' m : ℤ} (ha : a ≡ a' [ZMOD m]) (hb : b ≡ b' [ZMOD m]) :
    evalF F a b ≡ evalF F a' b' [ZMOD m] := by
  unfold evalF
  refine (((((Int.ModEq.refl _).mul (ha.pow 3))).add
    (((Int.ModEq.refl _).mul (ha.pow 2)).mul hb)).add
    (((Int.ModEq.refl _).mul ha).mul (hb.pow 2))).add ((Int.ModEq.refl _).mul (hb.pow 3))

/-- The lifts of one residue pair mod `p^e` that satisfy the congruence mod `p^(e+1)`. -/
def liftAt (F : Form) (M : ℤ) (p e : ℕ) (ab : ℕ × ℕ) : List (ℕ × ℕ) :=
  (List.range p).flatMap fun i => (List.range p).filterMap fun j =>
    if (evalF F ((ab.1 + p ^ e * i : ℕ) : ℤ) ((ab.2 + p ^ e * j : ℕ) : ℤ) - M) %
        ((p : ℤ) ^ (e + 1)) = 0
    then some (ab.1 + p ^ e * i, ab.2 + p ^ e * j) else none

/-- Residue pairs mod `p^e` with `F ≡ M (mod p^e)`, lifted level by level. -/
def lvl (F : Form) (M : ℤ) (p : ℕ) : ℕ → List (ℕ × ℕ)
  | 0 => [(0, 0)]
  | e + 1 => (lvl F M p e).flatMap (liftAt F M p e)

/-- One lifting step on residues: `a mod p^(e+1) = a mod p^e + p^e i` with `i < p`. -/
lemma lift_step (p e : ℕ) (hp : 0 < p) (a : ℤ) :
    ∃ i : ℕ, i < p ∧ (a % ((p : ℤ) ^ (e + 1))).toNat = (a % ((p : ℤ) ^ e)).toNat + p ^ e * i := by
  have hpe : (0 : ℤ) < (p : ℤ) ^ e := by positivity
  have hpe1 : (0 : ℤ) < (p : ℤ) ^ (e + 1) := by positivity
  set R := a % ((p : ℤ) ^ (e + 1))
  have hR0 : 0 ≤ R := Int.emod_nonneg _ hpe1.ne'
  have hR1 : R < (p : ℤ) ^ (e + 1) := Int.emod_lt_of_pos _ hpe1
  have hdvd : (p : ℤ) ^ e ∣ (p : ℤ) ^ (e + 1) := pow_dvd_pow _ (Nat.le_succ e)
  have hmod : R % ((p : ℤ) ^ e) = a % ((p : ℤ) ^ e) := Int.emod_emod_of_dvd a hdvd
  have hsplit := Int.emod_add_ediv R ((p : ℤ) ^ e)
  set i := R / ((p : ℤ) ^ e) with hi
  have hi0 : 0 ≤ i := Int.ediv_nonneg hR0 hpe.le
  have hip : i < p := by
    rw [hi, Int.ediv_lt_iff_lt_mul hpe, ← pow_succ']; exact hR1
  refine ⟨i.toNat, by omega, ?_⟩
  have hr0 : 0 ≤ a % ((p : ℤ) ^ e) := Int.emod_nonneg _ hpe.ne'
  rw [hmod] at hsplit
  have key : ((R.toNat : ℕ) : ℤ) = (((a % ((p : ℤ) ^ e)).toNat + p ^ e * i.toNat : ℕ) : ℤ) := by
    push_cast
    rw [Int.toNat_of_nonneg hR0, Int.toNat_of_nonneg hr0, Int.toNat_of_nonneg hi0]
    linarith
  exact_mod_cast key

/-- **Every solution reduces into every level.** -/
theorem mem_lvl (F : Form) (M : ℤ) (p : ℕ) (hp : 0 < p) (a b : ℤ) (h : evalF F a b = M) :
    ∀ e, ((a % ((p : ℤ) ^ e)).toNat, (b % ((p : ℤ) ^ e)).toNat) ∈ lvl F M p e := by
  intro e
  induction e with
  | zero => simp [lvl, Int.emod_one]
  | succ e ih =>
    obtain ⟨i, hi, hai⟩ := lift_step p e hp a
    obtain ⟨j, hj, hbj⟩ := lift_step p e hp b
    simp only [lvl, liftAt, List.mem_flatMap, List.mem_range, List.mem_filterMap]
    refine ⟨_, ih, i, hi, j, hj, ?_⟩
    rw [← hai, ← hbj]
    have hpe1 : (0 : ℤ) < (p : ℤ) ^ (e + 1) := by positivity
    have c1 : ((a % ((p : ℤ) ^ (e + 1))).toNat : ℤ) = a % ((p : ℤ) ^ (e + 1)) :=
      Int.toNat_of_nonneg (Int.emod_nonneg _ hpe1.ne')
    have c2 : ((b % ((p : ℤ) ^ (e + 1))).toNat : ℤ) = b % ((p : ℤ) ^ (e + 1)) :=
      Int.toNat_of_nonneg (Int.emod_nonneg _ hpe1.ne')
    have hcong := evalF_modEq F (Int.mod_modEq a ((p : ℤ) ^ (e + 1)))
      (Int.mod_modEq b ((p : ℤ) ^ (e + 1)))
    rw [h] at hcong
    have : (evalF F (a % ((p : ℤ) ^ (e + 1))) (b % ((p : ℤ) ^ (e + 1))) - M) % ((p : ℤ) ^ (e + 1)) = 0 :=
      Int.emod_eq_zero_of_dvd (Int.ModEq.dvd hcong.symm)
    rw [c1, c2, if_pos this]

/-- **An empty level proves the equation has no integral solution.** -/
theorem no_solution_of_lvl (F : Form) (M : ℤ) (p e : ℕ) (hp : 0 < p) (h : lvl F M p e = []) (a b : ℤ) :
    evalF F a b ≠ M := by
  intro hab
  have := mem_lvl F M p hp a b hab e
  rw [h] at this
  simp at this

/-! ### p-adic descent on forms (small certificates)

Residue lifting is exhaustive but can be wide.  Descent on forms follows the equation's p-adic
structure instead.  For `F(a, b) = M`, split the integer pairs:
* `p ∣ a, p ∣ b`: then `p³ ∣ M` and `F(a/p, b/p) = M/p³` (the *zero child*), or no solution
  when `p³ ∤ M`;
* otherwise, when `p ∣ M`, the residue `(a : b)` mod `p` is a root of `F` mod `p`, so `(a, b)` lies
  on a line `a = λ b + p c` (`T = ((λ, p), (1, 0))`, variables `(b, c)`) or `b = p v`
  (`T = ((1, 0), (0, p))`, variables `(a, v)`).  There `F ∘ T = p^s H` and the child is
  `H = M / p^s`.

A certificate is a list of nodes, children after parents.
- A *leaf* is closed by a lifting tree (`lvl`).
- A *split* lists the zero child and the line children.
- The checker verifies, residue by residue, that every nonzero pair mod `p` with `F ≡ 0` lies on a
  listed line.  This needs no primality, and no inverse mod `p`.
-/

/-- The node kinds: a lifting leaf (depth `e`), or a split with an optional zero child and line
children `(λ?, s, child index)` (`none` is the line `b = p v`). -/
inductive Kind
  | leaf (e : ℕ)
  | split (zero : Option ℕ) (lines : List (Option ℕ × ℕ × ℕ))
  deriving DecidableEq, Repr

/-- The line matrix. -/
def lineMat (p : ℕ) : Option ℕ → Mat
  | some l => (((l : ℤ), (p : ℤ)), (1, 0))
  | none => ((1, 0), (0, (p : ℤ)))

/-- `F` divided by `d`, coefficientwise, when `d` divides every coefficient. -/
def divF (F : Form) (d : ℤ) : Form := (F.1 / d, F.2.1 / d, F.2.2.1 / d, F.2.2.2 / d)

/-- `d` divides every coefficient of `F`. -/
def dvdF (d : ℤ) (F : Form) : Bool :=
  decide (F.1 % d = 0 ∧ F.2.1 % d = 0 ∧ F.2.2.1 % d = 0 ∧ F.2.2.2 % d = 0)

/-- The residue pair `(a₀, b₀)` lies on the line `λ?` mod `p`. -/
def onLine (p : ℕ) (a0 b0 : ℕ) : Option ℕ → Bool
  | some l => decide ((a0 : ℤ) % p = ((l : ℤ) * b0) % p)
  | none => decide ((b0 : ℤ) % p = 0)

/-- One node's check. -/
def nodeB (p : ℕ) (nodes : List (Form × ℤ × Kind)) (i : ℕ) : Bool :=
  match nodes[i]? with
  | none => false
  | some (F, M, Kind.leaf e) => decide (lvl F M p e = [])
  | some (F, M, Kind.split zero lines) =>
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
def descB (p : ℕ) (nodes : List (Form × ℤ × Kind)) : Bool :=
  decide (0 < p) && (List.range nodes.length).all (nodeB p nodes)

lemma evalF_divF {F : Form} {d : ℤ} (hd : d ≠ 0) (h : dvdF d F = true) (u v : ℤ) :
    evalF F u v = d * evalF (divF F d) u v := by
  obtain ⟨c0, c1, c2, c3⟩ := F
  simp only [dvdF, decide_eq_true_eq] at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  obtain ⟨k0, rfl⟩ := Int.dvd_of_emod_eq_zero h0
  obtain ⟨k1, rfl⟩ := Int.dvd_of_emod_eq_zero h1
  obtain ⟨k2, rfl⟩ := Int.dvd_of_emod_eq_zero h2
  obtain ⟨k3, rfl⟩ := Int.dvd_of_emod_eq_zero h3
  simp only [evalF, divF, Int.mul_ediv_cancel_left _ hd]
  ring

lemma evalF_scale (F : Form) (p a b : ℤ) : evalF F (p * a) (p * b) = p ^ 3 * evalF F a b := by
  simp only [evalF]; ring

/-- **One node's check is sound given its children**: if `nodeB p nodes i` holds and every later
node's equation has no integral solution, neither has node `i`'s.  Descent soundness, for a fixed
prime or with a prime per node, is induction over this step. -/
theorem nodeB_step (p : ℕ) (hp : 0 < p) (nodes : List (Form × ℤ × Kind)) (i : ℕ)
    (hi' : nodeB p nodes i = true)
    (child : ∀ j : ℕ, i < j → ∀ m : Form × ℤ × Kind, m ∈ nodes[j]? → ∀ a b : ℤ, evalF m.1 a b ≠ m.2.1) :
    ∀ n : Form × ℤ × Kind, n ∈ nodes[i]? → ∀ a b : ℤ, evalF n.1 a b ≠ n.2.1 := by
  intro n hn a b hab
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp
  obtain ⟨F, M, kind⟩ := n
  simp only [Option.mem_def] at hn
  simp only at hab
  unfold nodeB at hi'
  rw [hn] at hi'
  cases kind with
  | leaf e =>
    simp only [decide_eq_true_eq] at hi'
    exact no_solution_of_lvl F M p e hp hi' a b hab
  | split zero lines =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
      Bool.or_eq_true, List.any_eq_true] at hi'
    obtain ⟨⟨⟨hMp, hz⟩, hcover⟩, hlines⟩ := hi'
    by_cases hab0 : (p : ℤ) ∣ a ∧ (p : ℤ) ∣ b
    · -- the zero class
      obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩⟩ := hab0
      rw [evalF_scale] at hab
      cases zero with
      | none =>
        simp only [decide_eq_true_eq] at hz
        exact hz (by rw [← hab]; simp)
      | some j =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hz
        obtain ⟨⟨hij, hM3⟩, hnj⟩ := hz
        cases hnode : nodes[j]? with
        | none => rw [hnode] at hnj; simp at hnj
        | some m =>
          rw [hnode] at hnj
          simp only [Option.map_some, Option.some.injEq] at hnj
          have := child j hij m (by simp [hnode]) a' b'
          rw [(Prod.mk.inj hnj).1, (Prod.mk.inj hnj).2] at this
          apply this
          rw [← hab, Int.mul_ediv_cancel_left _ (by positivity)]
    · -- a primitive pair: its residue lies on a listed line
      have hA0 := Int.emod_nonneg a hpz.ne'
      have hA1 := Int.emod_lt_of_pos a hpz
      have hB0 := Int.emod_nonneg b hpz.ne'
      have hB1 := Int.emod_lt_of_pos b hpz
      have hc := hcover (a % p).toNat (by omega) (b % p).toNat (by omega)
      have ca : (((a % p).toNat : ℕ) : ℤ) = a % p := Int.toNat_of_nonneg hA0
      have cb : (((b % p).toNat : ℕ) : ℤ) = b % p := Int.toNat_of_nonneg hB0
      rcases hc with (⟨h0a, h0b⟩ | hnz) | ⟨ln, hln, hon⟩
      · exact hab0 ⟨Int.dvd_of_emod_eq_zero (by omega), Int.dvd_of_emod_eq_zero (by omega)⟩
      · apply hnz
        rw [ca, cb]
        have := evalF_modEq F (Int.mod_modEq a p) (Int.mod_modEq b p)
        rw [hab] at this
        rw [this]; exact hMp
      · have hl := hlines ln hln
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hl
        obtain ⟨⟨⟨hil, hdv⟩, hMs⟩, hnl⟩ := hl
        -- write (a, b) = T (u, v)
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
          have := child ln.2.2 hil m (by simp [hnode]) u v
          rw [(Prod.mk.inj hnl).1, (Prod.mk.inj hnl).2] at this
          apply this
          rw [← hT, Int.mul_ediv_cancel_left _ (by positivity)]

/-- Strong induction from the end of a certificate: if each node is sound whenever all later
nodes are, every node is sound. -/
theorem sound_of_step {α : Type*} (nodes : List α) (P : α → Prop)
    (step : ∀ i : ℕ, i < nodes.length → (∀ j : ℕ, i < j → ∀ m : α, m ∈ nodes[j]? → P m) →
      ∀ n : α, n ∈ nodes[i]? → P n) :
    ∀ (i : ℕ) (n : α), n ∈ nodes[i]? → P n := by
  suffices H : ∀ k i : ℕ, nodes.length - i ≤ k → ∀ n : α, n ∈ nodes[i]? → P n from
    fun i => H _ i le_rfl
  intro k
  induction k with
  | zero =>
    intro i hi n hn
    rw [List.getElem?_eq_none (by omega)] at hn; simp at hn
  | succ k ih =>
    intro i hi n hn
    have hlt : i < nodes.length := by
      by_contra hc; push_neg at hc; rw [List.getElem?_eq_none hc] at hn; simp at hn
    exact step i hlt (fun j hj => ih j (by omega)) n hn

/-- **Soundness of the descent certificate**: every node's equation has no integral solution. -/
theorem descB_sound (p : ℕ) (nodes : List (Form × ℤ × Kind)) (h : descB p nodes = true) :
    ∀ i : ℕ, ∀ n : Form × ℤ × Kind, n ∈ nodes[i]? → ∀ a b : ℤ, evalF n.1 a b ≠ n.2.1 := by
  simp only [descB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨hp, hall⟩ := h
  exact sound_of_step nodes (fun n => ∀ a b : ℤ, evalF n.1 a b ≠ n.2.1)
    (fun i hi child => nodeB_step p hp nodes i (hall i hi) child)

/-- **A descent certificate proves `F(a, b) = M` has no integral solution** (node 0). -/
theorem no_solution_of_desc (p : ℕ) (F : Form) (M : ℤ) (kind : Kind)
    (rest : List (Form × ℤ × Kind)) (h : descB p ((F, M, kind) :: rest) = true) (a b : ℤ) :
    evalF F a b ≠ M :=
  descB_sound p _ h 0 (F, M, kind) (by simp) a b

/-! ### Descent with a prime per node

Some equations need several primes: split at `p` where `p ∣ M`, and close a child at another
prime `q ∤ M` by residue lifting.  A multi-prime certificate lists `(p, F, M, kind)`; each node is
checked by `nodeB` at its own prime.  Soundness is the same induction. -/

/-- A descent certificate with a prime per node. -/
def descM (nodes : List (ℕ × Form × ℤ × Kind)) : Bool :=
  (List.range nodes.length).all fun i =>
    match nodes[i]? with
    | some (p, _) => decide (0 < p) && nodeB p (nodes.map Prod.snd) i
    | none => false

/-- **Soundness of multi-prime descent.** -/
theorem descM_sound (nodes : List (ℕ × Form × ℤ × Kind)) (h : descM nodes = true) :
    ∀ (i : ℕ) (n : Form × ℤ × Kind), n ∈ (nodes.map Prod.snd)[i]? → ∀ a b : ℤ, evalF n.1 a b ≠ n.2.1 := by
  simp only [descM, List.all_eq_true, List.mem_range] at h
  refine sound_of_step (nodes.map Prod.snd) (fun n => ∀ a b : ℤ, evalF n.1 a b ≠ n.2.1)
    (fun i hi child => ?_)
  rw [List.length_map] at hi
  have hi' := h i hi
  cases hq : nodes[i]? with
  | none => rw [hq] at hi'; simp at hi'
  | some q =>
    obtain ⟨p, r⟩ := q
    rw [hq] at hi'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hi'
    exact nodeB_step p hi'.1 _ i hi'.2 child

/-- **A multi-prime descent certificate proves `F(a, b) = M` has no integral solution.** -/
theorem no_solution_of_descM (p : ℕ) (F : Form) (M : ℤ) (kind : Kind)
    (rest : List (ℕ × Form × ℤ × Kind)) (h : descM ((p, F, M, kind) :: rest) = true) (a b : ℤ) :
    evalF F a b ≠ M :=
  descM_sound _ h 0 (F, M, kind) (by simp) a b

end PerfectPower.ThueLocal
