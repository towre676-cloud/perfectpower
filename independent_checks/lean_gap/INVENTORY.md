# PerfectPower Lean gap inventory — the two named open formal items

Repository inspected read-only at `~/workspace/research/perfectpower`
(HEAD `4769e49`, default branch `claude/laughing-lamport-qqzdo9`),
Lean toolchain pin `leanprover/lean4:v4.20.0`, Mathlib pin `v4.20.0`
(`lakefile.lean` / `lean-toolchain`). The Lean tree contains 1,175
`.lean` files in total, 947 of them under `PerfectPower/` plus the root
module `PerfectPower.lean`.

## 1. There is no `sorry`, no `admit`, and no custom axiom anywhere in the tree

Exact searches over all 1,175 `.lean` files (commands in REPORT.md):

- Word search for `sorry`: **0 occurrences** (not even in comments).
- Word search for `admit`: 4 occurrences, all the ordinary English word
  "admit" inside doc comments (`PerfectPower/UnitGenResidue.lean:9`,
  `PerfectPower/Generated/Minus61.lean:80`, `Minus87.lean:80`,
  `Minus95.lean:78`). No tactic use.
- Declarations matching `^\s*axiom `: **0**.
- `Lean.ofReduceBool` / `sorryAx`: mentioned only in comments asserting
  their *absence* (`PerfectPower/Generated/MordellPoints.lean:6`,
  `PerfectPower/Generated/Sandwich.lean:305, 381` — "kernel evaluation,
  `decide +kernel`; no `Lean.ofReduceBool`").
- `native_decide`: 1 file, `PerfectPower/Tactic/NativePower.lean`, which
  defines the tactic; the audited gates described in the monographs
  reject `sorryAx` and native-reduction axioms, permitting only
  `propext`, `Classical.choice`, `Quot.sound`
  (`docs/DESCENT_BRIDGES_MONOGRAPH.md`, reproduction section).
- No `opaque`, `partial def`, or `unsafe` in any of the six bridge files
  below.

**Conclusion: the two open items are not hidden sorries. They are
missing theorems.** Everything stated in the bridge modules is proved;
the gaps are (a) hypotheses that callers must supply, and (b) whole
constructions/statements that do not exist yet in Lean form. The
distinction matters and is itemised below.

## 2. Item (1): squareclass quotient identification — what is missing, exactly

Stated as open at `README.md:134` ("squareclass quotient identification
and unconditional Mordell–Weil rank remain open"), at
`docs/DESCENT_BRIDGES_MONOGRAPH.md:111` ("The squareclass quotient
identification and construction of that decomposition remain required
for unconditional Lean rank conclusions"), and most precisely at
`docs/ISOGENY_POINT_GROUPS_MONOGRAPH.md:107`:

> "Also still required are the squareclass homomorphisms, the
> identification of their kernels with the respective isogeny images,
> the associated finite image bounds, and the torsion/kernel
> cardinality calculation leading to the customary divisor four."

Concretely, for the 2-isogeny φ : E → E′ and its dual ψ : E′ → E already
defined as point-group maps in the repo, the following do **not** exist
as Lean definitions/theorems anywhere in the tree:

- **(1a) The squareclass homomorphisms themselves.** No definition of
  δ : E′(ℚ) → ℚ*/ℚ*² (x-coordinate class, with its exceptional values
  at 0 and at the rational 2-torsion point T′) or of the dual
  δ′ : E(ℚ) → ℚ*/ℚ*², and no proof that either is a group homomorphism.
- **(1b) Kernel = image identifications.** No theorem
  `ker δ = range ψ` (i.e. δ(P′) = 1 ↔ P′ ∈ ψ(E(ℚ))) and no dual
  `ker δ′ = range φ`. This is the "identification" in the item's name.
- **(1c) Finite image bounds.** No theorem bounding the images of δ, δ′
  to an explicit finite set of squareclasses (classically: squarefree
  divisors of b, resp. of a² − 4b). The arithmetic input for such a
  bound *is* proved — see §4 — but it is not assembled into a statement
  about δ.
- **(1d) The torsion/kernel cardinality step** ("the customary divisor
  four"): no computation of |ker φ| = 2, |ker ψ| = 2 inside the index
  identity that would turn `elliptic_descent_rank` into a numerical
  rank formula. (The point-level kernel of φ *is* known:
  `TwoIsogenyPointMap.phi_eq_zero_iff`, §4.)

What carries this gap inside existing theorems: **nothing** — no
theorem in `TwoIsogenyPointMap.lean` (405 lines), `TwoIsogenyDual.lean`
(243), `IsogenyCoordinates.lean` (25), `IsogenyIndexBridges.lean` (32),
`DescentRankBridge.lean` (75) or `TwoDescentBridges.lean` takes a
squareclass hypothesis. The gap is absence, not assumption.

## 3. Item (2): unconditional Mordell–Weil rank — the exact hypotheses that carry it

The rank conclusion is blocked by two distinct inputs, each visible in
the code:

### 3a. The free-plus-finite decomposition is a hypothesis, not a construction

`PerfectPower/DescentRankBridge.lean`:

- Line 43, `doubling_index_from_decomposition`: premise
  `(e : G ≃+ F × T)` with `[Module.Free ℤ F] [Module.Finite ℤ F]
  [Finite T]` — the decomposition is *supplied by the caller*.
- Line 52, `descent_rank_equation`: same premise `(e : G ≃+ F × T)`.
- Line 64, `elliptic_descent_rank`: premise
  `(e : (TwoIsogenyPointMap.E a b).Point ≃+ F × T)` — i.e. an explicit
  Mordell–Weil decomposition of the *actual* rational point group,
  with F free of finite rank and T finite. The file's own doc comment
  (lines 61–63) says: "the only remaining group input here is a
  Mordell–Weil decomposition, whose free rank and finite torsion are
  explicit."

No construction of such an `e` for any retained curve exists in the
tree; `docs/ISOGENY_POINT_GROUPS_MONOGRAPH.md:107` confirms: "It has
not been constructed here for the retained rational point groups."
Supplying it *is* the Mordell–Weil theorem for those curves (finite
generation plus a basis), so this is a genuine mathematical gap, not a
technicality. Note the rank is also never *bounded above* by this
route without item (1): the index identity relates [E:2E] to the two
isogeny indices, and converting those into a rank bound is exactly
what (1b)+(1c)+(1d) would provide.

### 3b. The Mordell completion inputs (contracts/current_frontier.json, finding id 2)

`contracts/current_frontier.json` finding 2, "Mordell global
completeness", status **`open`**, contract text: "All 457 retained
census bases now have unconditional actual rational-group
saturation-at-2 proofs. Curve-specific rank upper bounds, saturation
at other primes and global integral coordinate bounds remain open.
The separate 1,026 descent curves retain global emptiness proofs."

`PerfectPower/MordellCompletionBridge.lean` (149 lines, imports all of
Mathlib) proves the *composition* machinery and leaves exactly three
curve-specific inputs as theorem hypotheses:

- **Global saturation prime support** — `PrimeSupport H S`
  (definition, line 36) is the hypothesis `hsupport` of
  `eq_top_of_prime_support` (line 67). Per
  `docs/MORDELL_FORMAL_BRIDGE_MONOGRAPH.md:25`, every curve needs "a
  proved global saturation prime-support bound, including exceptional
  reduction primes. The eclib logs retain numerical bounds and the
  selected primes, but do not contain Lean proof terms establishing
  those bounds." The same monograph (line 17) records a proved
  *obstruction* to a shortcut: the subgroup 17ℤ ⊂ ℤ is saturated at
  every prime ≤ 13 and still proper, so no native prime cutoff
  supplies the support bound.
- **Saturation at the supported primes** — `PrimeSaturated H p`
  (definition, line 14) is the hypothesis `hsat` of
  `eq_top_of_prime_support` (line 67), of `mem_of_bounded_multiple`
  (line 76) and of `eq_top_of_bounded_index` (line 95, whose other
  hypothesis is `BoundedIndex H B`, line 19). One proved special case
  exists: `boundedIndex_of_finite_quotient` (line 24) derives
  `BoundedIndex` from a finite quotient. The bridge
  `prime_saturated_of_reduction_separation` (line 113) derives
  `PrimeSaturated` from a *separation premise* `hsep` (line 113):
  for every g ∉ H a reduction homomorphism separating g from
  p·(image of H). The monograph (line 11) is explicit that "a
  finite-field computation by itself does not construct that
  compatibility proof" — the rational-to-finite-group connection for
  the 788 native exclusions is an uninstantiated interface
  (monograph line 25).
- **Global integral coordinate bound** — hypothesis `hbound`
  (lines 133 and 142) of `integralBox_complete` and
  `integralList_complete`: `∀ x y, y² = x³ + k → -X ≤ x ∧ x ≤ X ∧
  -Y ≤ y ∧ y ≤ Y`. Per monograph line 27, this needs "a proved global
  integral-coordinate bound or an equivalent completeness theorem for
  the elliptic-logarithm and LLL argument… not a checked analytic
  inequality chain or a Lean proof of the global bound." The monograph
  (line 3) quantifies the result: "zero of the 457 external completion
  packets have been promoted to unconditional Lean complete-basis or
  integral-list theorems by this continuation."

### 3c. Related explicit-premise items in the same frontier contract

For completeness: finding id 5 ("Matveev premises", `open`: "Named
analytic premises remain undischargeable by finite packet checks") and
finding id 9 (higher number-ring orbit representatives and effective
exponent bounds, `open`) are the same pattern — clean conditional
theorems whose analytic hypotheses are the gap. They are outside the
two named items but are recorded here because any "no gaps remain"
claim would have to address them too. `PerfectPower/ABC.lean:11`
shows the house style: premises are taken as explicit hypotheses
"so `#print axioms` stays at the standard three."

## 4. What IS proved (so the gap boundaries are exact)

- Both isogenies as actual point-group maps, with addition
  compatibility: `TwoIsogenyPointMap.phi_add` (line 314),
  `TwoIsogenyDual.scaleBack_add` (line 46); normalised dual composition
  = doubling: `TwoIsogenyDual.dual_phi` (line 175),
  `dual_comp_phiHom` (line 229).
- Point-level kernel of φ: `TwoIsogenyPointMap.phi_eq_zero_iff`
  (line 113): φ(P) = 0 ↔ P = 0 ∨ P = T.
- Coordinate identities: `IsogenyCoordinates.isogeny_lands_on_curve`,
  `dual_composition_x`.
- The corrected index algebra, fully proved for abstract groups:
  `IsogenyIndexBridges.composition_index`, `kernel_correction`,
  `doubling_index`, and `DescentRankBridge.descent_rank_equation` /
  `elliptic_descent_rank` (conditional only on the decomposition
  premise of §3a).
- The arithmetic descent input: `TwoDescentBridges.integer_squareclass`
  (line 103, *existence* of a signed squarefree representative),
  `rational_primitive_squareclass` (line 121), and
  `rational_point_cover_complete` (line 155): every nonzero rational
  point x-coordinate equals (d)·u²/v² with d squarefree, **d ∣ b**, and
  an associated quartic — with no squareclass premise supplied. What
  this does *not* state is that d is the *unique* such label, which is
  the well-definedness half of the squareclass identification and the
  piece attempted in this task (REPORT.md).
- Saturation composition and finite-box enumeration:
  all ten theorems of `MordellCompletionBridge.lean` as itemised in §3b.

## 5. Summary table

| Gap | Kind | Location |
|---|---|---|
| δ, δ′ squareclass homomorphisms (1a) | missing definition + homomorphism proof | absent; required by ISOGENY_POINT_GROUPS_MONOGRAPH.md:107 |
| ker δ = range ψ, ker δ′ = range φ (1b) | missing theorem | absent |
| finite image bounds for δ, δ′ (1c) | missing theorem (arithmetic input proved) | absent; input at TwoDescentBridges.lean:155 |
| divisor-four kernel/torsion cardinality (1d) | missing computation | absent |
| Mordell–Weil decomposition `E(ℚ) ≃+ F × T` (2a) | hypothesis, never constructed | DescentRankBridge.lean:43, 52, 64 |
| global prime support `PrimeSupport H S` (2b) | hypothesis | MordellCompletionBridge.lean:36, 67; frontier finding 2 |
| prime saturation `PrimeSaturated H p` / separation premise (2b) | hypothesis / uninstantiated interface | MordellCompletionBridge.lean:14, 76, 95, 113 |
| global coordinate bound `hbound` (2b) | hypothesis | MordellCompletionBridge.lean:133, 142 |
| rank upper bounds per curve (2) | consequence of (1)+(2a), not formalised | README.md:134; frontier finding 2 |
| sorry / admit / custom axioms | **none exist** | whole tree, §1 |
