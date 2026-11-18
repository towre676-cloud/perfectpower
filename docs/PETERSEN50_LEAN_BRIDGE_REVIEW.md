# Petersen50: source-bound BDD semantic bridge

Approved semantic bridge based on PR #17 commit `89d1e580dd05b77930424d5911abe8c736efcfdc`.
The canonical checker, original receipts and published full-witness evidence
are unchanged. This document is the mathematical and verification report for
the additions approved for repository integration. The Explorer feed exposes
the semantic-bridge evidence separately from the external replay result.

## Result and its precise limit

The candidate proves generic source-coordinate transport, signed threshold
recurrences, conjunction/cofactor rules, chronological resource stages,
indexed allocation counts, skipped-variable multiplicities, and a portion of
binary decoding in Lean 4.20.0. It includes small checked examples and an
explicit specialization to the retained Petersen50 coordinate order.

It **does not prove** that the complete 1,395,583,020-byte stream generates
these semantic proofs. It does not establish a Lean theorem asserting the
unconditional Petersen50 population. That population remains the independently
replayed external result **702,508,860,122,761**. In particular, both the new
receipt and the unchanged canonical receipt retain
`full_population_kernel_proved: false`.

The new theorem `Petersen50Bridge.population_if_complete_stage_evidence` has
explicit hypotheses: a checked 50-variable diagram, complete five-stage
semantic evidence for the reordered literal rows, and its asserted count.
It is a proved implication. No inhabitant of its full-witness evidence
hypothesis is supplied by this candidate.

## Mathematical specification

Let `census n f` be the sum of the indicator of Boolean predicate `f` over
all length-`n` Boolean lists. The reused `assignments_multiplicity` theorem
proves that each such list occurs exactly once, and the reused
`census_cardinality` identifies the sum with the size of the filtered list.
Thus the population is a subset count, not a count of search paths.

For a decision diagram, `reject` is false, `accept` is true, a branch consumes
one input bit, and `skip r d` drops `r` input bits. Consequently

\[
C_{n+r}(\operatorname{skip}_r d)=2^r C_n(d).
\]

For a node at level `k` with child levels `l` and `h`, its local count is

\[
2^{l-k-1}c_{lo}+2^{h-k-1}c_{hi}.
\]

`unequal_skips_count` covers different child gaps. `lift_count` and
`root_population` cover the omitted prefix above a stored root, giving
`2^root.level * root.localCount`. These are natural-number equations;
no machine-word overflow or shift implementation is imported as an axiom.
`indexed_allocation_count` proves that successful execution of the existing
Lean indexed allocation checker certifies the claimed local population.
The checked-node invariant ties counts to actual diagrams and `Fits`, rather
than accepting an arbitrary numerical count label.

For nonnegative resource weights, `dot ws xs` is the selected cost. The new
`Threshold ws cap d` uses **integer** capacities, with rules:

* `cap < 0`: rejection, including all-zero rows and the empty selection;
* `sum ws <= cap`: acceptance;
* branch: low evidence at `cap`, high evidence at `cap - w`;
* reduction/reuse: an explicitly proved equality of diagram predicates.

`threshold_sound` proves the resulting predicate is exactly
`decide ((dot ws xs : Int) <= cap)`. This distinguishes negative residual
capacities from truncated natural subtraction. Suffix-sum pruning is covered
by the accept rule and the reused proof `dot_bound`.

`Conjunction n a b out` records the rejecting, accepting, equal-operand,
cofactor-split, common-skip and semantic-reuse rules. Its theorem is restricted
to lists of length `n`, so it makes no assumption about a missing input bit.
`cofactor_correct` is reused. A recursive apply split proves both Boolean
cofactors; `skip` handles the common gap above the minimum operand level.

`Stages n rows caps d` starts at `accept` and appends one threshold and its
intersection with the **previous** predicate. `stages_sound` proves both the
row/capacity length invariant and exact feasibility for every length-`n`
assignment. `stage_population` connects this predicate to the checked count.
An omitted constraint cannot furnish this evidence for the original list of
rows. This is a semantic guarantee, not yet a proof of numeric proof-index
lookup or the binary stage counter.

## Source-variable transport

`PlanningPermutation` counts selections of project identities. It proves
population invariance under `List.Perm` by its constructors: preserve a head,
swap adjacent projects, and compose permutations. Feasibility is invariant
because simultaneous reordering preserves the sum of the selected source
costs for every resource. `dot_selected` and `reordered_semantics` connect
this formulation back to Boolean coordinates.

`original_population` in `PlanningReplayBridge` has the following precise
shape:

```lean
(c : CheckedNode n)
(order : List Nat) (rows : List (List Nat)) (caps : List Nat)
(permutation : List.Perm order (List.range n))
(shape : ∀ row ∈ rows, row.length = n)
(source : Stages n (reorder order rows) (caps.map Int.ofNat) c.diagram)
⊢ c.count = census n (feasible rows caps)
```

The permutation proof establishes both coverage and the absence of duplicate
or out-of-range project indices; equal list length alone would not suffice.
The proof requires neither the producer's sorting algorithm nor a rerun of
that algorithm inside Lean. The actual order is also independently compared
against the retained external receipt by the audit script. The literal
50-element order is proved to permute `range 50` by kernel reduction.
The original 50-by-5 rows are reused from `PetersenPlanning`, and their shape
is a kernel theorem. The raw OR-Library file's relationship to those literals
is independently checked by the existing source-binding routine; it remains
outside the kernel.

## Binary grammar and decoding boundary

The existing stream starts with `PPBDD001`, little-endian unsigned dimensions,
`m` signed 32-bit capacities, and `m*n` unsigned costs in row-major order.
The body contains eight unsigned little-endian 32-bit words per record.

| Tag | Payload after tag | New formal coverage |
| --- | --- | --- |
| 1 | level, low ID, high ID, count low/high, zero, zero | Decoder, word/count bounds, executable indexed allocation count theorem |
| 2 | resource, level, cap, result ID, low/high proof IDs, zero | Decoder and signed threshold semantic recurrence; numeric lookup refinement remains |
| 3 | left/right/result IDs, low/high proof IDs, zero, zero | Decoder and conjunction semantic rules; numeric lookup refinement remains |
| 4 | resource, threshold ID/proof ID, root ID/apply proof ID, count low/high | Decoder, chronological semantic stages and root multiplicity; numeric stream-state link remains |
| 5 | root ID, count low/high, four zeros | Decoder and root multiplicity; EOF/finalization-state proof remains |

`PlanningTraceDecode` defines pure Lean decoding over `List UInt8`. It proves
that each decoded word is below `2^32`, a combined count is below `2^64`
when its words are bounded, and signed decoding lies in the signed 32-bit
range. A decoded record consumes exactly 32 bytes, so a short record cannot
be accepted. `fromWords` enforces tag-specific zero padding and rejects
unknown tags. The literal allocation bytes are then passed through the
existing indexed checker **inside Lean**, with their local population proved.

This is a record decoder, not a complete stream parser: it does not decode
the magic/header, assemble the full stream, validate every proof index, reset
stage proof tables, require all finalization conditions, reject trailing
records after finalization, or decompress xz/gzip. The Python tests exercise
some of these conditions independently; test success is not a kernel proof
of them.

## Small certificates and executed checks

`PlanningReplayExamples` contains:

* A literal allocation with a free suffix coordinate, accepted by both the
  Lean byte decoder and indexed allocation checker; its local population is
  2. Incorrect gap counts, forward references, bad order and equal-child
  unreduced allocations are rejected by kernel reduction.
* A complete semantic one-resource fixture for `[0,1,0] <= 0`, with population
  4. It uses source recurrence, signed rejection, equal-branch reduction,
  skipped coordinates and stage conjunction. The Python test supplies a
  corresponding complete five-record binary trace; its allocation bytes
  match the Lean literal exactly. The stage-evidence proof is constructed
  separately; the complete byte trace is not parsed into evidence in Lean.
* Two original-coordinate resources `[[2,0,1],[0,1,1]]`, capacities `[1,1]`,
  and order `[2,0,1]`. Explicit threshold and conjunction derivations yield
  population 3, transported back to the original rows by the generic
  permutation theorem. This proof does not validate the final predicate by
  enumerating all assignments.
* An all-zero row with capacity -1, whose population is 0.

Run from the repository with the pinned Lean toolchain on PATH:

```bash
python scripts/check_planning_bridge.py --lean lean
PYTHONPATH=python python -m unittest \
  python.tests.test_planning_bridge python.tests.test_planning_certificate -v
```

The audit builds the nine-module dependency closure directly, then builds
both final proof modules through an isolated Lake project using the same
sources. It needs the standard library, without downloading Mathlib. The
whole unrelated PerfectPower library is not built by this command.

It audits **every theorem** in those modules and permits only Lean's standard
`propext`, `Quot.sound` and `Classical.choice` axioms. It rejects admitted or
native-reflection axioms. Five intentionally false propositions must fail
with Lean's explicit `decide`-proved-false diagnostic: wrong population,
duplicate source coordinate, negative-capacity truncation, wrong endian
count, and accepted nonzero padding.

Exact results, source hashes, original literal-source binding, matched receipt
order, build output, axiom lists and rejection diagnostics are in
`receipts/planning/bridge/`. The Python log covers the existing deterministic
120 random small source cases, boundary cases up to 62 free variables,
record bit mutations, and the new literal fixture attacks. Neither the
complete Python replay nor the historical best-first search is rerun.

## Remaining trust and next proof obligations

| Component | Current evidence | What is still required for full kernel certification |
| --- | --- | --- |
| Lean semantic rules and permutation transport | Kernel checked | Complete evidence for the actual witness |
| Literal source rows and capacities | Existing Lean literals plus independent raw-file comparison | Proved source-file decoding, or an explicitly accepted literal instance specification |
| One allocation record | Decoded and count checked in Lean | Extend to the complete source header and stream |
| Python parser and packed tables | Existing full replay, unchanged; small adversarial tests | State invariant and refinement theorem for numeric IDs, earlier references, table appends and resets |
| Threshold/apply proof tables | Semantic inference rules proved | Connect every stored numeric state and operand pair to its inferred proposition |
| Resource stages and finalization | Semantic append theorem and root-count theorem | Prove source stage indices, complete stage coverage, final root identity, EOF and trailing-data rejection |
| Compression, filesystem and hashes | External transport and identity evidence | Treat decompression as an untrusted producer of fully checked bytes; compressed-file identity remains external unless separately formalized |
| Petersen50 count | Complete external replay already succeeded | Kernel construction/check of full-witness evidence; not provided here |

The next implementation should introduce an executable decoded-record state
machine with a proved invariant over indexed node and proof tables. Its
`mk_matches` refinement must connect raw branch fields or equal-child reuse
to the semantic diagram. Prove soundness by induction over accepted records,
then connect an explicit header parser and EOF check. A failed record must
produce no evidence; stage resets must invalidate old threshold/apply IDs.

Before using the large witness, validate this path on increasing fixtures
with zero costs, negative capacities, shared subgraphs, unequal skips,
terminal roots and several stages. The existing nested `Diagram` proof model
may expand excessively for 14.4 million nodes; a scalable shared-table model
and its proved evaluator should be measured rather than assumed. Chunking
proofs must preserve all cross-chunk references: a hash receipt alone is not
a kernel proof of the referenced chunk.

This candidate deliberately leaves that unproved stream invariant visible.
It supplies reusable mathematics and executable small checks while keeping
the external population result separate from a full kernel theorem.

## Observed review result

The final audit checks 158 theorems, including 59 in the five added modules.
All compile and the scoped Lake build succeeds. The axiom audit finds only
`propext`, `Quot.sound` and `Classical.choice`; it finds no admitted proofs or
native-reflection axioms. All five expected-failure Lean attacks are rejected
as false propositions. The six Python test methods pass, including the
existing 120-case randomized exhaustive comparison and bit-mutation suite.
These totals include reused baseline theorems; they are not a claim of 158
new results. The complete witness and historical search were not rerun.
