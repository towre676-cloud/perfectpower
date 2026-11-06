# Petersen50: reproducibility audit and independent evidence

## Finding

The reported count **702,508,860,122,761** is preserved and **the complete retained source-bound BDD certificate has now passed a fresh local replay**. PR #11's original best-first search was not independently replayed in this audit, and its missing `bf50/state.bin` has not been recovered. Current `main` contains a substantially stronger alternative verification route: a separate Boolean decision diagram (BDD) construction trace, an independently implemented source-bound streaming checker, and a published archive retaining the full trace. This audit retrieved that existing witness and ran its checker locally. The fresh receipt is `receipts/planning/compiled_repro/certificate50_replayed.json`.

The reviewed PR head is `d6ea8808afaaf4356972d50d75559afa3972d685`. The reviewed `main` snapshot is `1f6b07f90c3a7bc05444a099da444a7839f37ae3`. The source comparison reports one PR-only commit and 103 main-only commits. PR #11 remains open and mergeable against the older default branch `claude/laughing-lamport-qqzdo9`; that status does not establish conflict freedom against `main`.

## What the committed PR evidence verifies

The original counter and all 35 PR-added files were obtained at the pinned head. The three text cases were compared, in their original item order, with the independent parser's literal public `data/planning/mknap1.txt` cases. All costs and capacities match for sizes 28, 39 and 50. The JSON catalogue also agrees with the conversion path; current main and the PR have identical public case source bytes. Objective profits are irrelevant to this feasible-subset count; no optimizer-uniqueness claim is inferred from the result.

The C program was rebuilt with GCC and run locally on both validation cases under the original single-pair and six-pair bounds:

| Case | Exact count reproduced | Single-pair expansions | Six-pair expansions |
|---|---:|---:|---:|
| Petersen28 | 208,817,578 | 1,288,947 | 921,324 |
| Petersen39 | 368,072,359,571 | 136,680,243 | 8,585,148 |

All four runs closed their frontiers and reproduced the retained expansion totals. The original Python gates were not rerun to completion here; agreement with Python's expansion totals is a comparison with its retained evidence. This distinction avoids presenting two newly executed implementations where only one was run in this audit.

The committed closing log and JSON agree on the final count and **24,921,515,942** expansions. The last progress sample still has 2,433,019 live heap entries. The closing `RESULT completed=1` reports a point interval; the JSON explicitly records `heap_nodes: 0`. These are retained claims about the completed campaign, rather than a replayable transcript of all expansions. Earlier log intervals containing the answer provide consistency evidence, not an independent derivation of that answer.

## Arithmetic and bounding invariants

A node fixes the first i items in a branching permutation and records their resource usage u. Its suffix represents exactly 2^(n−i) possible subsets. Nonnegative costs allow exclusion and feasible inclusion to partition that suffix without losing or duplicating assignments. Distinct prefix assignments may have identical usage vectors; their multiplicities must still be retained, and the frontier implementation keeps separate entries rather than deduplicating them.

For each resource j, a suffix dynamic program computes S_j, the number of suffix subsets satisfying its residual capacity. For each selected pair p=(j,k), another dynamic program computes P_p, satisfying both resources. The pair program clamps over-capacity sums into absorbing overflow bins. Because costs are nonnegative, no overflowed sum can return to a feasible bin. Prefix sums over the non-overflow bins therefore give exact pair counts.

Let T=2^(n−i). Every feasible subset lies in every counted single-resource and pair set. Thus U=min(S_j,P_p) is a valid upper bound. For a chosen pair, at most T−S_j suffixes violate another resource j. The union bound therefore gives

    L_p = P_p − Σ[j outside p] (T − S_j).
    L = max(0, max_p L_p),    U = min(min_j S_j, min_p P_p).

Taking the largest valid lower bound and smallest valid upper bound preserves soundness. If the complete suffix fits every residual resource, all T assignments are feasible. If L=U, the node's count is established without enumerating those assignments. The implementation clamps L to U; within the proved domain this clamp is redundant. It must never be used to excuse an underlying inconsistent DP or arithmetic overflow.

For the actual cases, n≤50, m≤10, all capacities and individual costs are small nonnegative integers, and selected-prefix additions do not approach 16-bit overflow. All subset and frontier totals are at most 2^50; pair lower-bound differences safely fit signed 64-bit arithmetic. The branching keys alone use floating point. A different key order changes the search schedule and expansion totals but does not change the feasible-subset population. The compensated summation reproduces the historical order; its equivalence to a particular CPython `sum()` implementation is version-sensitive.

The accounting invariant is

    floor = exact_accumulated + Σ[live nodes] lower_bound,
    ceiling = exact_accumulated + Σ[live nodes] upper_bound.

An expansion removes its parent's interval, adds exact child counts, and adds surviving child intervals. The two children partition the parent. A depth-first dive replaces a node by its exact count. When the live frontier is genuinely exhausted, floor=ceiling=exact_accumulated. This argument relies on valid initialization, complete child coverage and preserved accounting throughout execution; reading only the final numbers does not establish that history.

As a bounded differential test, `bounds_probe.c` includes the actual archived C implementation and compares its intervals with direct suffix enumeration on 256 sampled states per case and pair configuration: **1,536 states total**, each with at most twelve free variables. Every tested interval contained the exact enumerated suffix population. This supports implementation review without constituting a formal proof or a full Petersen50 enumeration.

## Missing accounting reconstructed

There is a second omission besides the final BFS checkpoint: both campaign aggregations require `prefixes.bin`, and those binaries are absent from the PR. They can be regenerated cheaply by the depth-13 split mode. This audit rebuilt both from the original case data.

| Campaign | Live prefixes | Split exact constant | Solved receipt prefixes | Reconstructed retained interval |
|---|---:|---:|---:|---|
| Single pair | 4,086 | 434,014,798,562,688 | 18 | [677,205,149,345,632; 708,957,902,784,392] |
| Six pairs | 3,734 | 479,210,271,767,118 | 76 | [691,091,625,831,361; 703,631,266,985,368] |

The partial intervals and all associated expansion totals reproduce exactly. Their solved-prefix counts are retained historical inputs, not newly recomputed subtree counts. The Python audited interval **[699,497,138,009,147; 703,473,996,819,983]** is preserved as historical evidence; its incomplete spill campaign is not silently treated as replayed.

The historical C `qsort` compares width alone. Tied nodes have implementation-dependent indices. The receipt-used tie groups are [3,4] and [16,17] for the single-pair campaign, and [19,20] for the six-pair campaign. Every such group is fully solved, so replacing every interval in each group by the sum of its recorded exact counts gives the same aggregate regardless of tie order. The new procedure checks this property and rejects partially solved tied groups. Individual historical index-to-prefix identities still lack a retained original binary.

`reproduce_evidence.py` checks exact binary length, prefix dimensions, padding, interval bounds and header sums; rejects invalid receipt indices, impossible counts and conflicting duplicates; and verifies the final log/JSON correspondence. Explicit exceptions keep these validations active under `python -O`. It never writes a synthetic `state.bin`, never overwrites the historical result and never launches the Petersen50 search.

## Recovery search and the meaning of an empty checkpoint

No original checkpoint was found in fetched reachable Git history, the five workflow runs attached to the PR head, current repository-wide Actions artifacts, GitHub releases, PR comments or the targeted GitHub code search. The five attached workflows report `startup_failure` and no retained artifacts. The public repository-wide artifact listing currently reports zero artifacts and the release listing is empty. These observations do not prove that a deleted artifact, unadvertised Git object or private local copy never existed.

The BFS1 writer's empty-heap final record would be only **104 bytes**: 16 bytes of header, 48 bytes for six pairs and 40 bytes for the five accounting values. Its fields can be reconstructed from the JSON, but such reconstruction would merely serialize the assertion again. It would not recover the original bytes or strengthen provenance. Even an authentic final empty-heap record is a result receipt, not a compact proof of its construction.

The historical loader also trusts stored bounds, accumulator values and heap ordering. It checks dimensions and pair choices, but carries no case-data hash, source-build identity or complete transition proof. It writes native integer representations despite describing little-endian files. General unsupported inputs can trigger problems such as shifting by 64, malformed pair indices or usage overflow; the audited fixed cases avoid these domains. Any future resume tool should validate exact file size, source/case hashes, every live node, summed accounting, reserved bytes, heap order and disjoint prefix coverage before trusting an imported state. Checksums authenticate identity, not mathematical truth.

## Stronger alternative already on main

The published `PerfectPower_Petersen_SourceBound_Verification.zip` retains `perfectpower/certs/planning/petersen50.trace.xz`. Its archive SHA-256 is `20bc53f2bfad4c4b2a585922ded144bed20d777f6b7143ad81b2145a3e1d0413`. The compressed witness is 394,402,476 bytes; its raw stream is 1,395,583,020 bytes. This is a smaller independently checkable representation of a complete counting argument, rather than a record of 24.9 billion frontier expansions. No further compression or size-optimality claim is made.

The retained archive's checker, source parser and raw dataset match current main byte for byte. The checker imports no frontier-counter machinery. Its trace establishes threshold functions for all five literal resource rows and their successive Boolean conjunctions. Earlier-node references, variable ordering, exact node populations including skipped-coordinate multiplicities, threshold-state dependencies, conjunction cofactors, resource stages and finalization are checked. It does not accept a bare BDD node table as evidence that the diagram represents the source constraints.

The fresh successful replay took **424.000 seconds**. It accepted 14,404,146 nonterminal allocation records, 20,391 threshold proof records, 29,187,394 conjunction proof records, five source stages and one finalization. The exact uncompressed SHA-256 is `3ed96863081f6ba5c00eab09869034bcf1b42a0d16b45836b63fd30c6975d5ed`; the compressed SHA-256 is `bbfa02d1651d4bd7edc3056da412dd514c4de4dd8364688619b9b4894f858354`. Both match the retained publication evidence, as do the checker hash, raw-source hash and coordinate permutation. The original complete-trace checker was used unchanged.

Checking this complete trace is independent verification of the encoded exhaustive counting argument. It is not a new execution of PR #11's best-first search or a new construction run of the BDD producer. It shares the host Python implementation, parser and checker trust boundary with the published certificate route. Existing Lean proofs establish local rules and small source-bound instances; they do not formally verify the full packed checker, parsed stream and unrestricted 50-variable source theorem.

## Reproduction commands

From a checkout of the reviewed main snapshot with this proposed integration applied:

```bash
python3 independent_checks/planning_compiled/reproduce_evidence.py --gates --out /tmp/compiled-evidence.json
gcc -O2 -std=c11 independent_checks/planning_compiled/bounds_probe.c -lm -o /tmp/bounds-probe
/tmp/bounds-probe independent_checks/planning_compiled/petersen_50.txt '3,4;1,4;0,4;0,1;1,3;2,4'
PYTHONPATH=python python3 -m unittest discover -s python/tests -p 'test_planning*.py' -v
python3 scripts/check_planning_certificate.py /path/to/petersen50.trace.xz --case 50 --receipt /tmp/certificate50.json
```

The first command has subprocess limits and only searches the two smaller benchmark cases. Omit `--gates` for accounting reconstruction alone. The last command replays retained proof data; it does not run a search. Review its count, compressed and uncompressed hashes and source hashes against the publication receipt. Do not substitute a matching recorded receipt for actually executing the checker.

## Integration and remaining requirements

The proposed local integration copies only the PR's isolated `independent_checks/planning_compiled/` subtree, adds this audit, the bounded reconstruction tool, the differential harness, focused rejection tests and new receipts. Current `main`'s existing independent BDD checker and raw sources remain the reference for the alternative complete verification. There are no existing path collisions in the imported subtree. This is a prepared change for review, not a merged or published update; no Site synchronization is claimed.

For preserving the original campaign, obtain its authentic checkpoint with a published hash, producing command, case identity, compiler/build identity, complete segment provenance and original prefix mapping. If that cannot be recovered, keep the loss explicit. A fresh deterministic BFS run could establish a new campaign, but cannot retroactively authenticate the missing file. Such an expensive external computation requires the user's approval and is unnecessary merely to repeat an already available full certificate check.

For reviewer-accessible verification, retain the complete BDD trace, pinned checker, raw dataset and fresh replay receipt together in a durable download. GitHub currently retains the checker and receipts, not the large witness itself. Cross-link this alternative evidence from PR #11 so that its old branch does not obscure the canonical verifier. A future dedicated public artifact can remove the remaining distribution dependency on the retained download.

For a fully kernel-established theorem, finish the verified parser/table-state connection, source permutation transport and complete source-chain replay in Lean or an equivalently checked proof pipeline. Neither regenerated accounting nor successful external certificate replay closes that separate obligation. The exact count and existing supporting intervals remain unchanged.

## Pinned references

- [PR #11](https://github.com/towre676-cloud/perfectpower/pull/11)
- [Archived counter and receipts](https://github.com/towre676-cloud/perfectpower/tree/d6ea8808afaaf4356972d50d75559afa3972d685/independent_checks/planning_compiled)
- [Canonical source-bound checker](https://github.com/towre676-cloud/perfectpower/blob/1f6b07f90c3a7bc05444a099da444a7839f37ae3/python/perfectpower/planning_certificate.py)
- [Certificate publication receipt](https://github.com/towre676-cloud/perfectpower/blob/1f6b07f90c3a7bc05444a099da444a7839f37ae3/receipts/planning/independent/certificate_publication.json)
- [Retained complete witness package](https://chatgpt.com/library?file_id=libfile_d3a6b80e4b988191a38fea8c46cfc619&account_id=personal)
