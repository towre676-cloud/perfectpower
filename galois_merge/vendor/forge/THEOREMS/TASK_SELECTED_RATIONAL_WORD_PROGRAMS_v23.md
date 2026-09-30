# Task-selected characteristic-zero synchronized word programs -- Forge v0.23

## 1. Scope

V0.22 deliberately refused to reconstruct the complete 127-dimensional rational coupling lattice. V0.23 follows that decision literally. It selects the two concrete one-dimensional Hecke tasks supplied by EQ-LAB -- the cost-aware two-route sensor `A_12+A_48` and the canonical Paley line -- and lifts only their certified optimal native masks:

- degree 8, `(r_+,r_-)=(0,2)`, using minus channels 1 and 2;
- degree 9, `(r_+,r_-)=(1,0)`, using plus channel 1.

The four resulting synchronized programs are characteristic-zero rational identities in the deterministic integral `G/H` ISA of v0.21. They are verified directly against the integral native and Hecke word-evaluation matrices. No finite-field equality is used as the final certificate.

## 2. Exact four-program ledger

| task | native mask | max degree | support | prefix primitive cost | common denominator bits | max numerator bits |
|---|---:|---:|---:|---:|---:|---:|
| `A_12+A_48` | `(0,2)` | 8 | 488 | 833,035 | 4,652 | 4,640 |
| `A_12+A_48` | `(1,0)` | 9 | 633 | 1,081,036 | 6,007 | 5,999 |
| Paley | `(0,2)` | 8 | 488 | 833,035 | 4,623 | 4,608 |
| Paley | `(1,0)` | 9 | 633 | 1,081,036 | 5,979 | 5,969 |

Every coefficient on the selected prefix supports is nonzero. The degree-eight programs use the first 488 breadth-first `G/H` words; the degree-nine programs use the first 633. The native output is verified to vanish identically outside the declared mask, while the Hecke output is verified to equal the requested target after clearing the stored common denominator.

The prefix execution ledger uses the v0.21 primitive costs `cost(G)=1732`, `cost(H)=1689`. The 488-word prefix has 487 extension edges, split 244 `G` and 243 `H`, so its exact proxy is

`244*1732 + 243*1689 = 833035`.

The 633-word prefix has 632 extension edges, split 316/316, giving

`316*1732 + 316*1689 = 1081036`.

## 3. The arithmetic Pareto front is opposite the native-state Pareto front

The degree-nine schedule still wins overwhelmingly in native state size. A one-plus section uses five native coordinates and inherited arrow proxy 30, while the degree-eight two-minus section uses 150 coordinates and proxy 3000.

But the synchronized rational word program moves in the opposite direction. For the two-route sensor, degree nine uses 145 additional words, about 29.77 percent more shared-prefix primitive work, and 1,355 additional coefficient-height bits. For Paley the corresponding height increase is 1,356 bits. Thus one extra word degree buys a 150-to-5 native-state collapse but worsens the canonical synchronized rational program on support, prefix work, and height.

This is the first exact characteristic-zero demonstration that polynomial depth, native execution state, and synchronized arithmetic conditioning are genuinely independent compiler resources.

## 4. Application-side bypasses remain part of the Pareto set

For the two-route sensor, the direct physical implementation from EQ-LAB v0.13-v0.15 is still the relevant application endpoint: two height-one route calls, routes 12 and 48, with route-work 120 per node. Forcing that statistic through the synchronized `G/H` language is mathematically exact but much more expensive arithmetically.

Paley has its own unconstrained endpoint. In EQ-LAB v0.15, the primitive-aligned synchronized Paley program is simply the one-word program `H`, coefficient height 1, primitive cost 1689, with native rank pair `(1,3)`. The new 488/633-word programs are not replacements for that endpoint; they are the exact price of imposing the restricted native schedules `(0,2)` and `(1,0)`.

The compiler should therefore expose at least three cost axes for a one-dimensional task: physical-route execution, unrestricted synchronized execution, and restricted native-section execution.

## 5. Single-prime sparse-support accidents are rejected

A one-free-coordinate search at the original certification prime `p=1,000,003` found apparent 487-word degree-eight and 632-word degree-nine reductions. V0.23 audits those candidate support collisions at four additional primes:

`1,000,033`, `1,000,037`, `1,000,039`, `1,000,081`.

The original prime produces 5 sensor degree-eight candidate collision groups, 79 sensor degree-nine groups, 1 Paley degree-eight group, and 79 Paley degree-nine groups. **Zero** survive at any of the four independent primes. The one-word reductions are therefore characteristic-specific accidents and are not promoted to characteristic zero.

This audit is intentionally weaker than a global sparsity theorem. The 488/633 supports are exact stable characteristic-zero programs on deterministic prefix supports. V0.23 does **not** prove that no unrelated support of size 487 or 632 exists over `Q`.

## 6. Formation v38 correction and final full-outer finite-simple shape theorem

V0.22 imported the v37 binary outer-residual collapse. Formation v38 sharpens the interpretation. The outer **residual shadow** is indeed binary, but the exact integral center of a mixed critical packet need not be elementary. If active local 2-primary reservoir depths are `d_i`, the mixed all-ones lock has center order

`2^E`, `E=max_i d_i`.

Within the exact v14 semisimple central-quotient universe for finite nonabelian simple species under the full outer action, every critical object has one of three shapes:

1. one centerless simple group;
2. one-species cyclic prime-power central atom, including the isolated two-copy binary zero-sum local form;
3. a multi-species binary all-ones lock on exactly one copy of each species.

No multiprime critical center, odd-prime mixed criticality, higher-dimensional mixed projective code, relative p-adic phase, full-support cancellation tether, or v36 section witness remains in that full-outer criticality branch. The broader v33-v36 machinery remains live outside this scope.

## 7. Evidence boundary and next compiler problem

The four rational programs are exact characteristic-zero certificates and are machine-verifiable. Their large heights are properties of the selected breadth-first prefix bases, not lower bounds over all synchronized word dictionaries. The multi-prime audit excludes only the specific one-coordinate support drops found by the finite-field search.

The next high-value problem is therefore basis design rather than whole-lattice reconstruction: search for task-specific word dictionaries whose evaluation matrices have smaller arithmetic height while preserving the same native mask, then compare support, common-prefix DAG cost and numerator/denominator height. The two-route sensor and Paley remain the correct paired benchmarks because they separate a physical bypass from a canonical Wilson observable while sharing the same native section geometry.

Machine data: `DATA/RELATION/TASK_SELECTED_WORD_PROGRAMS_V23/`.
Reproducer/verifier: `scripts/analyze_task_selected_word_programs_v23.py` and `tests_v23/`.
