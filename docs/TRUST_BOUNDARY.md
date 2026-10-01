# Trust boundary

This page states what each artifact in the repository establishes, what it takes on trust, and which statements depend on ineffective theorems. If a statement is not covered here, treat it as unverified.

## 1. What the Lean kernel proves

The Lean files are in `PerfectPower/`, including the machine-generated `PerfectPower/Generated/`. They are compiled against Lean `v4.20.0` and Mathlib `v4.20.0`, both pinned in `lean-toolchain` and `lake-manifest.json`. `audit/check_axioms.sh` checks every audited declaration: each may depend only on `propext`, `Classical.choice` and `Quot.sound`, so there is no `sorryAx`, no `Lean.ofReduceBool` and no custom axiom. The audited count is generated into the README by `make counts`.

Given that kernel, the following are theorems:

- **Definitions and elementary density facts.** The hit predicate, the count $A(N)$, the finite-support squeeze, exact finite surgery, and periodic rational density.
- **Rigid branch.** Either $F=G^d$ over $\mathbb Z$ or the hit set is finite; the density exists and is $0$ or $1$.
- **Explicit families.**
  - Twisted powers are finite.
  - For monomials $n^r$ the count is exact.
  - The hit indicator of $c\,a^n$ is $d$-periodic, so its density is $P/d$.
  - $2n^2+1$ has infinitely many square values and density zero.
  - Ljunggren's quartic has hit set exactly $\lbrace 3\rbrace$.
- **Runge reduction in integer form** (`runge_pointwise`, `runge_finite`).
- **Generated hit sets.** Each statement of the form "for $n\ge1$, $F(n)=m^d$ is solvable iff $n\in H$", for the polynomials named in `PerfectPower/Generated/`. Python proposes the data, and Lean checks the proof. **A compiled generated theorem does not depend on the Python code being correct.**

**Unconditional function-field results.**
- Davenport's bound $2\deg(f^3-g^2)\ge\deg f+2$ (`davenport`), derived from Mathlib's Mason–Stothers (`Polynomial.abc`).
- Its sharpness (`davenport_sharp`).
- Function-field Pillai (`pillai_polynomial`, `pillai_polynomial_balanced`): for coprime $f,g$ with $f$ nonconstant and $f^a\ne g^b$, $a\deg f+1\le\deg f+\deg g+\deg(f^a-g^b)$.

**Counting and geometry pieces.**
- Theorem B count: $|vA(N)-RW|\le2Rv$ (`radical_count_bound`).
- Pell orbits: finitely many representatives exhaust the solutions of the norm equation (`pell_orbits_exhaust`), with pure periodicity modulo $2A$ (`unitOrbit_periodic`), and the Pell-type count is $O(\log N)$ (`pell_count_log`).
- The combinatorial half of Theorem G (`S_le_one_iff`, and the exhaustive table `profile_table_ok` for $d,\deg F\le12$).

**Exact counts and named premises.**
- `pell_exact_count` gives the Pell count with its exact constant for any quadratic with a given unit.
- `radical_asymptotic_int` gives the radical count for the normalised family.
- `atlas_finite` proves finiteness only *under* the premise `SuperellipticSiegel`, which is stated in `Atlas.lean` and not proved.
- The 1163 theorems of `Generated/MordellDescent.lean` (no integral points on $y^2=x^3+k$) are `LEAN_CERTIFIED`: they assume nothing beyond the standard axioms. The Python generator only *searches* for the parameters $(D,c,b,M,j,b_1,u)$; Lean re-checks each condition. They cover only curves with no integral points. The one unconditional *nonempty* family is `MordellFLT3.lean` ($y^2=x^3-432u^6$, points $(12u^2,\pm36u^3)$), which rests on Mathlib's proof of Fermat's Last Theorem for exponent 3. `MordellMinus2.lean` ($y^2=x^3-2$) and `MordellMinus4.lean` ($y^2=x^3-4$) close two rank-one curves with no hypothesis, and the class-number-2 template `ClassTwo.lean` closes $y^2=x^3-13$ (points $(17,\pm70)$) and reproves $y^2=x^3-5$, $x^3-6$ empty. Its only per-curve inputs are finite tables that the kernel checks. `Transport.lean` carries such lists through affine substitutions and into `Genus1`'s checker, via a premise that asks only for points in the image of the change of variables. Every other nonempty genus-one list here still rests on Sage.
- The complete lists for $y^2=x^3-D$, $D=7,28,63$ (`Generated/Field756.lean`) $D=18,23,45,89$ (`Generated/Minus18.lean`, `Minus23.lean`, `Minus45.lean`, `Minus89.lean`, through solution-carrying descent to registered unit equations), and the `D = 72` residual (`D72Residual.residual_empty`) hold only *under* Matveev's lower bound for linear forms in three logarithms. It is stated per class as `matveev_i`: three explicit instances of `AnalyticBridge.MatveevLB`, whose constants come from height bounds computed in Python. Everything else in these theorems is proved, including unit generation, the norm representatives and the analytic inequality. The analytic inequality comes from a rational interval certificate checked by the kernel (`AnalyticBridge.analytic_of_cert`). These theorems are not counted as closed.
- The 399 genus-one theorems of `Generated/Genus1.lean` hold only *under* their named hypotheses `IntegralPoints_…`, which say that Sage's point lists are complete. That is the label `LEAN_REDUCTION_PLUS_INDEPENDENT_POINTS`, not `LEAN_CERTIFIED`.

**Verified checkers.** `Reflect.check_sound`, `Reflect.rungeCheck_sound` and `Reflect.mordellOK_sound` are proved once. Every generated certificate (Runge and sandwich) and every census block is data that the kernel runs through these checkers (`decide +kernel`, no `Lean.ofReduceBool`).

**Conditional results (abc as a hypothesis).** The following are implications "`ABC ε C` ⇒ …":
- `hall_of_abc`, for coprime $x,y$;
- `pillai_bound_of_abc` and `pillai_finite_of_abc`, for coprime bases and $(a,b)\ne(2,2)$.

abc is an ordinary proposition passed as an argument, so the axiom audit is unaffected. These theorems say nothing about whether abc is true.

## 2. What the Lean kernel does not prove

- **The Python classifier's type assignments** (`atlas.py`): power, radical, Pell or finite. Nor does it prove the constants $\kappa$, the structural counts, or the shift spectrum. These are paper proofs, cross-checked against direct scans.
- **Siegel's theorem, and anything resting on it.** Through Theorem G of the research notes, it now replaces the secondary-source LeVeque statement. That covers the finite type of the atlas, the exponent spectrum $\lbrace 0,1\rbrace \cup\lbrace 1/t\rbrace$ as a complete list, and Corollary K. Siegel's and Boshernitzan's theorems are likewise outside the kernel.
- **That scan-only rows are complete.**
- **Hall's conjecture, Pillai's conjecture, or any uniform integral-point bound.** No part of the repository proves these, and none is claimed. See `FRONTIER_PLAN.md`.
- **Completeness of the Mordell census** (`data/mordell_census.csv`). That is Sage's claim: Mordell–Weil generators from mwrank, saturated, then elliptic-logarithm sieving. It is rigorous modulo the correctness of that software and of the proved rank. Lean checks no row of the census.
- **The Sage cross-validations** (cubic table, genus-one families, binomial curves, Theorem G normalisation). These are external computations: Mordell–Weil generators from mwrank, then elliptic-logarithm sieving, or function-field integral closures. Lean never checks a Baker bound, a sieve or a normalisation. For the genus-one families, `crosscheck/check_genus1.py` recomputes the Weierstrass models, re-verifies every stored model point, redoes the pull-back, and reruns the exact scan to $10^6$ in plain Python. It does not rerun the Sage side.
- **The modular sieve** (`perfectpower/sieve.py`) as a program. Its soundness is elementary (a discarded residue has no $d$-th power value modulo $m$). It is tested against the plain scan, but it is not verified. Rows scanned with it are `EXACT_WITHIN_BOUND` evidence only.
- **The constraint compiler and the programs it generates** (`compiler.py`, `specialize.py`). The reductions they use are Lean theorems (`Reduction.lean`), and so are the completeness results they cite. Recognising a reduction, choosing a solver and executing a plan are Python. They are tested differentially against brute force, but not verified, and every plan reports `execution_verified: false`. Recognising a member of Mordell's family (`mordell_family_match`) is a bounded search. A match comes with its certificate, which Lean checks in the emitted theorem. A miss proves nothing. The descent certificates (`descent.py`) are discovered in Python and checked in full by the kernel through `Descent.tableB`. The Python class number is reported but not used by any proof. OEIS entries are **leads**: an entry is marked `DEFINITION_PROVED_EQUIVALENT` only when its definition, read from the committed `.seq` file, is formalized with the same offset and every listed term agrees. The formalization is either a human step (`SqrtTwoOrbit.lean`, `SqrtTwoBatch.lean`, recorded in the `PROVED` table of `oeis_orbit.py`) or the definition language (`oeis_dsl.py`). **The translation from English text to an encoding is unverified Python**. It is guarded by re-evaluating the encoding against every listed term, and each generated Lean block quotes the name it was read from, so a reader can compare the two. The Lean proof is then of the encoding, not of the English. `TRANSPORTED_FROM_DUPLICATE` rests on the entry's own "Duplicate of" text plus a term comparison. The Mordell obstruction classes (`descent.diagnose`) are diagnostics, not proofs. The branch compiler's certificates (`branch_descent.py`) are found in Python and checked in full by the kernel (`DescentBranch.branchB`, `pointsB`); an earlier Python test that Lean did not check was caught when the kernel rejected its certificate. The PARI Thue solutions of the 33 open curves (`crosscheck/branch_thue_pari.py`) are external computations (PARI's Baker-type bounds), labelled as such; they only label classes in `receipts/thue_graph.json`, and no Lean certificate depends on them. The cubic-field fingerprints (`crosscheck/thue_fields_pari.py`) are external and are not used as equivalences. The GL₂(ℤ) edges and the descent certificates are checked by the kernel. The partition into 79 classes is computed by a reduced-Hessian normal form: transport inside a class is certified, but that the classes are pairwise inequivalent rests on classical reduction theory, which is not formalized. The `galois_merge` adapters are a bounded cross-check, and so are the D = 72 local-solubility witnesses (`d72_local.py`, whose argument at the good primes is a Hasse–Weil paper proof) and the solution-preserving descent measurement (`descent_residual.py`); none of them is a proof of completeness. The shared-field pilot (`crosscheck/field756_pilot.py`) is external PARI data and computes no exponent bound. The `D = 72` and field-756 results (`Generated/D72Unit.lean`, `Generated/Field756.lean`) are proved in Lean under one named premise per class, `Analytic` (Siegel's identity, the conjugate estimates in mpmath interval arithmetic, and Matveev's theorem, `crosscheck/thue_bound.py`). Unit generation (`UnitGen.lean`) and the norm representatives (`NormRepProof.lean`, explicit division) are Lean theorems; `unit_basis_witness.py` and `norm_rep_localization.py` remain only as cross-checks. The direct reduction from the analytic inequality to the exponent box is a Lean theorem (`DirectReduction`), and its rational stages are evaluated by the kernel. The curves `D = 7, 28, 63` are not counted as closed. The compiler's solved-family registry (`receipts/mordell_registry.json`) is structured data from the generators' receipts; `make_mordell_registry.py` checks every entry against its Lean theorem statement with a full parse in both directions and fails on any gap, so the registry can omit nothing silently. The host-solver adapter (`smt_adapter.py`, optional, needs `z3-solver`) replaces a recognized conjunct `m^2 = (rn+s)^3 + k` by the complete list of a Lean-proved curve; the substitution step and the coefficient identity are checked in Python, and no Lean proof of the replaced SMT problem is emitted. Its benchmark (`receipts/host_adapter_bench.json`) uses constructed instances, not an independent workload. The script-level path (`smt_cert.py`) issues source-bound certificates re-derived by `check_certificate`; a checked replacement is still a Python-checked substitution plus a Lean theorem, not a proof any downstream verifier accepts. The Why3 bridge (`why3_bridge.py`) moves the substitution step into Why3: Why3 with z3 proves the replacement lemma and the VC, and the only imported fact is the curve theorem, stated in Why3 as Lean proves it (a `val lemma`). Why3 and z3 are then trusted for those steps, and GNATprove itself was not available. On the independent corpus (`independent_nia/`) it found zero replaceable conjuncts; solver status annotations and timings there are external measurements, not proofs. For A048624, the 16-term match and the uniqueness of the shift over all of ℕ are Lean theorems (`Interfaces.lean`); reading the dead entry as that infinite sequence is an adopted interpretation. Published Mordell solution counts (A081119/A081120) are used only for the cross-check and the ranked leads. The missing premise reported for `NOT_ENUMERATED` genus-one plans is a statement, not a result. The catalogued plans' count constants and least solutions are computed and checked in the kernel (`FilteredAuto.lean`). The Python counterparts (`count_cert`, `iter_hits`) are what the compiler uses for other plans. Filtered Pell decisions have Lean theorems (`FilteredPell.lean`), and the 18 catalogued plans in `Generated/Plans.lean` have 24 kernel-checked theorems about their original constraints, including counts whose constants are certified (`FilteredCount.lean`); a plan cites its theorem when it has one. The Galois front end (`galois.py`, with the factorizer `factor.py`) is explanatory Python; it reports the root field and the Pell unit field separately. A plan's status (`COMPLETE_FINITE`, `STRUCTURED_INFINITE`, `STRUCTURED_FILTERED`, `CLASSIFIED_FINITE`, `NOT_ENUMERATED`) inherits the label of its justification: a plan justified by the atlas classifier carries the classifier's status (paper proof, tested), not Lean's. `BOUNDED_EVIDENCE` is evidence only.
- **The Python Runge enumerator and the v0.5 cutoff certificate as programs.** Their mathematics is Theorem R, whose reduction step is compiled. The Python code is tested, including planted-hit adversarial tests, but it is not verified.

## 3. Conditional and ineffective inputs

| Statement | Depends on | Effective? |
|---|---|---|
| Density zero outside the rigid branch (monograph §3) | Boshernitzan's equidistribution criterion | Qualitative only |
| Atlas finite type, exponent spectrum as a complete list, $O(N^{1/p})$ barrier, Corollary K | Siegel (standard form) via Theorem G; historically LeVeque (1964) | **No.** Siegel is ineffective. Brindza's effective version exists in principle, but its bounds are astronomical, and none is computed here. |
| Second proof of the 0–1 law (research notes §1) | Siegel, via Theorem G | **No.** It cannot replace the Boshernitzan argument where effectivity matters. |
| Shifted exponentials $c\,a^n+k$ finite | Thue, the S-unit theorem | Thue is effective via Baker; no bounds are computed |
| Each Mordell curve $y^2=x^3+k$ has finitely many integral points | Siegel; effective via Baker | Yes. The census lists come from Sage, not from explicit Baker bounds computed here. |
| Pillai: finiteness for fixed $(a,b)$ | Siegel, via Theorem G; effective via Baker | Not computed here |
| Pillai: finiteness uniform in the exponents; Hall's inequality | **abc (open)** | Formalised only as implications |
| Radical and Pell counts, Theorems P, B, C | Elementary; paper proofs | Yes, explicit |
| Rigid-branch complete hit lists | Theorem R; elementary | Yes, explicit |

**LeVeque is no longer a dependency.** Theorem G in the research notes derives the finite type directly from Siegel's theorem in its standard form. That form is stated in Hindry–Silverman (Theorem D.9.1) and Bombieri–Gubler (§7.3): an affine curve with $2g-2+n_\infty>0$ has finitely many $S$-integral points. The derivation is a Riemann–Hurwitz computation, $\chi=d'(1-S)$, carried out for each geometric component of $y^d=F(x)$. It treats common multiplicities, the normalisation of singular points, fields of definition, and integrality with bounded denominators after normalisation. Its status is `PAPER_PROOF`, not independently refereed. It is backed in three ways:
- randomized consistency checks: the genus comes out integral and non-negative, and $\chi<0$ exactly for the finite type;
- an independent computation over every profile with $d\le8$ and $\deg F\le8$ (462 cases): Singular's normalisation genus in every case, and Sage's places at infinity where they finish within the time limit (`receipts/theorem_g_check.json`);
- a Lean proof of the combinatorial half (`ProfileG.lean`).

A referee needs to trust only the Kummer/Riemann–Hurwitz step for the normalisation. Proof step 2 counts $d'$ geometric points over an unramified $x$; an earlier draft said "one point", which was a wording error. The LeVeque statement (Acta Arith. 9 (1964) 209–219) was only ever taken from secondary sources, because the primary paper could not be read in the build environment. It is now historical context and matches Theorem G's conclusion.

## 4. Epistemic label of every data row

Every data row carries one label: `receipts/atlas_benchmarks.json`, `data/families.csv`, `data/mordell_census.csv` (which also names the engine and version) and `data/pillai_gaps.csv`. The labels are:

| Label | Meaning |
|---|---|
| `LEAN_CERTIFIED` | A compiled Lean theorem states the complete hit set. |
| `PROVED_STRUCTURAL` | A paper proof of the structure (Theorems P, B, C), with counts cross-checked against scans. |
| `COMPLETE_HIT_LIST` | Theorem R plus exact arithmetic; not formalised for this instance. |
| `INDEPENDENT_COMPUTATION` | Our scan agrees with a certified external computation (Sage integral points; `receipts/cubic_crossval.json`). |
| `LEAN_REDUCTION_PLUS_INDEPENDENT_POINTS` | Lean proves the reduction to an elliptic curve, the congruence filtering, and that every surviving point is a hit (`PerfectPower/Binomial.lean`). Completeness of the curve's integral-point list is an explicit hypothesis, certified by Sage (`receipts/binomial_curves.json`: rank proved, basis saturated). |
| `CONDITIONAL_ON_UNPROVEN_RANK` | A Sage integral-point list computed from generators whose rank mwrank could not prove. Complete only if the rank is right. Used in `data/mordell_census.csv`. |
| `CONDITIONAL_ON_UNSATURATED_BASIS` | A Sage integral-point list whose generator basis Sage could not show saturated. Defined for `data/mordell_census.jsonl`; no row currently carries it. |
| `SCAN_DISAGREEMENT` | Sage's list and our independent scan disagree for $\lvert x\rvert \le10^5$. Such a row is never certified. Defined for the census; no row currently carries it. |
| `EXACT_WITHIN_BOUND` | An exhaustive enumeration, complete up to the stated bound and silent beyond it. Used in `data/pillai_gaps.csv`. |
| `SCAN_EVIDENCE_ONLY` | Finiteness is conditional on Siegel (Theorem G). The listed hits are those with $n\le10^5$. **No completeness claim is made.** |

**The census gate.** `make receipts` runs `crosscheck/mordell_census.py --from-jsonl 10000`, which checks `data/mordell_census.jsonl` in plain Python before it rebuilds the CSV and summary.
- *Domain.* The keys are exactly $\lbrace -10000,\dots,-1,1,\dots,10000\rbrace$, once each and in order, so a duplicated row cannot hide an omitted curve. Every curve is $[0,0,0,0,k]$, and every $x$-list and scan list is strictly increasing.
- *Rows.* The SHA-256 of each $x$-list is recomputed, each $x^3+k$ is checked to be a square, the stored scan is compared with the listed points for $|x|\le10^5$, and the label is recomputed from `rank_proved`, `saturation_index` and that comparison. A row whose scan cross-check fails cannot carry `INDEPENDENT_COMPUTATION`.
- *Not rerun.* The scan itself is stored data here. Only the Sage run (`make crosscheck`) recomputes it.

`python/tests/test_gates.py` plants a duplicate plus an omission (same row count), an out-of-bound key, unsorted and duplicated $x$-lists, a failed scan and an off-curve point, and checks that each is rejected.

**The binomial gate.** `make receipts` also runs `crosscheck/check_binomial.py`, which ties `receipts/binomial_curves.json` to the Lean source without Sage. It checks that:
- each curve has a proved rank and a saturated basis;
- every receipt point lies on its curve;
- the receipt's $x$-list equals the disjunction in `IntegralPointsCubePlusOne` or `IntegralPointsCongruent6`, parsed from `PerfectPower/Binomial.lean`;
- the points proved in `binomial_curve_points_valid` are the receipt's points with $y\ge0$;
- a scan over $|X|\le10^6$ finds nothing else;
- pulling the points back through the reductions gives exactly the hit lists of `choose_two_cube_hits` and `choose_three_square_hits`.

It writes `receipts/binomial_gate.json`. `make crosscheck` reruns the Sage computation (`crosscheck/binomial_curves.py`). Completeness beyond $|X|\le10^6$ remains Sage's claim and Lean's hypothesis.

The cubic cross-validation shows why the last label matters. Among the 622 curves $m^2=n^3+an+b$ with $|a|,|b|\le12$, a scan to $10^3$ would have missed hits on 18 curves, and a scan to $10^4$ on 4. The largest hit is $n=80327$, at $(a,b)=(-12,-10)$.
