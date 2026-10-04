# PerfectPower


The [parallel-session Lean formalization](docs/PARALLEL_LEAN_MONOGRAPH.md) proves exact weighted Hodge algebra, integral divisor-coordinate solving, symplectic basis transport, polyhedral Voronoi exclusion rules, finite clock/shift commutants, recovered power-sum identities, and the original PSG deweighting identity. It proves complete power-coordinate enumeration for all 3,080 quartic families at every nonzero power, and kernel-checks all 12,320 stored plain/affine lifting packets. The newest enhanced push also receives complete scaled affine lifting, a global modulo-16 quartic obstruction, exact quadratic completion and the complete tied integer minimizer example. Exact stored surface and Hodge matrices are checked independently of numerical periods. The focused axiom audit covers 12,835 declarations through 577 proof groups; 177 new modules compiled. Run `scripts/check_parallel_push.sh`; analytic identification, numerical quadrature certification and global solver bounds remain open.
The [enhanced machinery](docs/ENHANCED_MACHINERY_MONOGRAPH.md) rebuilds recovered ideas into an integrated exact solver: canonical affine/power coordinates, complete residue covers, finite quartic/Runge leaves and divisibility-preserving integer lifting. It solves and replays all 12,320 stored pullbacks and constructed affine variants, including expanded equations of degrees 12, 40 and 15 with answers at `10³⁰`. An exact integer optimizer combines saturated Smith fibres, weighted basis reduction and complete ellipsoid enumeration, preserves every tied optimum, and uses the actual stored divisor-feature metric. Run `python python/enhance_machinery.py`, or use `exact-solve` and `nearest-lift`. The audit inventories all 22 preceding monographs and older inspirations; the new execution is exact Python with replayable certificates, with no new Lean compilation or industrial-superiority claim.

The [deep historical recovery](docs/DEEP_GEMS_MONOGRAPH.md) builds four constructions from February–March 2025 and March–June 2026: exact weighted Hodge projectors, complete positive-box searches for sums of powers, polynomial power-coordinate quotients with integer lifting, and exact finite Fourier/chirp commutants with maps between levels. Square and cube lifting of all 3,080 existing quartic proof packets gives 6,160 derived equations and 5,255 point occurrences; the runner checks every outer polynomial and literal point packet against the saved kernel ledger. All six stored surface models receive weighted decompositions. Run `python python/recover_deep_gems.py`, or use the `power-composition`, `power-sums`, `weighted-hodge`, and `finite-weil` commands. The monograph corrects the old common-divisor, regularized-projector and coefficient-symmetry shortcuts and separates current exact Python results from inherited Lean proofs.

The [January arithmetic-kernel recovery](docs/DIVISOR_KERNEL_RECOVERY_MONOGRAPH.md) adds exact divisor coordinates, matrix-free GCD and normalized occupancy actions, complete raw rational/integer linear fibres, and an integral tridiagonal threshold inverse. It replays all 8,358 stored divisor-sum power hits, checks the divisor identity at one million coordinates, and constructs their exact seven-set Gram matrix without enumerating nearly 70 million pairs. Run `python python/recover_divisor_kernel.py --benchmark` for the exact corpus results and a fresh 50,000-coordinate run. The recovered mathematics also corrects the old unconditional positivity and non-normality claims.

The [native higher-power Runge engine](docs/NATIVE_RUNGE_POWER_MONOGRAPH.md) now recognizes expanded degree-`dn` inputs with nonzero integer `d`-th-power leading coefficient, for `d ≥ 2`. It proves the power-gap bound, extracts integer roots by a proved binary algorithm, and generates complete original point packets, including negative odd powers. `native_runge_power cubic for [1,1,0,1], 3` proves exactly `(-1,-1)` and `(0,1)`. Run `scripts/solve_native_runge_power.sh '1,1,0,1' 3` or `scripts/check_native_runge_power.sh`. Exact powers retain the negative branch precisely for even exponents; certificate-only mode handles unevaluated large searches.

The [native Runge recognizer](docs/NATIVE_RUNGE_MONOGRAPH.md) now takes expanded even-degree polynomials with positive square leading coefficient, proves an unconditional effective bound, and generates complete integer square-value lists directly in Lean. `native_runge sextic for [1,1,0,0,0,0,1]` proves all four points of `y²=x⁶+x+1`; exact squares receive parameterized relations. Certificate-only mode proves completeness of a finite search without evaluating a huge packet. Run `scripts/check_native_runge.sh` or `scripts/solve_native_runge.sh '1,1,0,0,0,0,1'`.

The [August 2025 recovery monograph](docs/MONOMIAL_RECOVERY_MONOGRAPH.md) adds exact multiplicative equation solving: hidden-variable exponent elimination, complete positive-rational families, bounded positive-integer fibres and whole-query substitution. Recomputing the old four-equation presentation reveals a missed factor of three and its cube-compatibility condition. Run `python python/recover_monomial.py` to replay the recovered equations and all 1,562 stored prime-power and square-product cases.

Start with the [three end-to-end examples](docs/SHOWCASE_MONOGRAPH.md): ten complete nonlinear integer pairs near 10³⁰, exact square-triangular counts and residue filters under a 1,000-digit bound, and elimination of a complete arithmetic relation from whole SMT queries. Run `python python/run_showcase.py` to rebuild their results and standalone programs.

The [integer lifting monograph](docs/INTEGER_LIFTING_MONOGRAPH.md) completes the rational operator interface: all whole-number lifts, saturated integer kernels, simultaneous integral intertwiners, embedded lattice comparisons and exact affine elimination from whole queries. Run `python python/recover_integer_lifting.py` to replay the examples and all 23 existing order maps.

The [operator recovery monograph](docs/OPERATOR_RECOVERY_MONOGRAPH.md) adds constructive task sections, exact invisible-state witnesses, simultaneous intertwiners and Fitting decompositions. It processes all 135 recovered recurrence models, establishes all-future equality for seven supplied generating-function models, and applies the recovered carriers to all seven field-756 Thue packets, recovering their 14 listed points in a signed unit box.

The [sequence recovery monograph](docs/SEQUENCE_RECOVERY_MONOGRAPH.md) recovers reusable machinery from the Padovan, tube-operator, Wilson and Formation work: exact signed recurrences, bounded modular reconstruction, formal differential operators, quotient projectors and phase-sensitive finite subgroup censuses. The new sequence atlas checks all 149 staged OEIS sequence files and records 135 finite-prefix recurrence candidates, with seven supplied generating-function bridges.

PerfectPower helps answer a deceptively simple question: **when does a formula produce an exact square, cube, or other whole-number power?** A search can find examples and still miss a distant answer. For the families this project supports, it can produce a complete list or an exact rule for generating answers, together with a machine-checked proof. It also says explicitly when the answer remains unresolved. This makes it useful for replacing repeated searches with reusable, checkable results.

The new divisor route solves `y² = P(x)² + k` for every nonconstant integer polynomial `P` and nonzero integer `k`, using factor pairs and integer roots instead of a coordinate scan. For example, `y² = (x + 1000000)² + 1` has exactly `(-1000000, ±1)`. The Python compiler recognizes expanded inputs of this form; the native Lean command independently checks a complete point list. [Algorithm, reusable arithmetic, and verification](docs/DIVISOR_REUSE_MONOGRAPH.md).

The new [solution-chart framework](docs/GEOMETRIC_LANGLANDS_CONNECTION.md) also preserves partial progress: proved reconstructed cases, exact remaining obligations, and the number of original solutions over each reduced case. It takes a proof-organization lesson from Geometric Langlands and implements independent finite-set theorems; it does not claim a Langlands solution to arbitrary integer equations.

The [literature-derived arithmetic routes](docs/research/literature-routes-monograph.md) now include a completely proved mixed equation: `y⁴ + 2y³ − 9x²y² + 2xy − 15x − 7 = 0` has exactly `(-1,-4), (-1,-1), (-1,1), (-1,2)`. New reusable theorems handle quadratic discriminant projection, two signed unit exponents modulo certified periods, and cubic-to-Mordell transport. General exponent and Mordell height bounds remain explicit obligations. Run `scripts/check_literature_routes.sh` for the targeted proof audit and regression tests.

**Lean-native effective enumeration:** [the native power module](docs/NATIVE_POWER_START_HERE.md) proves coefficient-derived global bounds and computes complete integer point lists for `y² = (x² + ax + b)² + k`, with `k ≠ 0`. `native_near_square` emits an explicit set and its kernel-checked completeness theorem without Sage, Singular, Python or JSON. The same push classifies polynomial Fermat points over finite fields when `n ≥ 3` and the exponent is nonzero in the field, including all eight points of `f⁴ + g⁴ = 1` over `F₇[t]`, while explicitly retaining the Frobenius exception. These are supported families, not a universal Diophantine solver. [Mathematics, examples and remaining scope](docs/NATIVE_POWER_MONOGRAPH.md).

**When is $F(n)$ a perfect power, and how often?**
PerfectPower classifies the possible long-term patterns for every integer polynomial. It gives exact counts for the power, radical and Pell families, and complete hit lists when a finite-case certificate or an independently established integral-point list is available. It has three layers:
- **A Lean 4 library.** It proves the counts, complete solution sets, and the counting law for Pell orbits, and ties the orbits to published integer sequences.
- **A Python compiler.** It turns integer constraints into certified plans.
- **A comparison layer.** It checks those results against the OEIS, keeping term matches separate from proofs.

The [trust table](#what-to-trust-at-a-glance) says what is machine-checked and what relies on outside mathematics or software.

**New here? Start with [PerfectPower in the history of perfect powers](docs/HISTORY.md)**, and its companion [Perfect powers, computation, and the limits of solving equations](docs/HILBERT10.md) (Hilbert's tenth problem, and why complete answers exist for some families but not for all equations). The first essay is on where this work sits: from Catalan, Pillai and Tijdeman to the machine-checked Mordell-curve theorems. It also explains why "complete" here means a proof that reaches every input. Two companion pages:
- [The square–cube gap atlas](docs/GAP_ATLAS.md) gives Pillai's equation $a^2-b^3=\pm k$ for every $k\le100$, with the status of each answer.
- The compiler's four answers are: a complete list, a generator, an answer conditional on a named premise, or unresolved ([below](#the-four-answers)).

> Take $F\in\mathbb Z[x]$ and $d\ge2$. A *hit* is an $n\ge1$ with $F(n)=m^d$ for some integer $m$, and $A(N)$ counts the hits with $n\le N$.
> Only four behaviours are possible:
>
> | type | $A(N)$ | example |
> |---|---|---|
> | **power** | $N$ | $(n^2+1)^2$ |
> | **radical** | $\kappa\,N^{1/t}+O(1)$, $t\mid d$ | $4n+1=m^2$: $\kappa=1$ |
> | **Pell** | $\kappa\log N+O(1)$ | $2n^2+1=m^2$: $\kappa=1/\log(3+2\sqrt2)=0.5673\ldots$ |
> | **finite** | $O(1)$ | $n^4+1=m^2$: no positive hits |
>
> Root multiplicities identify the candidate families; exact residue and Pell-orbit tests determine whether a candidate has infinitely many hits. The constants $\kappa$ have exact formulas. The growth exponent always lies in $\lbrace 0,1\rbrace \cup\lbrace 1/t: t\mid d\rbrace$.

The classification is a **synthesis**, and we claim no priority for it. It combines Siegel's theorem, through the Euler characteristic $\chi=d'(1-S)$ of the curve $y^d=F(x)$ (Theorem G), with classical Pell and valuation counting. For a general finite-type polynomial, knowing that the hits eventually stop does not yet give an algorithm that lists all of them.

**One example, end to end.** Is $27n^3+405n^2+2025n+3319$ ever a square?

```python
>>> from perfectpower.compiler import compile_constraint, PowerConstraint
>>> from perfectpower.specialize import parse_poly
>>> p = compile_constraint(PowerConstraint(parse_poly('27*n**3 + 405*n**2 + 2025*n + 3319'), 2))
>>> p.status, p.all_hits(), p.justification[:2]
('COMPLETE_FINITE', [(1, [-76, 76])], ['PerfectPower.Generated.MordellThue.minus56', 'PerfectPower.DescentThue.complete_of_thue'])
```

1. **Recognition.** The compiler recognizes the cubic as $(3n+15)^3-56$, so a hit is an integral
   point of $y^2=x^3-56$ with $x\equiv0 \pmod 3$ and $x\ge18$.
2. **The curve's complete list.** It is $(18,\pm76)$, and it is a Lean theorem
   (`Generated/MordellThue.lean`, `minus56`):
   - every point enters one of finitely many branches of Thue's lattice argument;
   - eight branches are field cubes;
   - the four Thue branches are transported by unimodular matrices to one equation,
     $-3u^3-45u^2v+504uv^2+840v^3=729$, which a 3-adic descent certificate proves impossible.
3. **The original expression.** The complete list is pulled back through $x=3n+15$, and the kernel
   checks the resulting theorem about the original expression (`Generated/Plans.lean`,
   `plan_thue_minus56`):

   $$1\le n \;\wedge\; m^2=27n^3+405n^2+2025n+3319 \iff n=1 \;\wedge\; m=\pm76.$$

   Nothing in that proof trusts the Python that found it.

<a id="the-four-answers"></a>**The four answers.** Every plan reports `plan.answer`, one of four things a consumer can act on, and `plan.certificate`, the boundary of what is proved where:

| `answer` | meaning | example |
|---|---|---|
| `complete_list` | every solution, with a Lean theorem and no added premise | $n^3+33=m^2$: none with $n\ge1$ (`ClassLists.K33.plus33`) |
| `generator` | infinitely many, generated exactly (power, radical or Pell orbit) | $2n^2+1=m^2$ |
| `conditional` | a complete list from a Lean theorem that assumes named premises, listed in the certificate | $n^3-15=m^2$: $n=4$, under `matveev_n1`…`matveev_n4` (`Minus15.minus15`) |
| `unresolved` | finite by Siegel, no complete list here; the plan refuses to enumerate and names the missing premise | $n^3+19=m^2$ |

`plan.certificate` lists the Lean theorems, the named premises, the Python reduction steps, and `execution_verified: false`: the Python that runs a plan is not itself verified.

**As a component of another solver** ([HOST_ADAPTER.md](docs/HOST_ADAPTER.md)).
`python3 -m perfectpower.smt_adapter TASK.smt2` replaces solved conjuncts of an SMT-LIB task by
their complete solution sets, each an exact equivalence over ℤ, and hands back the smaller task.
- On two verification-condition-shaped examples, z3 alone returns `unknown`, and after the
  reduction it proves both in milliseconds.
- On 48 constructed instances, the 24 impossibility tasks (no point satisfies the system) are proved by the adapter in all 24 cases, against 1 for z3 alone. On genuinely satisfiable instances z3 alone already finds 10 of 12 witnesses.
- Recognition costs about 2 ms on unrecognized tasks (classifier overhead only).

**Bounded Pell queries are kernel-checked by default:** for `2 ≤ N ≤ 10⁹`, all 24 solutions of $N(N-1)=2S^2$ are a Lean theorem (`BoundedPell.quad_bounded`; each unit step at least doubles the orbit, so 32 steps cover the range). **Why3 accepts the replacement:** on three constructed verification conditions, Why3 (with z3) proves both the replacement lemma and the VC from the imported Lean theorem, and fails without it ([details](docs/HOST_ADAPTER.md)). These instances are constructed. On an independent corpus of 69 upstream QF_NIA files (12,860 queries, including 12,801 industrial ELSTER queries), the fail-closed script-level adapter finds **zero** replaceable conjuncts ([coverage report](independent_nia/reports/PERFECTPOWER_COVERAGE.md)).

**Industrial front-end replay:** a separate [bounded command transport](industrial_performance/REPLAY_README.md) preserves the original QF_NIA assertions and solver strategy. On all 181 pinned ELSTER files with a frozen first-32-query prefix (5,612 queries), fast command slicing and bounded native batches reduce summed replay wall time from 742.481 to 707.361 seconds (4.73%) and solve 64 more queries within the same 250 ms allocation. No SAT/UNSAT conflicts or native errors occur. Full-corpus slicing matches every one of 3,602,272 commands and is approximately 2.7 times faster. These are single-host front-end measurements, not a new arithmetic theorem or a full-corpus query run. [Raw results and scope](industrial_performance/REPLAY_MONOGRAPH.md) are retained; the earlier strategy portfolio remains opt-in because it regressed.

**An independently authored software workload** ([details](docs/ARITHMETIC_WORKFLOW.md), [`why3_isqrt/`](why3_isqrt/README.md)). Why3 1.6.0 exports 134 native-bitvector verification conditions from the unmodified Von Neumann integer square root (16, 32 and 64 bits). The Mordell/Pell adapter makes zero replacements there. A separate route adds guarded unsigned facts, `b ≤ᵤ n ∧ n ≤ᵤ x ⇒ n − b ≤ᵤ x`, proved in Lean for every word width (`BVWorkflow`; 307 source-bound instances, and 4 VCs with complete ground proofs). With z3 at 3 s, it raises the solved VCs from 128 to 130 and cuts the time from 28.5 s to 21.2 s; on the seven hard VCs over five seeds, from 3 to 13 of 35. The SMT-to-Lean translation is Python, not verified. **Native Why3 sessions** replay from a clean checkout (`make why3-session`). Used as a proof step on the subtraction-shaped goals (`subst_all; apply`), the rule proves the 64-bit subtraction invariant in 5 of 5 runs, where the baseline proves it in none, and loses no goal. Left as a lemma in the context, it helps nowhere. Planted bugs stay detected and legitimate code changes stay proved ([details](docs/ARITHMETIC_WORKFLOW.md)). **GNATprove**, built from source here, reproduces AdaCore's 8 unproved checks on its own Von Neumann regression. A selective ghost-lemma variant proves the six loop invariants only relative to lemmas it cannot yet discharge, so no AdaCore check is closed ([`spark_pilot/`](spark_pilot/README.md)).

**Try one in five minutes.** Follow the [tutorial](docs/TUTORIAL.md) to give the program $1+n+n^2+n^3+n^4$, find its square hit at $n=3$, and compile a Lean proof that there are no others.

---

## What is here

### 1. Exact counts, proved in Lean
`PerfectPower/Atlas.lean` gives one interface for all four types:
- **Pell:** `pell_exact_count` gives $|A(N)-\kappa\log N|\le K$ with $\kappa=\frac1{\log\varepsilon}\sum_\rho g_\rho/P_\rho$, over canonical orbit roots, so no orbit is counted twice.
- **Radical:** `radical_asymptotic_int` gives $|A(N)-\kappa N^{1/t}|\le K$, including $\kappa=0$, where local solvability does **not** give infinitely many hits.
- **Finite:** `atlas_finite` proves finiteness **from an explicitly named premise** (`SuperellipticSiegel`). The combinatorial half of Theorem G, "$\chi<0$ iff the profile is not of power, radical or Pell type", is proved for **all** $d$ (`chi_neg_iff`).
- **General input:** every nonzero $F$ reduces pointwise through its Yun decomposition (`PerfectPower/Continuation/`), so general radical and Pell polynomials are counted end to end, with all zeros, both signs and every branch.

### 2. Complete solution sets
- **Certificates you can re-check.** `pp-cert/1` is a small, hash-bound JSON format ([spec](docs/CERTIFICATE_FORMAT.md)). A Lean checker proved sound once turns each certificate into a kernel theorem. There are 19 complete hit sets, including Erdős–Selfridge instances. Mutated certificates are rejected, and `make cert-audit` rechecks the arithmetic independently.
- **Genus one, unconditionally:**
  - $y^2=x^3+k$ has no integral points for **1163** values $0<|k|\le10^4$ (`MordellDescent.lean`);
  - $n^3-432u^6$ is a square iff $n=12u^2$, for every $u\ne0$ (`MordellFLT3.lean`, via Mathlib's Fermat $n=3$);
  - positive-rank curves get exact integral points: $x^3-2$ has $(3,\pm5)$, $x^3-4$ has $(2,\pm2),(5,\pm11)$, and $x^3-13$ has $(17,\pm70)$.
- **Descent certificates for new curves** (`Descent.lean`, `descent.py`). For $y^2=x^3-D$:
  - the compiler finds a class-group certificate in $\mathbb Z[\sqrt{-D}]$ itself;
  - the kernel turns it into a complete, **nonempty** answer on the original polynomial. For example, $8n^3+12n^2+6n-73$ is a square only at $n=49$.
  - `make fresh` hands the compiler a random disguised cubic it has never seen, and Lean checks the file it emits.
- **Mordell's family** $k=(4t-1)^3-4m^2$ (`MordellFamily.lean`): one theorem covers every member, through every affine substitution.
- **36 previously unresolved curves closed by a branch compiler** ([MORDELL_BRANCH.md](docs/MORDELL_BRANCH.md), `DescentBranch.lean`, `DescentThue.lean`, `Generated/MordellBranch.lean`, `Generated/MordellThue.lean`).
  - **Method:** every solution of $y^2=x^3-D$ enters one of finitely many branches of Thue's lattice argument, with no coprimality, maximal-order, unit or class-number assumption. Each branch is closed by a kernel check, as a field cube (a reducible cubic, listed by divisors) or as impossible mod $m$.
  - **Result:** complete lists for **26 of the 59** unresolved curves with $1\le D\le100$, including $y^2=x^3-1$ (`MordellMinus1.lean`: every Gaussian unit is a cube, $i=(-i)^3$, and $2+2i=(i-1)^3$). Ten have Sage rank 0, twelve rank 1, four rank 2; all 26 agree with the Sage census and the published counts.
  - **Prediction tested:** the earlier diagnostic predicted 46; 22 of those closed, and 4 unpredicted curves closed too.
  - **The Thue workload as a graph:** the other 33 curves reduce to 316 explicit Thue equations. Certified unimodular transformations group them into **79 computed classes**, in 26 cubic fields. Transport inside each class is Lean-checked. Inequivalence between classes rests on classical reduction theory, which is not formalized, and a bounded independent search agrees (`receipts/galois_adapters.json`). The established equivalences share nothing across curves.
    - A new certificate, **p-adic descent on forms** (`ThueLocal.lean`), proves 15 of them impossible. It needs 178 nodes in total (220 before interning exact repeated subproblems), where plain residue lifting needs about 8 million steps and ran out of kernel memory.
    - Transported to every branch that uses them, these obligations close **10 more curves** (D = 29, 32, 36, 38, 52, 56, 77, 80, 86, 92).
  - **Still open:** 23 curves have Thue branches that carry points. PARI solves them unconditionally and agrees with Sage; that is external, not Lean.
    - **D = 72** is among the 23. Its two point-free classes are everywhere locally soluble, including the branch restrictions (`receipts/d72_local.json`), so no local certificate can close them. Solution-preserving descent reduces both to one unit equation, $-3u^3+9uv^2-2v^3=\pm1$. Lean proves it has no solution (`D72Residual.residual_empty`) under one named premise, Matveev's lower bound for linear forms in three logarithms (three explicit instances). Unit generation, the norm representatives and the analytic inequality are proved ([UNIT_PREMISES.md](docs/UNIT_PREMISES.md)). The direct maximum-exponent reduction, checked by the kernel, limits the exponents to 4.
    - Solution-preserving descent (`receipts/descent_residual.json`, measurement only) reduces the 64 classes without a descent certificate to 109 distinct unit equations. `ThueLocal.descM` adds multi-prime descent certificates, but they close nothing new: the only point-free classes left are `D = 72`'s two, which are locally soluble.
    - **D = 7, 28, 63, from one shared field, conditionally** (`Generated/Field756.lean`, [UNIT_PREMISES.md](docs/UNIT_PREMISES.md)). Seven classes of these three curves live in one cubic field of discriminant 756.
      - Lean proves the complete integral points (`minus7`, `minus28`, `minus63`; for example $(2,\pm1)$ and $(32,\pm181)$ on $y^2=x^3-7$) under **one named premise per class**, Matveev's lower bound (`matveev_i`: three explicit instances of `AnalyticBridge.MatveevLB`). The rest is now made of Lean theorems:
        - unit generation (`unitGen_proved`, from real embeddings, log enclosures and a kernel-checked box);
        - the norm representatives (`normRep_*_proved`, by explicit division by $t$ and $1+t$);
        - the analytic inequality (`analytic_i_proved`, from Siegel's identity, the conjugate estimates and the inverse log matrix, with a kernel-checked rational interval certificate).
      - Everything between the premises and the lists is kernel-checked: the direct maximum-exponent reduction (bounds 5 to 7), the norm identities, the exponent boxes, the small cases and the branch transport (`DescentThueList.complete_of_lists`). The box hits are exactly PARI's solutions.
      - The Matveev premise is the only external input. These curves are not counted among the closed ones.
    - **D = 23, through descent to two unit equations, conditionally** (`Generated/Minus23.lean`). The three open classes (8, 9, 10) descend, with a prime per node, to two unit equations in the field of discriminant 621: $F_1(u,v)=-u^3-3u^2v+6uv^2+4v^3=1$ and $F_2(u,v)=-u^3-6u^2v+69uv^2+46v^3=1$.
      - The pipeline:
        - both unit equations are solved by the field pipeline (unit generation, norm $1$, analytic certificate, reduction to $H\le6$, box);
        - solution-carrying descent certificates (`DescentLists.descL`) carry their lists back to the classes;
        - branch transport gives the points.
      - `minus23`: the integral points are exactly $(3,\pm2)$, under `matveev_u1` and `matveev_u2`. Classes 8 and 9 need only `matveev_u1`. The result agrees with the Sage census, and the curve is not counted among the closed ones.
    - **D = 45, one nonmonic source equation for three classes, conditionally** (`Generated/Minus45.lean`). Classes 30, 31 and 32 descend to $-2u^3-6u^2v+3uv^2+4v^3=1$.
      - Its encoding has norm $4$. `NormRepProof.normRep_of_res` proves by a residue certificate modulo $8$ that every element of norm $4$ is $(4+x)\cdot$unit. No class number is used.
      - `minus45`: the integral points are exactly $(21,\pm96)$, under `matveev_w1` alone.
    - **D = 18, in the order of the D = 72 residual, conditionally** (`Generated/Minus18.lean`). Classes 6 and 7 descend to $-u^3-3u^2v+6uv^2+2v^3=1$ and $-u^3-9u^2v+54uv^2+54v^3=1$ in $\mathbb{Z}[\theta]$, $\theta^3=9\theta+6$.
      - Unit generation is imported from the shared module `Generated/Order1944.lean`, which `D72Unit` also imports. It is checked once.
      - `minus18`: the integral points are exactly $(3,\pm3)$, under `matveev_v1` and `matveev_v2`. Class 6 needs only `matveev_v1`.
    - **D = 89, one order for both sources, conditionally** (`Generated/Minus89.lean`). Classes 68 and 69 descend to $-u^3-3u^2v+12uv^2+2v^3=1$ and $-u^3-18u^2v+267uv^2+534v^3=1$.
      - Both live in $\mathbb{Z}[\theta]$, $\theta^3=15\theta+12$, with $\varphi_1=1+\theta$ and $\varphi_2=6+5\theta$. The second source's own generator is $5\theta$.
      - The unit box has 2,548,975 triples. `UnitGenProof.unitGen_of_slab` enumerates only the 33,217 lattice points that the three embedding bounds allow.
      - `minus89`: the integral points are exactly $(5,\pm6)$, under `matveev_t1` and `matveev_t2`.
    - **D = 39, 47, 60, through order maps, conditionally** (`Generated/Minus39.lean`, `Minus47.lean`, `Minus60.lean`). Each curve's sources are moved into one target order along a Lean-checked map (`OrderEmbedding`, `Generated/OrderMaps.lean`). Two of the maps are isomorphisms, and one embeds into a larger order of index 2.
      - `minus39`: the integral points are $(4,\pm5)$, $(10,\pm31)$ and $(22,\pm103)$.
      - `minus47`: $(6,\pm13)$, $(12,\pm41)$ and $(63,\pm500)$.
      - `minus60`: $(4,\pm2)$ and $(136,\pm1586)$.
    - **D = 72, in the order of its own residual, conditionally** (`Generated/Minus72.lean`). Its four monic sources move into Order1944 with index 2, and its residual comes from `D72Unit`. `minus72`: the integral points are exactly $(6,\pm12)$.
    - **D = 15, 26, 48, 55, 71, with nonmonic sources, conditionally** (`Generated/Minus15.lean` and others). Their nonmonic sources get residue norm representatives, searched in a larger order (`python/norm_rep_search.py`). A nonmonic class that takes the value $\pm1$ is replaced by a monic representative. Sources with several representatives carry one analytic certificate per representative.
      - $D=15$: $(4,\pm7)$. $D=26$: $(3,\pm1)$, $(35,\pm207)$. $D=48$: $(4,\pm4)$, $(28,\pm148)$. $D=55$: $(4,\pm3)$, $(56,\pm419)$. $D=71$: $(8,\pm21)$.
    - **D = 25 and D = 100, through composable divisor covers, conditionally** (`NormCover.lean`, `Generated/Covers2700.lean`, `Generated/Minus25.lean`, `Minus100.lean`). In $t^3=15t+20$, a norm-4 cover (three elements, checked modulo 4) and a norm-9 cover (checked modulo 9) compose into norm representatives for $4, 9, 16, 36, 64$ and $4096$. This replaces residue tables of up to $4096^3$ entries. $D=25$: $(5,\pm10)$. $D=100$: $(5,\pm5)$, $(10,\pm30)$, $(34,\pm198)$.
    - **Coverage** (`receipts/descent_coverage.json`, derived from the registered Lean theorems): 96 of the 109 unit equations are registered, and all 23 curves with open branches are conditionally complete; no class is unresolved, so $U_{\mathrm{needed}}$ (the unregistered leaves of unresolved classes) is empty. The last five ($D=53,61,79,87,95$) went through shared orders and composable divisor covers; $D=79$ through a common overorder $t^3=60t+178$ of its three orders.
    - **Cost before proof** (`receipts/order_cost.json`): an estimate of the kernel work $C(D)$ for each unresolved curve, with shared orders charged once.

### 3. From constraints to certified plans
The constraint compiler (`python -m perfectpower solve`, [guide](docs/CONSTRAINT_COMPILER.md)) accepts constraints that do not mention powers:
- $F(n)=m^d$;
- "$F(n)$ is triangular";
- "$ay^2+by+c=F(n)$ has an integer root".

It reduces them exactly (`Reduction.lean`) and emits a plan with one explicit outcome.
- **Outcomes:**
  - a complete finite list;
  - an infinite family with a counting law;
  - for genus-one cubics that cannot be finished, the **exact missing premise**, stated as `Transport.IntegralPointsOnImage` on the Weierstrass model.
- **Filtered Pell families** are decided by their finite symmetry system (`FilteredPell.lean`).
- **Catalogued plans become Lean theorems** about the original constraint (`Generated/Plans.lean`):
  - the kernel computes the counting certificates itself (`FilteredAuto.lean`);
  - it proves least solutions. For example, $41y^2+y+3=n^2+3$ has least solution $n=655680$ and count $\tfrac12\log N/\log\varepsilon+O(1)$.
- **Generated programs:** a Pell scan becomes orbit iteration. $991n^2+1$ reaches its first square, at $n\approx1.2\cdot10^{28}$, in microseconds.

### 4. One orbit, many sequences
A Pell orbit is one arithmetic object, and a sequence in a table is usually one **coordinate** of it.
- **The counting law for observations** (`Observation.lean`): finitely many filtered orbits, with coordinates growing like $E^j$ and disjoint beyond a threshold, give a number of observed values $v\le N$ equal to

  $$\Big(\sum_\rho\frac{g_\rho}{P_\rho\log E_\rho}\Big)\log N+O(1).$$

  The observations need only be eventually increasing. The measured coordinate changes the constant, not the orbit.
- **Thirteen OEIS entries from $(1+\sqrt2)^k$** (`SqrtTwoOrbit.lean`). Each entry's definition is read from its original OEIS text with its offset, and proved equal to an exact coordinate of the orbit:
  - A000129 (Pell numbers);
  - A001541, A001542, A001109, A001108, A001110 (square triangular numbers);
  - A001652, A002315, A005319;
  - A001653, A055997, A084703, A075870, which are set definitions proved as increasing enumerations.

  Behind these are two orbits of $3+2\sqrt2$: norm $+1$ and norm $-1$, proved exhaustive. The Pell numbers count as the union of both, at rate $\log N/\log(1+\sqrt2)$ (`pell_count`).
- **A quadratic-unit orbit engine** (`QuadOrbit.lean`). For any positive nonsquare $D$, one kernel-checked `seedCheck` proves that finitely many seed orbits exhaust $x^2-Dy^2=\Delta$ (`complete`, `unique`). It also gives recurrences, residues mod $M$ as a periodic finite-state filter, two-sided geometric growth, and collision theorems.
- **A second discriminant, with the ring of integers** (`FibOrbit.lean`). The $\varphi$ orbit of $\mathbb Z[\varphi]$ splits into six seed orbits of the $\mathbb Z[\sqrt5]$ unit $\varphi^6$. The results:
  - $F_i=F_j$ only at $F_1=F_2$, repaired by the parity of the index;
  - $2\mid F_n\iff3\mid n$;
  - Fibonacci numbers count at $\log N/\log\varphi$, and even ones at a third of that.
- **Generated proofs from OEIS text** (`oeis_dsl.py`, `OEISLib.lean`, `Generated/OEISAuto.lean`). A small definition language translates recurrences, generating functions, coordinate expressions and the set pattern `D k^2 + c is a square`, with the entry's offset and domain. Each translation is checked against every term, and the compiler emits the Lean definition and its equivalence proof. **69 entries are proved this way**, including all 8 translatable entries of a withheld family ($2+\sqrt3$). Ten more $\sqrt2$ entries (Pythagorean triples, a matrix orbit, a coprime splitting, an exceptional set, a residue filter, and squares of other entries) are proved by hand in `SqrtTwoBatch.lean`.
- **The OEIS layer** ([OEIS.md](docs/OEIS.md)) reads a versioned local snapshot of the official `oeisdata` export: a Git adapter or a directory of `.seq` files, sharing one parser.
  - **Discovery:** a term-index search over all 399,743 entries finds 39 candidates for the $\sqrt2$ orbit, 57 for $\varphi$ and 19 for $2+\sqrt3$; a name scan finds 27 set definitions.
  - **Verification:** every candidate is re-checked against its full entry. On the $\sqrt2$ orbit:
    - 29 are proved equivalent, including A001333 through the continued fraction of $\sqrt2$ (`SqrtTwoBridges.lean`, with Euclid's primitive-triple classification);
    - 3 are proved equal to a coordinate outside a finite exceptional set;
    - 1 is transported from the proved entry it duplicates, and 1 (A048624) with the shift its terms fix (Lean proves the 16-term match and that `s = 2` is the only shift over all of ℕ; reading the dead entry as that infinite sequence is an adopted interpretation);
    - 5 agree without proof.
  - **The claim of a generated proof:** Lean proves the emitted definitions. Reading the English as that definition is an inspected translation, with its grammar and semantics in [DEFINITION_LANGUAGE.md](docs/DEFINITION_LANGUAGE.md) and every translation exposed in `receipts/oeis_translation_review.md`.
  - **Mordell cross-check:** all 77 Lean-certified Mordell lists with $|k|\le100$ match the published solution counts (A081119/A081120).

### 5. Evidence and frontiers
- **Hidden hits, caught.** Short scans miss real solutions: $6n^2-7n-6=95339^3$ at $n=12{,}017{,}947$. There are 399 such families with complete lists from a *named* hypothesis (Sage's point list), which is not proved in Lean.
- **Censuses.** These are evidence only: all integral points of $y^2=x^3+k$ for $0<|k|\le10^4$, and perfect-power gaps up to $10^{18}$ (Pillai). Hall and Pillai are open. The function-field analogues are proved (`davenport`, `pillai_polynomial`), and over $\mathbb Z$ they follow from abc as an explicit hypothesis.
- **The Pell oscillation.** The heat transform over Pell hits has a log-periodic second term (Theorem T2), checked numerically to order $\tau^2\log(1/\tau)$.

---

## Status in numbers

<!-- counts:begin (generated by python/make_counts.py; do not edit) -->
- Lean declarations audited: **2796**; using only `propext`, `Classical.choice`, `Quot.sound` (or a subset): **2796**.
- Machine-generated Lean hit-set certificates: **434**.
- Theorems conditional on named premises (Matveev's lower bound, three explicit instances per class; not counted as closed): **24** (`Field756.minus28`, `Field756.minus63`, `Field756.minus7`, `Minus15.minus15`, `Minus18.minus18`, `Minus23.minus23`, `Minus25.minus25`, `Minus26.minus26`, `Minus39.minus39`, `Minus45.minus45`, `Minus47.minus47`, `Minus48.minus48`, `Minus53.minus53`, `Minus55.minus55`, `Minus60.minus60`, `Minus61.minus61`, `Minus71.minus71`, `Minus72.minus72`, `Minus79.minus79`, `Minus87.minus87`, `Minus89.minus89`, `Minus95.minus95`, `Minus100.minus100`, `D72Residual.residual_empty`).
- Positive $k$: curves $y^2=x^3+k$, $1\le k\le100$, with complete integral-point lists in Lean and **no** premise (class lists proved, reducible classes solved; `Generated/ClassLists/K*.lean`): **73** (25 empty; 34 through irreducible rank-one sources, $k=1,2,3,4,8,9,10,11,12,15,17,18,22,24,25,33,37,41,43,44,48,49,54,57,64,65,68,73,81,82,89,97,98,100$, of which $k=9,12,17,18,37,64,65,89,97,100$ use a witness-normalized nonmonic source).
- Atlas families by certification label: `COMPLETE_HIT_LIST` 2, `INDEPENDENT_COMPUTATION` 2, `LEAN_CERTIFIED` 16, `LEAN_REDUCTION_PLUS_INDEPENDENT_POINTS` 7, `PROVED_STRUCTURAL` 19, `SCAN_EVIDENCE_ONLY` 5.
- Cubic cross-validation ($m^2=n^3+an+b$, $|a|,|b|\le12$): 622/622 certified by Sage, 0 disagreements with the scan to $10^5$.
- Adversarial Runge test: 220 planted-hit trials, 0 failures, planted hits up to 993,384,039.
- Mordell census $y^2=x^3+k$, $0<|k|\le10000$: 20000 curves, 8600 integral points; labels `CONDITIONAL_ON_UNPROVEN_RANK` 485, `INDEPENDENT_COMPUTATION` 19515; 0 scan disagreements ($|x|\le10^5$); best Hall ratio 4.870804 ($k=1090$, $x=28187351$).
- Genus-one cross-validation (non-monic/shifted $m^2=$ cubic, $m^3=$ quadratic): 400 families; labels `CONDITIONAL_ON_UNPROVEN_RANK` 1, `INDEPENDENT_COMPUTATION` 399; 0 disagreements with the exact scan to $10^6$; 3 certified hits beyond it (largest $n=12,017,947$).
- Generated Lean genus-one reductions: 399 theorems proving complete hit lists from a named hypothesis (Sage's integral points on the Weierstrass model); the hypothesis itself is not proved in Lean.
- Mordell curves $y^2=x^3+k$, $0<|k|\le10000$, proved in Lean to have **no** integral points, unconditionally (elementary descent, `MordellDescent.lean`): **1163**; 28 of them rest in the Sage census on an unproved rank; 0 conflicts with the census.
- Theorem G check ($d\le8$, $\deg F\le8$): 462 cases; Singular genus in all 462, Sage places at infinity in 453; 0 disagreements with $\chi=d'(1-S)$.
- Pillai gap census: 2856 pairs of perfect powers $\le 10^{18}$ at distance $\le 1000$ (exact within the bound).
<!-- counts:end -->

Every number above is regenerated by `make verify`, which fails if anything drifts. An earlier passing run is archived in [RELEASE_CHECK.md](docs/RELEASE_CHECK.md).

## What to trust, at a glance

| Label | Meaning | Examples |
|---|---|---|
| **Lean** | compiled; only `propext`, `Classical.choice`, `Quot.sound` | exact Pell and radical counts; 19 certificates; 1163 pointless Mordell curves; $x^3-2$, $x^3-4$, $x^3-13$; descent answers such as $8n^3+12n^2+6n-73$; the observation counting law; the quadratic-unit orbit engine; 36 complete lists from the branch compiler (with $y^2=x^3-1$), 15 Thue obligations by p-adic descent; 83 distinct OEIS definitions as orbit coordinates, convergents or seed-orbit enumerations; exact monomial and filtered counts (`MonomialCount.lean`) |
| **Lean ⇐ named hypothesis** | compiled, with an unproved premise stated as a `def` | finite type (`SuperellipticSiegel`), 399 genus-one lists, the binomials $\binom n2=m^3$ and $\binom n3=m^2$ |
| **Paper** | written proof, cross-checked by exact computation | geometric half of Theorem G |
| **External** | Sage, Singular or PARI, re-verified in plain Python by `make verify` | Mordell census, genus-one families, Theorem G check (462 cases, 0 disagreements), PARI Thue solutions of the 33 curves with Thue branches (23 still open in Lean) |
| **Lead** | a term match or a published count, never a proof | OEIS entries marked `TERMS_AGREE_UNPROVED`; the 82 nonempty uncertified Mordell curves ($\lvert k\rvert \le100$) whose scan matches the published count |
| **Evidence** | exact within a bound, silent beyond it | quartics such as Ljunggren's $2n^4-1=m^2$, genus $\ge2$ (sieve to $10^8$) |

The full picture, with dependency arrows, is in the status table of the [monograph](docs/MONOGRAPH.md#0-status-of-every-result-edition-07). What is assumed and what is ineffective is in [TRUST_BOUNDARY.md](docs/TRUST_BOUNDARY.md).

## Try it

```sh
export PYTHONPATH=python
python3 -m perfectpower classify --coeff 1,0,2 --d 2        # 2n^2+1: Pell type, kappa = 0.5673...
python3 -m perfectpower lean --coeff 1,1,1,1,1 --d 2        # Ljunggren's quartic -> Lean proof that n = 3 is the only hit
python3 -m perfectpower solve --expr '(5*n - 7)**3 - 2' --program   # the specialized program
python3 -m perfectpower prove --expr '8*n**3 + 12*n**2 + 6*n - 73'  # a standalone Lean theorem (descent)
python3 python/make_oeis_atlas.py      # re-verify the committed OEIS snapshot against the Lean links
make verify      # build Lean, audit axioms, lint, test, regenerate every receipt, require zero diff
make fresh       # an unseen disguised cubic, compiled, emitted and checked by Lean
make fuzz        # differential fuzzers with fixed seeds
make crosscheck  # optional, needs Sage
docker build -t perfectpower . && docker run --rm perfectpower
```

## The artifacts

| Artifact | Where | Interface |
|---|---|---|
| **Lean library** | `PerfectPower/` (Lean and Mathlib `v4.20.0`) | `import PerfectPower`; start at `Atlas.lean`, `PellExact.lean`, `Descent.lean`, `Observation.lean`, `SqrtTwoOrbit.lean` |
| **Python tool** (standard library only) | `python/perfectpower/` | CLI `classify / count / enumerate / lean / shifts / solve / prove / oeis`; `compiler`, `descent`, `oeis_source`, `oeis_orbit` |
| **Dataset** | `data/`, `receipts/`, `certs/` | families with type, $\kappa$, hits and certification label; `data/oeis/` holds unmodified OEIS entries with their export commit |

## Documents

- [MONOGRAPH.md](docs/MONOGRAPH.md): the status table, then the original 0–1 law.
- [RESEARCH_NOTES.md](docs/RESEARCH_NOTES.md) and the [paper (PDF)](paper/perfectpower.pdf): statements and proofs.
- [FORMAL_AUDIT.md](docs/FORMAL_AUDIT.md): the Lean library, file by file.
- [CONSTRAINT_COMPILER.md](docs/CONSTRAINT_COMPILER.md): reductions, plans, certified first hits, descent, the three kinds of answer.
- [MORDELL_BRANCH.md](docs/MORDELL_BRANCH.md): the branch compiler, the Gaussian pilot, the 26 closed curves, the tested prediction, the Thue branches.
- [DEFINITION_LANGUAGE.md](docs/DEFINITION_LANGUAGE.md): grammar, semantics and the exact claim of the generated OEIS proofs.
- [OEIS.md](docs/OEIS.md): observations of orbits, the orbit engine, the definition language and generated proofs, the withheld $\sqrt3$ test, snapshots, the promotion rule, the Mordell cross-check and obstruction classes.
- [ARITHMETIC_WORKFLOW.md](docs/ARITHMETIC_WORKFLOW.md): the Why3 Von Neumann isqrt route; [ARCHIVE_SALVAGE.md](docs/ARCHIVE_SALVAGE.md): exact examples and corrections recovered from old notes, and the projector certificate.
- [CERTIFICATE_FORMAT.md](docs/CERTIFICATE_FORMAT.md), [TRUST_BOUNDARY.md](docs/TRUST_BOUNDARY.md), [RELATED_WORK.md](docs/RELATED_WORK.md), [OPEN_PROBLEMS.md](docs/OPEN_PROBLEMS.md).

**What is still open.**
- Effective enumeration of the finite type outside Runge and the certified Mordell cases. The compiler states the missing premise exactly, and the OEIS cross-check ranks 82 nonempty curves with $|k|\le100$ as leads.
- **The negative-$k$ curves whose Thue branches carry points.** All 23 are complete under Matveev premises (`receipts/descent_coverage.json`). The remaining premise everywhere is Matveev's theorem itself, one named hypothesis per source equation.
- **Positive $k$** (96 curves $|k|\le100$): the factorization is real quadratic, which this lattice argument does not cover. The cubic-form route avoids it (`MordellCubicForm.lean`, `python/positive_k.py`): a point gives a form of discriminant $-108k$ representing 1, so each curve is a union of Thue equations in complex cubic fields (unit rank 1). Of 321 classes for $k\le100$, 163 are locally impossible and 54 are reducible (solved completely, `ReducibleThue.lean`).
  - **73 curves are complete in Lean with no premise** (no Matveev, no class-list hypothesis; `Generated/ClassLists/K*.lean`).
    - For 39 of them every class is locally impossible or reducible: 25 with no integral point, and $k=5,7,14,16,23,27,34,50,52,59,61,70,77,86$ with their points.
    - The other 33 have irreducible sources (below): $k=1,2,3,4,8,9,10,11,12,15,17,18,24,25,33,37,41,43,44,48,49,54,57,64,65,68,73,81,82,89,97,98,100$. They include $y^2=x^3+17$ with its 16 points up to $x=5234$, and $y^2=x^3+24$ with $(8158,\pm736844)$.
    - The remaining 28 positive-$k$ curves $\le100$ are census evidence only. The negative-$k$ theorems with Thue branches are conditional on Matveev's bound. These three statuses are kept separate everywhere.
  - The class-list premise is proved (`ClassListProof.classList_of`). The real reduction runs through a covariant positive definite form $q$ with $\det q=3/|D|$ and $q(v)^3\ge27F(v)^2/D^2$ (`CubicReduction.lean`). Then come Gauss reduction, an integer box with checked parameters, and kernel-checked transports for every form in the box.
  - **$k=2$: the first irreducible source, with no premise** (`Plus2.lean`, `Skolem3.lean`, `Generated/ClassLists/K2.lean`).
    - `Plus2.source` proves that $-u^3-3uv^2-2v^3=1$ only at $(-1,0)$.
    - The units of $\mathbb{Z}[z]$, $z^3+3z+2=0$, are $\pm\eta^n$, by a real-embedding box with no complex numbers.
    - The $z^2$ coordinate of $\eta^n$ vanishes only at $n=0$ for all integers $n$, by a 3-adic Skolem argument with integer valuations.
    - `K2.plus2`: the integral points of $y^2=x^3+2$ are exactly $(-1,\pm1)$.
  - **The method made generic: fifteen more curves** (`SkolemP.lean`, `RankOne.lean`, `Generated/RankOneSources/K*.lean`): $k=3,4,10,25,33,41,43,44,48,49,54,57,81,82,98$.
    - `SkolemP.corner_zero` is the zero set at any odd prime: if $A^M=1+pD$ with $p\nmid D_{20}$ and $p\nmid(A^r)_{20}$ for $0<r<M$, then $(A^N)_{20}=0$ only at $N=0$.
    - `RankOne.units_eq` proves unit generation for any $z^3=Pz+Q$ with a complex pair. It uses a slab check, because $|j|\le J$ and $|\mathrm{re}|\le1$ leave only a few $(a,b)$ per $c$.
    - Shifted sources $F(u,v)=-N((u+hv)-vz)$ are handled, and so are curves with two or three irreducible sources ($k=44,57$).
    - The Skolem primes range up to $p=67$ ($k=10$, period 22). They are checked on powers in $\mathbb Z[z]$ (`skolemB`).
    - The four $p=3$ candidates of the second OEIS handoff ($k=4,33,49,81$) are the inverses of the proved fundamental units.
    - The full table is in [MORDELL_BRANCH.md](docs/MORDELL_BRANCH.md) §7.4.
  - **Nonmonic sources with a known point** (`python/witness_monic.py`): $F(p,q)=1$ forces $\gcd(p,q)=1$, and Bézout completes $(-p,-q)$ to a determinant-one matrix $U$ with $F\circ U$ monic. These Mordell forms keep $3\mid B, C$ under $\mathrm{GL}_2(\mathbb Z)$, so $F\circ U=-u^3+Puv^2+Qv^3$ directly. 19 of the 36 nonmonic sources have a recorded point. 13 of them go through the unit engine (Lean source theorems pulled back through $U$); the other six have large slab checks (3), no unit found (1) or no Skolem prime (2).
  - **Sources with several solutions** (`SkolemZeros.lean`, `RankOneZeros.lean`, `python/rank_one_zeros.py`). `SkolemZeros.corner_zeros2` proves that every zero of $(A^N)_{20}$ lies below the period $M$, class by class:
    - $p\nmid(A^r)_{20}$;
    - or $(A^r)_{20}=0$ with a nonvanishing first-order term (the root $r$);
    - or recentring at a root of the inverse: $N=-(M-r)+M(m+1)$, which has no zero with $N\ge0$;
    - or an auxiliary prime $q$ with $q\nmid(A^s)_{20}$ on every class $s\equiv r\pmod{\gcd(M,M_q)}$.

    The kernel then filters the finitely many candidates (`RankOneZeros.source_list`). All 14 several-solution sources are certified: their lists are exactly the recorded representations. Up to three auxiliary primes are used, with periods up to 468.
  - OEIS regression (`receipts/positive_k_oeis.json`): all 100 positive-$k$ point lists agree with the seven original OEIS definitions `A081119`, `A134108`, `A054504` and `A134220`–`A134223` (0 mismatches). This is independent evidence, not a completeness proof.
  - **A nonmonic source with no point** (`RankOneNorm.lean`, `python/rank_one_norm.py`). The monic reduction $H(au,v)=a^2F(u,v)$ turns $F=1$ into an element of norm $a^2$ with $z^2$ coordinate $0$. `RankOneNorm.normN_eq` generalizes unit generation to norm $\pm N$: every such element is $\gamma\eta^n$ with $\gamma$ in a slab-checked list. `orbit_ne` excludes the coordinate on every orbit by one congruence. For $k=11$ the class $(-2,0,-3,-3)$ has the single representative $\pm(16+3z+2z^2)$ in $z^3=-6z+12$, and modulo 19 the coordinate never vanishes, so $y^2=x^3+11$ has no integral point. For the other 16 no-point sources the unit of the monic order is too large (index $a$ in the form's own ring).
  - Large points: the final point check uses supplied square roots (`PositiveKCurveRoot`), because the kernel's `Int.sqrt` exhausts memory beyond a few thousand.
  - Still open: 44 of the 104 irreducible equations (60 have Lean source theorems). Their blockers are recorded in `receipts/rank_one_blockers.json`: large slab checks, nonmonic leading coefficients without a known point, units not yet found, and missing Skolem primes.
- Quartic genus-one models: `EffectiveEnumeration.lean` has the degree-two map and exact lifts, not a quartic solver.
- The Bilu–Tichy classification: `MonomialCount.lean` has the finished counting pieces (monomials, filtered orbits, collisions, the $t^2$ outer polynomial), not the classification.

**CI.** GitHub Actions jobs for this repository are never assigned a runner, which is an account-level block. `make verify` (or the Dockerfile) is the reference check.

## Licence and citation

Code and Lean sources are licensed under [Apache-2.0](LICENSE); `docs/` and `paper/` under [CC-BY-4.0](LICENSE-docs). The OEIS entries in `data/oeis/` are unmodified copies under CC BY-SA 4.0 (the OEIS Foundation; see [data/oeis/SOURCE.md](data/oeis/SOURCE.md)). To cite, see [CITATION.cff](CITATION.cff).

Native square-plus-constant automation now supports **arbitrary degree and nonmonic integer polynomials** through ascending coefficient lists: `native_polynomial_square example_points for [0, 0, 0, 2], 1` emits a complete theorem for `y² = (2x³)² + 1`. This is a supported family, not a general solver for arbitrary polynomial power values. See [the mathematical account](docs/NATIVE_POLYNOMIAL_MONOGRAPH.md) and run `scripts/check_native_polynomial_power.sh` for both native audit suites.

The [recovered Lean bridges](docs/RECOVERED_LEAN_BRIDGES.md) now prove constructive integral matrix pullbacks, their connection to signed periodic unit sieves, two-isogeny covering identities, and the exact criterion for recovering a target from observations. Run `scripts/check_recovered_bridges.sh` for their targeted Lean audit.

The [sequence-recovery Lean foundations](docs/SEQUENCE_RECOVERY_LEAN.md) prove bounded rational reconstruction uniqueness, Wilson quotient-projector identities, all-index formal coefficient annihilation from a proved recurrence, and complete Padovan identification from recurrence certificates. Finite atlas matches retain their candidate status. Run `scripts/check_sequence_recovery_lean.sh` for the targeted audit.

[Operator recovery in Lean](docs/OPERATOR_RECOVERY_LEAN.md) now checks seven concrete all-future recurrence comparisons through finite invariant-subspace matrix certificates. Generic orbit transport and task-lift obstruction theorems are also proved. The paired recurrence definitions are certified; identification of OEIS definitions remains separate. Run `scripts/check_orbit_recovery.sh` to regenerate and check the certificates.

**Complete quartic solver:** the [effective quartic route](docs/QUARTIC_EFFECTIVE_SOLVER_MONOGRAPH.md) now solves quadratic squares plus nonzero linear perturbations, including fractional square completions for square-leading integer quartics. All 420 catalogue equations have kernel-checked complete point lists; 132 are empty. The geometric-series equation `y²=x⁴+x³+x²+x+1` has exactly six integer points and only the positive input `x=3`. The compiler recognizes these inputs and emits native Lean proofs without an external height premise.

### Divisor-sum results

The [divisor-sum atlas](receipts/divisor_sum/README.md) connects sigma to the complete quartic solvers, supplies 3,080 complete quartic lists, a perfect-power divisor-sum census through one million, and all square divisor sums in a specified two-prime-power grid. The [monograph](docs/DIVISOR_SUM_RESULTS_MONOGRAPH.md) explains the mathematics and exact scope. Use `PYTHONPATH=python python -m perfectpower sigma-quartic --shift 0` for the complete prime-fourth-power application, or `divisor-sum --factors '[[2,1],[11,1]]'` for exact factorization-based arithmetic.

### Branched geometry and faithful connection operators

The [branched-geometry module](docs/BRANCHED_GEOMETRY_MONOGRAPH.md) attaches 12,320 normalization profiles to the quartic atlas, with exact cyclotomic connection matrices, canonical surface cell models, dual face charges, and finite Hodge operators. Lean proves the explicit bouquet Laplacian kernel criterion for faithful root-of-unity transport, the energy and Hodge kernel identities, and integer-coordinate recovery from five concrete unimodular packets. Use `PYTHONPATH=python python -m perfectpower branched-geometry --coeff=0,-1,0,0,0,1 --d=2 --connection --cells`. The cell models describe topological type; intrinsic Voronoi geometry and analytic periods remain separate work.

### Positive geometry and branch degeneration extension

The new [mathematical monograph](docs/POSITIVE_GEOMETRY_MONOGRAPH.md) connects labelled root collisions, associahedral real branch chambers, canonical forms, exact cyclic connection determinant polytopes, period normalization contracts and polynomial Descartes curvature orbits. The deterministic corpus has 1,939 collision strata, 196 connection patterns and 5,438 associahedron faces, with a source-linked connection index over the preceding 12,320 quartic topology records. Run `PYTHONPATH=python python python/build_positive_geometry.py` to rebuild it. These new results are exact Python computations; [the Lean handoff](docs/POSITIVE_GEOMETRY_LEAN_HANDOFF.md) supports separate formalization.

### Explicit differentials and enclosed Legendre periods

The [holomorphic-basis extension](docs/HOLOMORPHIC_BASIS_MONOGRAPH.md) constructs actual differential numerators on normalized cyclic components, including repeated-root cancellations, deck eigenspaces and polynomial differential operators. It connects the quartic and collision atlases to explicit bases. `branched-geometry --differentials` returns formulas; `legendre-period-bounds --lambda 1/2 --terms 80` returns exact rational enclosures of normalized real and imaginary Legendre periods and their ratio. These classical analytic constructions are implemented in Python and are not yet formalized in Lean.

The [Lean backlog sweep](docs/LEAN_BACKLOG_MONOGRAPH.md) formalizes Descartes dynamics, rational collision charts, the theta determinant and Jacobian, two-column weighted Cauchy–Binet, finite period normalization, cyclic differential regularity arithmetic, the formal Legendre equation and convergent-series tail bound, and the recovered multiplicative system's exact exponent-image criterion. Its data audit checks all 1,939 saved collision profiles and twelve full basis representatives. The stronger quartic cutoff preserves exceptional zero-perturbation points and makes the remaining catalogue proof checks practical. Analytic normalization, Euler-period identification, general graph rank and general solver completeness remain separate targets. Run `scripts/check_lean_backlog.sh`.

**Quartic ledger complete:** all 3,080 divisor-sum catalogue equations now have kernel-checked complete lists and literal packet equalities. The 394-case compilation backlog is closed.

### Intrinsic geometry on the original complex curves

The [analytic geometry release](docs/ANALYTIC_GEOMETRY_MONOGRAPH.md) supplies period-derived Legendre conformal tori with intrinsic Voronoi polygons and curve-site inversion; continued-sheet circle and root-word period integrals for cyclic curves; smooth differential metrics in finite, branch and infinity charts; and curve-derived closed hyperelliptic meshes with intrinsic heat Voronoi approximations. Use `intrinsic-voronoi --lambda 1/2`, `analytic-periods --coeff=-1,0,0,1 --d=3 --word '[1,2,-1,-2]'`, or `conformal-voronoi --coeff=0,-1,0,0,0,1 --resolution 6 --sites 8`. The new general numerical backend is optional; exact lattice enclosures, floating predicates and mesh approximation scopes are recorded separately.

The geometry layer now includes exact rational polyhedral Voronoi boundary enclosures and integral symplectic bases on closed oriented meshes. See [the scope and proofs](docs/CERTIFIED_SURFACE_GEOMETRY.md). These certify the represented finite model; smooth metric comparisons and integration over the new basis remain unfinished.

The [symplectic analytic layer](docs/SYMPLECTIC_ANALYTIC_MONOGRAPH.md) now integrates the original curve's holomorphic forms along recorded integral homology cycles, producing actual numerical period matrices in genera one through four. It also supplies canonical Bergman metric evaluations, continued paths on cyclic components, and Abel–Jacobi lattice coordinates. Rigorous analytic error bounds and smooth Voronoi certification remain open.
