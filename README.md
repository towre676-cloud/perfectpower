# PerfectPower

**When is $F(n)$ a perfect power, and how often?**
PerfectPower classifies the possible long-term patterns for every integer polynomial. It gives exact counts for the power, radical and Pell families, and complete hit lists when a finite-case certificate or an independently established integral-point list is available. It has three layers:
- **A Lean 4 library.** It proves the counts, complete solution sets, and the counting law for Pell orbits, and ties the orbits to published integer sequences.
- **A Python compiler.** It turns integer constraints into certified plans.
- **A comparison layer.** It checks those results against the OEIS, keeping term matches separate from proofs.

The [trust table](#what-to-trust-at-a-glance) says what is machine-checked and what relies on outside mathematics or software.

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

**As a component of another solver** ([HOST_ADAPTER.md](docs/HOST_ADAPTER.md)).
`python3 -m perfectpower.smt_adapter TASK.smt2` replaces solved conjuncts of an SMT-LIB task by
their complete solution sets, each an exact equivalence over ℤ, and hands back the smaller task.
- On two verification-condition-shaped examples, z3 alone returns `unknown`, and after the
  reduction it proves both in milliseconds.
- On 48 constructed instances, the 24 impossibility tasks (no point satisfies the system) are proved by the adapter in all 24 cases, against 1 for z3 alone. On genuinely satisfiable instances z3 alone already finds 10 of 12 witnesses.
- Recognition costs about 2 ms on unrecognized tasks (classifier overhead only).

**Bounded Pell queries are kernel-checked by default:** for `2 ≤ N ≤ 10⁹`, all 24 solutions of $N(N-1)=2S^2$ are a Lean theorem (`BoundedPell.quad_bounded`; each unit step at least doubles the orbit, so 32 steps cover the range). **Why3 accepts the replacement:** on three constructed verification conditions, Why3 (with z3) proves both the replacement lemma and the VC from the imported Lean theorem, and fails without it ([details](docs/HOST_ADAPTER.md)). These instances are constructed. On an independent corpus of 69 upstream QF_NIA files (12,860 queries, including 12,801 industrial ELSTER queries), the fail-closed script-level adapter finds **zero** replaceable conjuncts ([coverage report](independent_nia/reports/PERFECTPOWER_COVERAGE.md)).

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
    - **Coverage** (`receipts/descent_coverage.json`, derived from the registered Lean theorems): 8 of the 109 unit equations are registered, and $D=7,18,23,28,45,63,89$ are conditionally complete. The workload that still blocks a class is $U_{\mathrm{needed}}$: 88 unit equations, the unregistered leaves of the 45 unresolved classes.
    - **Cost before proof** (`receipts/order_cost.json`): an estimate of the kernel work $C(D)$ for each unresolved curve, with shared orders charged once. The cheapest priced curves are $D=39$, $60$, $47$ and $95$.

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
- Lean declarations audited: **1032**; using only `propext`, `Classical.choice`, `Quot.sound` (or a subset): **1032**.
- Machine-generated Lean hit-set certificates: **56**.
- Theorems conditional on named premises (Matveev's lower bound, three explicit instances per class; not counted as closed): **8** (`Field756.minus7`, `minus28`, `minus63`; `Minus18.minus18`, `Minus23.minus23`, `Minus45.minus45`, `Minus89.minus89`; `D72Residual.residual_empty`).
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
- [CERTIFICATE_FORMAT.md](docs/CERTIFICATE_FORMAT.md), [TRUST_BOUNDARY.md](docs/TRUST_BOUNDARY.md), [RELATED_WORK.md](docs/RELATED_WORK.md), [OPEN_PROBLEMS.md](docs/OPEN_PROBLEMS.md).

**What is still open.**
- Effective enumeration of the finite type outside Runge and the certified Mordell cases. The compiler states the missing premise exactly, and the OEIS cross-check ranks 82 nonempty curves with $|k|\le100$ as leads.
- **The 23 negative-$k$ curves whose Thue branches carry points** (62 obligations). Local certificates cannot close them; this needs bounds for irreducible Thue equations (Baker with reduction, or Skolem's method), certified in Lean.
- **Positive $k$** (96 curves $|k|\le100$): the factorization is real quadratic, which this lattice argument does not cover. `Interfaces.orbit_mod_three` proves only the unit-exponent normalization (units mod cubes). Seed and ideal-class coverage, the exceptional primes and the integral readout are separate obligations.
- Quartic genus-one models: `EffectiveEnumeration.lean` has the degree-two map and exact lifts, not a quartic solver.
- The Bilu–Tichy classification: `MonomialCount.lean` has the finished counting pieces (monomials, filtered orbits, collisions, the $t^2$ outer polynomial), not the classification.

**CI.** GitHub Actions jobs for this repository are never assigned a runner, which is an account-level block. `make verify` (or the Dockerfile) is the reference check.

## Licence and citation

Code and Lean sources are licensed under [Apache-2.0](LICENSE); `docs/` and `paper/` under [CC-BY-4.0](LICENSE-docs). The OEIS entries in `data/oeis/` are unmodified copies under CC BY-SA 4.0 (the OEIS Foundation; see [data/oeis/SOURCE.md](data/oeis/SOURCE.md)). To cite, see [CITATION.cff](CITATION.cff).
