# PerfectPower

**When is $F(n)$ a perfect power, and how often?**
PerfectPower classifies the possible long-term patterns for every integer polynomial. It gives exact counts for the power, radical and Pell families, and complete hit lists when a finite-case certificate or an independently established integral-point list is available. It has three layers:
- **A Lean 4 library.** It proves the counts, complete solution sets, and the counting law for Pell orbits, and ties the orbits to published integer sequences.
- **A Python compiler.** It turns integer constraints into certified plans.
- **A comparison layer.** It checks those results against the OEIS, keeping term matches separate from proofs.

The [trust table](#what-to-trust-at-a-glance) says what is machine-checked and what relies on outside mathematics or software.

> Take $F\in\mathbb Z[x]$ and $d\ge2$, and count the *hits* $A(N)=\#\{1\le n\le N : F(n)=m^d\}$.
> Only four behaviours are possible:
>
> | type | $A(N)$ | example |
> |---|---|---|
> | **power** | $N$ | $(n^2+1)^2$ |
> | **radical** | $\kappa\,N^{1/t}+O(1)$, $t\mid d$ | $4n+1=m^2$: $\kappa=1$ |
> | **Pell** | $\kappa\log N+O(1)$ | $2n^2+1=m^2$: $\kappa=1/\log(3+2\sqrt2)=0.5673\ldots$ |
> | **finite** | $O(1)$ | $n^4+1=m^2$: no positive hits |
>
> Root multiplicities identify the candidate families; exact residue and Pell-orbit tests determine whether a candidate has infinitely many hits. The constants $\kappa$ have exact formulas. The growth exponent always lies in $\{0,1\}\cup\{1/t: t\mid d\}$.

The classification is a **synthesis**, and we claim no priority for it. It combines Siegel's theorem, through the Euler characteristic $\chi=d'(1-S)$ of the curve $y^d=F(x)$ (Theorem G), with classical Pell and valuation counting. For a general finite-type polynomial, knowing that the hits eventually stop does not yet give an algorithm that lists all of them.

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
- **The counting law for observations** (`Observation.lean`): finitely many filtered orbits, with coordinates growing like $E^j$ and disjoint beyond a threshold, satisfy
$$\#\{v\le N\}=\Big(\sum_\rho\frac{g_\rho}{P_\rho\log E_\rho}\Big)\log N+O(1).$$
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
    - 28 are proved equivalent;
    - 3 are proved equal to a coordinate outside a finite exceptional set;
    - 1 is transported from the proved entry it duplicates;
    - 7 agree without proof.
  - **Mordell cross-check:** all 41 Lean-certified Mordell lists with $|k|\le100$ match the published solution counts (A081119/A081120).

### 5. Evidence and frontiers
- **Hidden hits, caught.** Short scans miss real solutions: $6n^2-7n-6=95339^3$ at $n=12{,}017{,}947$. There are 399 such families with complete lists from a *named* hypothesis (Sage's point list), which is not proved in Lean.
- **Censuses.** These are evidence only: all integral points of $y^2=x^3+k$ for $0<|k|\le10^4$, and perfect-power gaps up to $10^{18}$ (Pillai). Hall and Pillai are open. The function-field analogues are proved (`davenport`, `pillai_polynomial`), and over $\mathbb Z$ they follow from abc as an explicit hypothesis.
- **The Pell oscillation.** The heat transform over Pell hits has a log-periodic second term (Theorem T2), checked numerically to order $\tau^2\log(1/\tau)$.

---

## Status in numbers

<!-- counts:begin (generated by python/make_counts.py; do not edit) -->
- Lean declarations audited: **583**; using only `propext`, `Classical.choice`, `Quot.sound` (or a subset): **583**.
- Machine-generated Lean hit-set certificates: **54**.
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
| **Lean** | compiled; only `propext`, `Classical.choice`, `Quot.sound` | exact Pell and radical counts; 19 certificates; 1163 pointless Mordell curves; $x^3-2$, $x^3-4$, $x^3-13$; descent answers such as $8n^3+12n^2+6n-73$; the observation counting law; the quadratic-unit orbit engine; 82 distinct OEIS definitions as orbit coordinates or seed-orbit enumerations (23 hand-written, 69 generated, 10 proved both ways) |
| **Lean ⇐ named hypothesis** | compiled, with an unproved premise stated as a `def` | finite type (`SuperellipticSiegel`), 399 genus-one lists, the binomials $\binom n2=m^3$ and $\binom n3=m^2$ |
| **Paper** | written proof, cross-checked by exact computation | geometric half of Theorem G |
| **External** | Sage or Singular, re-verified in plain Python by `make verify` | Mordell census, genus-one families, Theorem G check (462 cases, 0 disagreements) |
| **Lead** | a term match or a published count, never a proof | OEIS entries marked `TERMS_AGREE_UNPROVED`; the 98 uncertified Mordell curves ($|k|\le100$) whose scan matches the published count |
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
- [OEIS.md](docs/OEIS.md): observations of orbits, the orbit engine, the definition language and generated proofs, the withheld $\sqrt3$ test, snapshots, the promotion rule, the Mordell cross-check and obstruction classes.
- [CERTIFICATE_FORMAT.md](docs/CERTIFICATE_FORMAT.md), [TRUST_BOUNDARY.md](docs/TRUST_BOUNDARY.md), [RELATED_WORK.md](docs/RELATED_WORK.md), [OPEN_PROBLEMS.md](docs/OPEN_PROBLEMS.md).

**What is still open.**
- Effective enumeration of the finite type outside Runge and the certified Mordell cases. The compiler states the missing premise exactly, and the OEIS cross-check ranks 98 nonempty curves with $|k|\le100$ as leads.
- Descent when $3\mid h(-4D)$, at the ramified primes and for non-maximal orders, and positive $k$. For $y^2=x^3-1$ the certificate only assumes the units are $\pm1$; every Gaussian unit is a cube ($i=(-i)^3$). `receipts/mordell_obstructions.json` classifies the failures:
  - a maximal-order descent with a gcd case split would address every recorded failure of 46 of the 59 unresolved curves with $k<0$;
  - a certificate change for $\mathbb Z[i]$ (absorbing cube units, coprimality at $1+i$) reaches only $y^2=x^3-1$.
- Curves of rank $\ge2$ and quartic genus-one models.
- Formalizing the remaining 23 $\sqrt2$ entries, which need convergents, generating functions or Pythagorean triples.
- A Bilu–Tichy counting sequel.

**CI.** GitHub Actions jobs for this repository are never assigned a runner, which is an account-level block. `make verify` (or the Dockerfile) is the reference check.

## Licence and citation

Code and Lean sources are licensed under [Apache-2.0](LICENSE); `docs/` and `paper/` under [CC-BY-4.0](LICENSE-docs). The OEIS entries in `data/oeis/` are unmodified copies under CC BY-SA 4.0 (the OEIS Foundation; see [data/oeis/SOURCE.md](data/oeis/SOURCE.md)). To cite, see [CITATION.cff](CITATION.cff).
