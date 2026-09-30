# PerfectPower

**When is $F(n)$ a perfect power, and how often?**
This repository classifies the possible long-term patterns for every integer polynomial. It gives exact counts for the power, radical and Pell families, and complete hit lists when a finite-case certificate or an independently established integral-point list is available. The [trust table](#what-to-trust-at-a-glance) says which conclusions are machine-checked and which rely on outside mathematics or software.

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

The classification is a **synthesis**, and we claim no priority for it. It combines Siegel's theorem, through the Euler characteristic $\chi=d'(1-S)$ of the curve $y^d=F(x)$ (Theorem G), with classical Pell and valuation counting. The implementation has machine-checked components and a certificate system for complete finite answers. For a general finite-type polynomial, knowing that the hits eventually stop does not yet give an algorithm that lists all of them.

**Try one in five minutes.** Follow the [tutorial](docs/TUTORIAL.md) to give the program $1+n+n^2+n^3+n^4$, find its square hit at $n=3$, and compile a Lean proof that there are no others. You can also run `PYTHONPATH=python python3 -m perfectpower classify --coeff 1,0,2 --d 2` to see why $2n^2+1$ has infinitely many but increasingly rare square hits. Coefficients are entered from constant term to highest power.

---

## Highlights

**Exact counts, proved in Lean 4.** `PerfectPower/Atlas.lean` gives one interface for all four types:

- `pell_exact_count`: $|A(N)-\kappa\log N|\le K$ with $\kappa=\frac{1}{\log\varepsilon}\sum_\rho g_\rho/P_\rho$. The sum runs over canonical Pell orbit roots, so duplicate orbits are removed and each orbit is counted at the true rate $\varepsilon^j$.
- `radical_asymptotic_int`: $|A(N)-\kappa N^{1/t}|\le K$ with $\kappa=(R/v)(v/z_0)^{1/t}$. This includes the case $\kappa=0$, where local solvability does **not** give infinitely many hits.
- `atlas_finite`: finitely many hits, **from an explicitly named premise** (`SuperellipticSiegel`: Siegel's theorem plus the geometric half of Theorem G). The combinatorial half, "$\chi<0$ iff the profile is not of power, radical or Pell type", is proved for **all** $d$ (`chi_neg_iff`).

**Generic input, pointwise reductions in Lean.** Every nonzero $F\in\mathbb Z[X]$ has a rational squarefree-layer (Yun) decomposition (`exists_integer_decomposition`). From it, `integer_radical_reduction` and `integer_pell_reduction` reduce "is $F(n)$ a $d$-th power" to the radical form $\mathrm{lc}(F)\,v^{d-r}(vn-u)^r$, or to square branches of a monic quadratic. All zeros of $F$ are kept. Both counts are proved from these reductions, so a general $F$ of radical or Pell type is counted in Lean end to end (`PerfectPower/Continuation/`):
- `Decomposition.radical_count`: $|A(N)-\kappa N^{1/t}|\le K$ for every $F$ with one bad layer.
- `Decomposition.pell_count`: $|A(N)-\kappa\log N|\le K$ for every $F$ of Pell type.

They include all zeros, both signs, shifts, the $\pm\gamma$ branches and the unsolvable cases. Whether $\kappa>0$ is decided too, by a finite search for the radical type (`radical_kappa_decide`) and by a one-point criterion for the Pell type (`pell_kappa_decide`); each Pell branch also has an explicit bounded search.

**Certificates you can re-check.** `pp-cert/1` is a small, versioned JSON format whose statement is bound by a hash ([spec](docs/CERTIFICATE_FORMAT.md)).
- A Lean checker, proved sound once (`check_sound`, `rungeCheck_sound`), turns each certificate into a kernel theorem. 19 complete hit sets, including instances of Erdős–Selfridge, total 25 KB and check in about a minute.
- Mutated certificates are rejected by the kernel. One surprise: the same arithmetic bounds that prove $n(n+1)\cdots(n+11)$ is never a fourth power also work after adding $1$ (with a new statement hash).
- `make cert-audit` independently rechecks the JSON arithmetic with plain Python and returns a failing exit code on a bad certificate; `make verify` runs it alongside the Lean checker.

**Genus one, with no hypothesis at all.** New Lean files remove Sage from the trust base for whole families, including curves of positive rank:
- `MordellDescent.lean`: $y^2=x^3+k$ has **no** integral points for **1163** values $0<|k|\le10^4$, e.g. $n^3+7$ is never a square. This is Mordell's classical descent, with its congruences checked by the kernel. For 28 of these curves the Sage census relied on an unproved rank.
- `MordellFLT3.lean`: for every $u\ne0$, $n^3-432u^6$ is a perfect square **iff** $n=12u^2$. This is a complete, nonempty list for an infinite family, derived from Mathlib's proof of Fermat's Last Theorem for exponent 3.
- **Positive rank:** $y^2=x^3-2$ and $y^2=x^3-4$ have infinitely many rational points, yet Lean proves their integral points are exactly $(3,\pm5)$ and $(2,\pm2),(5,\pm11)$. This is done by descent in ℤ[√−2] and ℤ[i] (`MordellMinus2.lean`, `MordellMinus4.lean`).
- **Class number two, as a template:** `ClassTwo.lean` proves the class-group argument for $y^2=x^3-D$ for every $D$, without ideals: a Thue pigeonhole lattice bound plus a finite norm table that the kernel checks per $D$. Instances: $y^2=x^3-13$ has integral points exactly $(17,\pm70)$; $y^2=x^3-5$ and $y^2=x^3-6$ have none.
- **Transport with exact counts:** `Transport.lean` turns any such list into hit sets and exact counts $A(N)$ for $G(rn+s)$, keeping every divisibility condition. For example, $(rn+s)^3-2$ is a square iff $rn+s=3$.

**Hidden hits, caught.** Short scans miss real solutions. Sage-certified genus-one lists contain
$$6n^2-7n-6=95339^3\ \text{ at } n=12{,}017{,}947,\qquad 6n^2+n+1=61301^3\ \text{ at } n=6{,}196{,}204.$$
399 such families are generated as Lean theorems whose complete hit lists follow from a *named* hypothesis: Sage's point list on the Weierstrass model. That hypothesis is not proved in Lean.

**A census of the frontier.** All integral points of $y^2=x^3+k$ for $0<|k|\le10^4$ (the Hall ratio, the rank, and a proof status per curve), and every pair of perfect powers up to $10^{18}$ at distance at most $1000$ (Pillai). These are *evidence* only: Hall and Pillai are open, and nothing here proves them. The function-field analogues are proved unconditionally (`davenport`, `pillai_polynomial`). Over $\mathbb Z$ they are proved only from abc, taken as an explicit hypothesis (`hall_of_abc`, `pillai_finite_of_abc`).

**The oscillation in the Pell type.** For Pell-type families the heat transform $\sum e^{-\tau n}$ over the hits has a log-periodic second term. The proof keeps the shift $-B/2A$ and the pole at $s=-1$, and it is checked numerically to order $\tau^2\log(1/\tau)$ (Theorem T2).

---

## Status in numbers

<!-- counts:begin (generated by python/make_counts.py; do not edit) -->
- Lean declarations audited: **269**; using only `propext`, `Classical.choice`, `Quot.sound` (or a subset): **269**.
- Machine-generated Lean hit-set certificates: **19**.
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
| **Lean** | compiled; only `propext`, `Classical.choice`, `Quot.sound` | exact Pell and radical counts, the 0–1 law on the rigid branch, 19 certificates, 1163 pointless Mordell curves, $n^3-432u^6$, $x^3-2$, $x^3-4$, $x^3-13$ (rank one) |
| **Lean ⇐ named hypothesis** | compiled, with an unproved premise stated as a `def` | finite type (`SuperellipticSiegel`), 399 genus-one lists, the binomials $\binom n2=m^3$ and $\binom n3=m^2$ |
| **Paper** | written proof, cross-checked by exact computation | geometric half of Theorem G |
| **External** | Sage or Singular, re-verified in plain Python by `make verify` | Mordell census, 1022 genus-one families, Theorem G check for $d,\deg F\le8$ (462 cases, 0 disagreements) |
| **Evidence** | exact within a bound, silent beyond it | quartics such as Ljunggren's $2n^4-1=m^2$, genus $\ge2$ (sieve to $10^8$) |

The full picture, with dependency arrows, is in the status table of the [monograph](docs/MONOGRAPH.md#0-status-of-every-result-edition-07). What is assumed and what is ineffective is in [TRUST_BOUNDARY.md](docs/TRUST_BOUNDARY.md).

## Try it

```sh
PYTHONPATH=python python3 -m perfectpower classify --coeff 1,0,2 --d 2   # 2n^2+1: Pell type, kappa = 0.5673...
PYTHONPATH=python python3 -m perfectpower lean --coeff 1,1,1,1,1 --d 2   # Ljunggren's quartic -> Lean proof that n = 3 is the only hit
make verify      # build Lean, audit axioms, lint, test, regenerate every receipt, require zero diff
make fuzz        # differential fuzzers with fixed seeds (scans to 1e8 by a modular sieve)
make crosscheck  # optional, needs Sage: census, genus-one families, binomials, Theorem G
make bench       # certificate size and checking-time benchmarks
docker build -t perfectpower . && docker run --rm perfectpower
```

New here? Start with the five-minute [TUTORIAL.md](docs/TUTORIAL.md): a polynomial in, a compiled Lean certificate out.

## The three artifacts

| Artifact | Where | Interface |
|---|---|---|
| **Lean library** | `PerfectPower/` (Lean and Mathlib `v4.20.0`) | `import PerfectPower`; start at `Atlas.lean`, `PellExact.lean`, `RadicalAsymp.lean`, `Reflect.lean` |
| **Python tool** (standard library only) | `python/perfectpower/` | CLI `classify / count / enumerate / lean / shifts`; `certfmt` (certificates), `sieve` (exact scans) |
| **Dataset** | `data/`, `receipts/`, `certs/` | one row per family with type, $\kappa$, hits, certification label and the command that reproduces it |

## Documents

- [MONOGRAPH.md](docs/MONOGRAPH.md): the status table, then the original 0–1 law.
- [RESEARCH_NOTES.md](docs/RESEARCH_NOTES.md) and the [paper (PDF)](paper/perfectpower.pdf): statements and proofs.
- [CERTIFICATE_FORMAT.md](docs/CERTIFICATE_FORMAT.md): `pp-cert/1`, its soundness, rejection tests and benchmarks.
- [FORMAL_AUDIT.md](docs/FORMAL_AUDIT.md): the Lean library, file by file.
- [TRUST_BOUNDARY.md](docs/TRUST_BOUNDARY.md), [RELATED_WORK.md](docs/RELATED_WORK.md), [OPEN_PROBLEMS.md](docs/OPEN_PROBLEMS.md), [NEXT_PUSH.md](docs/NEXT_PUSH.md).

**What is still open.** The main open items are:
- generating `ClassTwo` instances for more $D$, and curves of rank $\ge2$;
- quartic genus-one models;
- a Bilu–Tichy counting sequel;
- complete the primary-source literature comparison. [RELATED_WORK.md](docs/RELATED_WORK.md) now checks the full texts of Beukers–Tengely (Runge), Bérczes et al. (explicit superelliptic bounds), and Baanen et al. (formal Mordell completeness); the remaining comparisons are explicitly pending.

**CI.** GitHub Actions jobs for this repository are never assigned a runner, which is an account-level block. `make verify` (or the Dockerfile) is the reference check.

## Licence and citation

Code and Lean sources are licensed under [Apache-2.0](LICENSE); `docs/` and `paper/` under [CC-BY-4.0](LICENSE-docs). To cite, see [CITATION.cff](CITATION.cff).
