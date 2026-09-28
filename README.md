# PerfectPower — density, exponents, and exact hit sets of polynomial perfect powers

**Release 0.6, 28 September 2026.** For $F\in\mathbb Z[x]$ and $d\ge2$, a *hit* is an index $n\ge1$ with $F(n)=m^d$, and $A(N)$ counts hits up to $N$. This repository contains:

- a publication-oriented manuscript,
- a compiled Lean 4 kernel,
- exact stdlib-only Python tooling,
- reproducible receipts.

## What is proved

| Result | Status |
|---|---|
| **0–1 law.** The hit density is $1$ if $F=G^d$ with $G\in\mathbb Z[x]$, else $0$ ([monograph](docs/MONOGRAPH.md) §3). | Paper proof using Boshernitzan; an independent route via LeVeque is in [the research notes](docs/RESEARCH_NOTES.md). |
| **Rigid branch** ($d\mid\deg F$, leading coefficient a $d$-th power): exact power or finitely many hits; density exists and is $0$ or $1$. | **Lean-verified**: `rigid_dichotomy`, `rigid_zero_one`. |
| **Twisted powers** $D^dF=cH^d$ with $c$ not a $d$-th power: every hit is a root of $H$. | **Lean-verified**: `twisted_finite`, and `power_type_finite` over $\mathbb Q[x]$. |
| Finite surgery, periodic density $P/T$, convergence bridge, finite-support squeeze. | **Lean-verified.** |
| **Monomials** $n^r$: hits are exactly the $t$-th powers, $A(N)=\lfloor N^{1/t}\rfloor$, $t=d/\gcd(r,d)$; this realises every exponent of the spectrum. | **Lean-verified**: `monomial_count`. |
| Complete hit lists: $1+n+\dots+n^4=m^2 \iff n=3$ (Ljunggren); $n(n+1)(n+2)(n+3)$ is never a square. | **Lean-verified**: `ljunggren_hitSet`, `consecutive_four_hitSet`. |
| **Machine-generated certificates** (new): Python finds a Runge plan and emits a Lean theorem "the hit set is exactly $H$", which Lean checks independently. There are 17 instances, including products of up to 12 consecutive integers. | **Lean-verified**: `PerfectPower/Generated/Runge.lean`. |
| **Pell example** $2n^2+1$: infinitely many square values but density zero, with $A(N)\le\sqrt N$. | **Lean-verified**: `pell_hitSet_infinite`, `pell_hasDensity_zero`. |
| **Atlas** (new): $A(N)$ is $N$, $\kappa N^{1/t}+O(1)$ with $t\mid d$, $\kappa\log N+O(1)$, or bounded, with explicit $\kappa$; the type is decidable from root multiplicities. | Paper proof plus LeVeque's theorem for the bounded case ([notes](docs/RESEARCH_NOTES.md) §§2–5). |
| **Exponent spectrum** (new): $\alpha(F,d)\in\{0,1\}\cup\{1/t: t\mid d,\ t>1\}$, and $A(N)=O(N^{1/p})$ ($p$ the least prime factor of $d$) for every non-power $F$. | Corollary of the atlas. |
| **Complete Runge enumeration** (new): in the rigid branch the entire hit set is computed, not just a cutoff. | Paper proof; the reduction to finitely many $G_t$ is Lean-verified (`runge_finite`); exact implementation. |
| **Sums of powers** (new): the atlas recovers Schäffer's list $(k,d)\in\{(1,2),(3,2),(3,4),(5,2)\}$ of infinite families $1^k+\dots+n^k=m^d$, with constants (e.g. $\kappa=1/\log(5+2\sqrt6)$ for $k=5$). | Corollary of the atlas; receipt-checked. |
| **Shift spectrum** (new): for $\deg S\ge3$, $S(n)+k$ has finitely many hits except at the $\le\deg S-1$ critical values $k$. | Corollary of the atlas. |
| **Transform asymptotics** (new): Dirichlet poles and heat asymptotics for every type. | Paper proof ([notes](docs/RESEARCH_NOTES.md) §8). |

Reading order:

1. [MONOGRAPH.md](docs/MONOGRAPH.md): definitions and the 0–1 law.
2. [RESEARCH_NOTES.md](docs/RESEARCH_NOTES.md): the v0.6 theorems with proofs.
3. [paper/perfectpower.pdf](paper/perfectpower.pdf): the same results as a typeset paper (source `paper/perfectpower.tex`; build with `pdflatex` twice).
4. [FORMAL_AUDIT.md](docs/FORMAL_AUDIT.md): exactly what the Lean build certifies.

## Lean

The toolchain is Lean `v4.20.0`, with Mathlib pinned to tag `v4.20.0` in `lake-manifest.json`.

```sh
lake exe cache get      # or build Mathlib from source (about 1900 modules)
lake build
./audit/check_axioms.sh # fails on sorry or any axiom beyond propext, Classical.choice, Quot.sound
```

All modules compile. Fifty-six audited theorems (including 17 machine-generated complete hit sets) use only the standard axioms. CI (`.github/workflows/lean.yml`) repeats both steps.

## Python (standard library only)

Coefficients are given low-to-high, so `1,4` means $4x+1$.

```sh
PYTHONPATH=python python3 -m unittest discover -s python/tests -v
PYTHONPATH=python python3 -m perfectpower scan      --coeff 1,4 --d 2 --N 10000
PYTHONPATH=python python3 -m perfectpower classify  --coeff 1,0,2 --d 2          # Pell type, kappa = 1/log(3+2*sqrt2)
PYTHONPATH=python python3 -m perfectpower count     --coeff 1,0,2 --d 2 --N 1000000000000000000000000
PYTHONPATH=python python3 -m perfectpower enumerate --coeff 1,1,1,1,1 --d 2      # complete: only n = 3
PYTHONPATH=python python3 -m perfectpower shifts    --coeff 0,-3,0,1 --d 2       # critical shifts k = +-2
PYTHONPATH=python python3 -m perfectpower lean      --coeff 7,0,0,0,1 --d 2      # emit a Lean proof of the hit set
PYTHONPATH=python python3 -m perfectpower certificate --coeff 1,0,0,0,1 --d 2    # v0.5 cutoff certificate
python3 python/make_receipts.py && python3 python/make_atlas_receipts.py
```

The modules are:

| Module | Contents |
|---|---|
| `core.py` | exact hit definition, v0.5 certificate |
| `polyalg.py` | exact $\mathbb Q[x]$ algebra: squarefree decomposition, Sturm integer roots, resultants |
| `arith.py` | factoring, square roots mod $m$, Pell and LMM |
| `runge.py` | complete rigid enumeration |
| `atlas.py` | classification, structural hits and counts, shift spectrum |

## Receipts

`receipts/exact_benchmarks.json` is the v0.5 receipt, unchanged apart from regeneration. `receipts/atlas_benchmarks.json` covers 43 families: their classification, exponent, $\kappa$, and structural counts up to $10^{24}$. Each structural count is cross-checked against the defining scan up to $10^5$. The receipt also contains complete hit lists and a Grunwald–Wang check. [Receipt policy](docs/RECEIPTS.md) defines the status labels, and [the roadmap](docs/NEXT_PUSH.md) lists what is open.
