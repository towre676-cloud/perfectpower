# OEIS as a discovery layer: quadratic-unit orbits, many sequences

The OEIS is used here to **find candidate correspondences**, never as evidence. A match of terms
is a lead; a Lean theorem about the entry's own definition, with its offset, is a result. This
file describes both halves and the rule that connects them.

## 1. The mathematics: observations of orbits (`Observation.lean`)

A Pell orbit is one arithmetic object. A sequence in a table is usually one **coordinate** of it,
and the count of that coordinate's values depends on how fast the coordinate grows.

**`observed_count`.** Take finitely many observations $v_{\rho,j}$ ($\rho\in R$) with:
- each $v_{\rho,j}$ strictly increasing in $j$;
- growth bounds $c_1E_\rho^j\le v_{\rho,j}\le c_2E_\rho^j$;
- acceptance on a set of indices of period $P_\rho$, with $g_\rho$ residues accepted;
- no value shared between two orbits above a threshold $V_0$.

Then the accepted values $S$ satisfy
$$\#\{v\in S: v\le N\}=\Big(\sum_\rho\frac{g_\rho}{P_\rho\log E_\rho}\Big)\log N+O(1).$$
Writing $E_\rho=\varepsilon^{r_\rho}$ gives the constant $\sum_\rho g_\rho/(P_\rho r_\rho\log\varepsilon)$: the
degree $r$ of the observation enters, and duplicate images are excluded by hypothesis.

The proof has three layers:
- `count_between`: indices between two geometric bounds;
- `filtered_obs_count`: periodic acceptance, split by residue class;
- `value_count`: indices to values, with an error of at most $(\#R+1)(V_0+1)$.

**`observed_count_eventually`** needs monotonicity and the growth bounds only from an index
$j_0(\rho)$ on. The first $j_0$ values change the count by a bounded amount, and
`card_filter_shift` shows that the accepted fraction of a period does not depend on where the
period starts.

## 2. One orbit behind thirteen entries (`SqrtTwoOrbit.lean`, `SquareTriangular.lean`)

Write $(1+\sqrt2)^k=A_k+B_k\sqrt2$.
- **The even powers** are the orbit of $(1,0)$ on $x^2-2y^2=1$.
- **The odd powers** are the orbit of $(1,1)$ on $x^2-2y^2=-1$.
- Both orbits run under the unit $3+2\sqrt2$, and `even_sol_iff`/`odd_sol_iff` prove they are
  exhaustive: the only orbit roots are $(1,0)$ and $(1,1)$.
- **The field symmetry explains the equation:** conjugation fixes the norm.
- **The unit generates each orbit.**
- **The coordinate sets the counting constant.**

Each entry below is defined in Lean **from the text of its OEIS entry**, with its offset, and
proved equal to an exact coordinate:

| entry | OEIS definition (from the `.seq` file) | offset | coordinate | Lean |
|---|---|---|---|---|
| A000129 | Pell numbers, $a(n)=2a(n-1)+a(n-2)$, $0,1$ | 0 | $B_n$ | `A000129_eq` |
| A001541 | $a(n)=6a(n-1)-a(n-2)$, $1,3$ | 0 | $A_{2n}$ | `A001541_eq` |
| A001542 | $a(n)=6a(n-1)-a(n-2)$, $0,2$ | 0 | $B_{2n}$ | `A001542_eq` |
| A001109 | $a(n)^2$ triangular; $6,-1$ from $0,1$ | 0 | $B_{2n}/2$ | `A001109_eq` |
| A001108 | $a(n)$-th triangular number a square; $a(n+1)=6a(n)-a(n-1)+2$ | 0 | $(A_{2n}-1)/2$ | `A001108_eq` |
| A001652 | $a(n)=6a(n-1)-a(n-2)+2$, $0,3$ | 0 | $(A_{2n+1}-1)/2$ | `A001652_eq` |
| A002315 | NSW numbers, $6,-1$ (initial $1,7$ from the terms) | 0 | $A_{2n+1}$ | `A002315_eq` |
| A005319 | $a(n)=6a(n-1)-a(n-2)$ (initial $0,4$ from the terms) | 0 | $2B_{2n}$ | `A005319_eq` |
| A001110 | square triangular numbers | 0 | $(B_{2n}/2)^2$ | `A001110_enumerates` |
| A001653 | $k$ with $2k^2-1$ a square | 1 | $B_{2n-1}$ | `A001653_enumerates` |
| A055997 | $k$ with $k(k-1)/2$ a square | 1 | $(A_{2n-2}+1)/2$ | `A055997_enumerates` |
| A084703 | squares $k$ with $2k+1$ a square | 0 | $B_{2n}^2$ | `A084703_enumerates` |
| A075870 | $k$ with $2k^2-4$ a square | 1 | $2B_{2n-1}$ | `A075870_enumerates` |

**Recurrence definitions** are proved by `rec_unique`: the same recurrence and the same two
initial values. A002315 and A005319 state only the recurrence in their names, so their initial
values are taken from their listed terms, and this is recorded.

**Set definitions** are proved as **increasing enumerations** (`Enumerates a off S`): from the
offset, the coordinate is strictly increasing and its values are exactly $S$. The domain is the
entry's own, read from its offset and first terms. A001110 and A084703 include $0$; A055997 starts
at $k=1$.

The relations the entries state about each other are theorems:
- A002315's own claim $a(n)^2-2\,\mathrm{A001653}(n+1)^2=-1$ is `A002315_A001653`;
- `cluster` proves $\mathrm{A001541}^2-2\,\mathrm{A001542}^2=1$, $\mathrm{A001542}=2\,\mathrm{A001109}$,
  $\mathrm{A001110}=\mathrm{A001109}^2$, $2\,\mathrm{A001108}+1=\mathrm{A001541}$, and that the Pell
  numbers interleave A001542 and A001653.

**Counting.**
- **The Pell numbers** are the union of the two observed orbits, disjoint by parity: even $B$
  values are even and odd ones are odd. `observed_count` with $\#R=2$ gives
  $\#\{\text{Pell numbers}\le N\}=2\log N/\log(3+2\sqrt2)+O(1)=\log N/\log(1+\sqrt2)+O(1)$
  (`pell_count`, `log_eps_eq`).
- **Square triangular numbers** count at $\log N/(2\log\varepsilon)$ and the odd ones at
  $\log N/(4\log\varepsilon)$ (`SquareTriangular.sqTri_count`, `oddSqTri_count`).

## 3. The snapshot and the pipeline (`oeis_source.py`, `oeis_orbit.py`, `make_oeis_atlas.py`)

**No live site.** The compiler reads a **versioned local snapshot** through one of two
adapters, and the parser, matching and Lean links are identical either way:
- **`GitExport`:** the official export `https://github.com/oeis/oeisdata.git`, cloned shallow,
  blobless and sparse with `GIT_LFS_SKIP_SMUDGE=1`, so the b-files are never fetched. Its version
  is the export commit and `time.txt`. Entries are added to the sparse checkout on demand.
- **`SeqDir`:** a hand-supplied directory of `.seq` files.

This release used export commit `14eb04df5c1a66f3b8c6d19ac8a5c1dce75f9014` (`time.txt`
2026-09-30T03:00:20−04:00). The global term index covers 399,743 entries; it came from the same
export dated 2026-09-29, with SHA-256 recorded. Everything is in `data/oeis/manifest.json`.

**The pipeline:**
1. **Discovery** (`discover`): the coordinates of three unit orbits ($1+\sqrt2$, $\varphi$,
   $2+\sqrt3$) under 20 observation maps, on all, even or odd powers, are looked up in the global
   index. The index truncates its last term, and the loader drops it. This gives 39, 57 and 19
   candidates. A scan of all names for `Numbers k such that D*k^2 + c is a square` adds 27.
2. **Acquisition:** those entries, plus four Mordell entries (144 in all), are fetched from the
   export and stored **unmodified** in `data/oeis/seq/`, with SHA-256 hashes (CC BY-SA 4.0, see
   `data/oeis/SOURCE.md`).
3. **Verification** (`make verify` → `receipts/oeis_sqrt2_atlas.json`): every candidate is
   re-checked against its **full** entry, term by term with exact integers at the entry's own
   offset. Generated proofs (§5) and duplicate transport are applied. The outcome is one of:

| outcome | rule | √2 | φ | √3 |
|---|---|---|---|---|
| `DEFINITION_PROVED_EQUIVALENT` | definition formalized with the entry's offset (hand-written or generated), Lean theorems present, every term agrees | 29 | 15 | 8 |
| `EXCEPTIONAL_SET_PROVED` | the discovered coordinate disagrees on a finite initial segment; the generated theorem proves the definition equal to an orbit coordinate from a stated index on | 3 | 3 | 0 |
| `TRANSPORTED_FROM_DUPLICATE` | named "Duplicate of X", X proved, every term equal at the same index | 1 | 1 | 0 |
| `TRANSPORTED_WITH_SHIFT` | named "Essentially a duplicate of X", X proved; the terms fix a unique shift among `1 ≤ s ≤ 4` (a tested family, not a determination of the infinite sequence), and `a(n) = X(n + s)` is a Lean theorem | 1 | 0 | 0 |
| `TERMS_AGREE_UNPROVED` | every term of the full entry agrees with the discovered coordinate | 5 | 18 | 10 |
| `REJECTED` | first counterexample recorded; `agrees_from_term` when only initial values differ | 0 | 20 | 1 |

On the √2 orbit the three former rejections A052542, A176981 and A215928 differ from the coordinate
only at $a(0)$; the generated theorems prove each equal to an orbit coordinate from index 1
(`EXCEPTIONAL_SET_PROVED`).
- **A001333**, defined by continued-fraction convergents, is now proved (`SqrtTwoBridges.A001333_eq`).
  The partial quotients of `GenContFract.of √2` are `1, 2, 2, …`, and the continuants are
  `(A_n, B_n)` from `p₋₁ = 1`, which is the entry's `a(0)`.
- **A048624** (dead; "Essentially a duplicate of A000129") is transported with the shift its
  terms fix, `a(n) = A000129(n + 2)`. The text itself does not state a shift. **The qualification
  stays attached:**
  - the 16 listed terms single out `s = 2` only within the tested candidate family (shifts
    `1 ≤ s ≤ 4` of A000129);
  - a finite term list cannot determine an unrestricted infinite sequence;
  - so the Lean theorem is about the reading "A000129 shifted by 2", and the atlas records the
    shift's evidential origin (`shift_from_terms`).

The five unproved √2 entries are A024537 and its duplicate A018905 (a floor recursion), A069306
(binary arrays), A163271 (a "zero-transform") and A171842 (a binomial transform).

## 4. The quadratic-unit orbit engine (`QuadOrbit.lean`)

For a positive nonsquare $D$, a unit $u+v\sqrt D$ of norm $1$ ($u>1$, $v>0$, certified by
`hu : u^2 - D v^2 = 1`) and a finite list of seeds, one Boolean check proves the whole solution
set of $x^2-Dy^2=\Delta$ ($x>0$, $y\ge0$):
- **`seedCheck D u v Δ seeds Ymax`** checks three things by `decide`:
  - the root box: $|\Delta|u^2<D(Y_{\max}+1)^2$;
  - every seed is a solution whose predecessor under the unit is not;
  - every solution with $y\le Y_{\max}$ either has a predecessor or is a seed.
- **`complete`**: `Sol D Δ p ↔ ∃ ρ ∈ seeds, ∃ j, unitOrbit D u v ρ j = p`. This is **seed
  completeness**, and there are several seeds from the start.
- **`unique`**: the seed and the index are determined by the point.
- **Observation identities:**
  - `orbit_rec`: $X_{j+2}=2uX_{j+1}-X_j$, and the same for $Y$;
  - `orbit_mod`/`residues_periodic`: the residues mod $M$ are the iterates of `stepInt`, periodic
    with a certified period (the finite-state modular filter).
- **Growth**: `fst_between`/`snd_between` give $c_1\varepsilon^j\le X_j,Y_{j+1}\le c_2\varepsilon^j$, the
  hypotheses of `observed_count`.
- **Collisions** (`fst_inj`, `snd_inj`, `cross_collision`):
  - on one equation, either coordinate determines the point;
  - between $\pm\Delta$, equal $y$ forces $(x-x')(x+x')=2\Delta$, so $x+x'\le2|\Delta|$: only finitely
    many collisions, all small.

**The ring of integers** (`FibOrbit.lean`). The engine runs in $\mathbb Z[\sqrt D]$. For $D=5$
the ring of integers is $\mathbb Z[\varphi]$, and its unit $\varphi$ (norm $-1$) is not in
$\mathbb Z[\sqrt5]$. The coordinates of $\varphi^n=(L_n+F_n\sqrt5)/2$ satisfy
$L_n^2-5F_n^2=4(-1)^n$, so the $\varphi$-orbit is split by the $\mathbb Z[\sqrt5]$ unit
$9+4\sqrt5=\varphi^6$ (`eps_eq`) into **six seed orbits**, three on each equation:
- `cert_pos`: seeds $(2,0),(3,1),(7,3)$ on $x^2-5y^2=4$, and `pos_iff`: the solutions are exactly
  $(L_{2n},F_{2n})$;
- `cert_neg`: seeds $(1,1),(4,2),(11,5)$ on $x^2-5y^2=-4$, and `neg_iff`: the solutions are exactly
  $(L_{2n+1},F_{2n+1})$.

**Inversion** (`fib_collision`): $F_i=F_j$ only for $i=j$ or $\{i,j\}=\{1,2\}$. The value
determines the index except at $1=F_1=F_2$, and **the parity of the index repairs it**
(`fib_parity_inj`): the two collide on different equations ($\Delta=-4$ and $\Delta=+4$).

**The modular filter and counting**:
- `even_iff`: $2\mid F_n\iff3\mid n$, from the period-3 residue orbit;
- `fib_count` and `even_fib_count`: the Fibonacci numbers count at $\log N/\log\varphi$ and the
  even ones at $\log N/(3\log\varphi)$, both $+O(1)$, each the $r/(P\,d\log\lambda)$ law of
  `observed_count` with the filter's accepted residues.

## 5. The definition language (`oeis_dsl.py`, `OEISLib.lean`, `Generated/OEISAuto.lean`)

The `%N` text of an entry is kept verbatim. When it has one of these forms, it is translated:

| encoding | form | Lean definition |
|---|---|---|
| `LinRec` | $a(n)=c_1a(n-1)+c_2a(n-2)+e$ for $n\ge s$, initial values from the text (or from the terms, recorded) | pattern-matching recursion |
| `GF` | `Expansion of P(x)/Q(x)`, any rational expression, reduced, $\deg Q\in\{2,3\}$ | `gf2`/`gf3`: the coefficient recursion of $Q\cdot A=P$ |
| `Coord` | `F(2n)`, `2*Fibonacci(2*n+2)`, `Lucas(2n)^2`, `Squares of Pell numbers` | the coordinate expression |
| `SetSquare` | `Numbers k such that D*k^2 + c is a square` (and "Positive integers k ...") | the set, with its domain |

**Each translation is re-evaluated against every listed term at the entry's offset**, and a
changed term makes it fail. The compiler then finds the mechanism:
- for recurrences and generating functions, it fits $d\,a(m+r)+s=pX_{\alpha m+\beta}+qY_{\alpha m+\beta}$
  on a family ($\varphi$, $1+\sqrt2$, or $2+\sqrt3$);
- for sets, it runs the engine's seed search.

It emits a proof, which must use one of these lemmas:
- **strides** (`stride_one`, `stride_two`, `stride_four`): $x(k+2\alpha)=T_\alpha x(k+\alpha)+S_\alpha x(k)$,
  with $T_\alpha$ the trace of $\varepsilon^\alpha$. This proves the entry's own recurrence for the
  coordinate, and the emitter requires the stated recurrence to be the stride;
- **`rec_unique`**, **`gf2_eq`/`gf3_eq`**: uniqueness from the first values, checked by `decide`.
  The order-3 case needs the denominator to factor as $(1-x)(1-T_\alpha x-S_\alpha x^2)$;
- **`setsq_enumerates`**: `seedCheck` plus `orderB` (seeds sorted, the last below the first one's
  successor). The merged seed orbits `interleave` then list the set in increasing order from the
  entry's offset (`Enumerates`), skipping merged values below the entry's domain.

**Exact shifted equivalences.** When the recurrence starts late (A288219: "for $n\ge3$"), or the
generating function has a numerator of higher degree (A128588), the theorem is stated from index
$m_0$ or $r$. The earlier values are the entry's own definitional exceptions, and the receipt
records `exact from index r`.

**Domain.** A239365 says "Numbers n such that $10n^2+4$ is a square". $n=0$ is a solution, but the
listed terms start at 12. The compiler reads "positive $n$", records why, and the Lean set is
$\{k\ge1\}$, with merged index 0 (the seed $(2,0)$) skipped.

**Promotion** (`make_oeis_auto.py`) requires all three of:
1. the encoding, read from the name, reproduces every term at the entry's offset;
2. the generated Lean definition is that encoding;
3. the generated theorem compiles.

`--accept` compiles every block alone and pins its SHA-256 in `data/oeis/auto_accepted.json`.
`make verify` regenerates `Generated/OEISAuto.lean` and fails if any block drifts.

**Current snapshot** (140 candidate entries, from three discovery runs and a scan of all 399,743
names for the set pattern):
- 69 blocks accepted, 0 failed to compile;
- by encoding: 27 set definitions ($D$ from 2 to 99, up to three seed orbits), 25 recurrences,
  10 coordinate definitions, 7 generating functions;
- 71 names are outside the language (floors, Pisot sequences, combinatorial objects).

## 6. The withheld family: $2+\sqrt3$

The family $2+\sqrt3$ (norm $+1$, so $S_\alpha=-1$) was added to discovery last, as a test.
Discovery on the global index proposed 19 entries. The compiler translated and proved 8 of them:
A001075, A001353, A001835, A011944, A052530, A067900, A079935, A094347.
- **In every case the proved mechanism is the $\sqrt3$ orbit**, the one discovery proposed. The
  coordinates can differ in form: discovery's "$A+B$ at power index $-1$" for A001835 is proved as
  $X_n-Y_n$.
- The other 11 names are outside the language: Pisot sequences, "standard deviation of $1..k$",
  "Chebyshev $S_r$", triangle sides.
- `receipts/oeis_auto.json` → `withheld_sqrt3`.

## 7. Hand proofs that needed new machinery (`SqrtTwoBatch.lean`)

- **Geometric parametrization** (A046090, A115598, A115599):
  - $X^2+(X+1)^2=Z^2\iff(2X+1)^2-2Z^2=-1$, so the triples are the odd orbit (`triple_iff`);
  - ordered by $Z$ (`ListsBySnd`), A046090 lists them from the degenerate $(0,1,1)$ and A115598/9
    from $(3,4,5)$. Both domains are formalized (`triples_listed`, `pos_triples_listed`).
- **Matrix orbit** (A090390): $(1,0,0)M^n=(A_n^2,2B_n^2,2A_nB_n)$ for
  $M=\begin{psmallmatrix}1&2&2\\2&1&2\\2&2&3\end{psmallmatrix}$ (`vM_eq`).
- **Coprime splitting** (A078522): $(k+1)(2k+1)=m^2$ with coprime factors forces both factors to be
  squares (`Int.sq_of_isCoprime`), which puts $k$ on the odd orbit.
- **Finite exceptional set** (A055792): "$a$ and $\lfloor a/2\rfloor$ squares" is $x^2-2y^2\in\{0,1\}$.
  The value $0$ comes from $x^2=2y^2$ (`sq_eq_two_sq`, from the irrationality of $\sqrt2$), the
  rest from the even orbit.
- **Residue filter** (A046176): $k^2=m(2m-1)\iff(4m-1)^2-2(2k)^2=1$, with $4m-1\equiv3\pmod4$, which
  keeps every other index of the even orbit (`A_mod4`).
- **Entries named through others** (A008843, A008844, A098602): read as the sets their names
  define, and proved equal to the squares and products of the named entries.

## 8. Why the Mordell descent fails, curve by curve (superseded in part by the branch compiler)

The obstruction classes below were a **prediction**. [MORDELL_BRANCH.md](MORDELL_BRANCH.md)
tests it with proofs:
- 26 of the 59 negative-$k$ curves now have Lean-certified complete lists, $y^2=x^3-1$ among them;
- 22 of the predicted 46 closed, and 4 closed that were not predicted;
- the other 33 reduce to irreducible Thue equations, solved externally by PARI and agreeing with
  Sage.

The leads in the Mordell cross-check fall from 155 to 129. (`descent.diagnose`, `make_mordell_obstructions.py`)

`receipts/mordell_obstructions.json` classifies, for each of the 155 curves with $|k|\le100$ that
the compiler cannot enumerate, the first failing checks of the descent certificate.

For $k>0$ (96 curves), $y^2-k=x^3$ factors in a real quadratic field with infinitely many units,
so this certificate does not apply (`REAL_QUADRATIC`). For the 59 curves with $k<0$:

| category | meaning | curves |
|---|---|---|
| `NOT_COPRIME` | a representation of $k^3$ that is not a cube, with $3\nmid h$: $y\pm\sqrt{-D}$ share a prime over 2 or $D$ | 36 |
| `NONMAXIMAL` | the residue check `div_ok` fails: $\mathbb Z[\sqrt{-D}]$ is not integrally closed | 34 |
| `CLASS_3` | not a cube, and $3\mid h(\mathbb Q(\sqrt{-D}))$ | 12 |
| `NONMAXIMAL_CUBE` | a cube of $(a+b\sqrt{-D})/2$ in the maximal order, not in $\mathbb Z[\sqrt{-D}]$ | 6 |
| `UNIT_BEYOND_PM1`, `ELEMENT_CUBE` | a norm-1 representation the table rejects because it assumes units $\pm1$; a representation that is an element cube | 1 each |

**$y^2=x^3-1$.** The certificate fails in two places, and **neither is an arithmetic
obstruction**:
- **The unit $i$.** The table rejects the norm-1 representation $0^2+1^2$ (`UNIT_BEYOND_PM1`)
  because it assumes the unit group is $\{\pm1\}$. Every Gaussian unit is a cube, since
  $i=(-i)^3$ (a correction from the `expert_push` package: an earlier release named $i$ as the
  obstruction). A unit can therefore be absorbed into the cube.
- **The ramified prime.** It also rejects $2^2+2^2=2^3$, and $2+2i=(i-1)^3$ is a cube
  (`ELEMENT_CUBE`). This norm is divisible by the ramified prime $1+i$. The classical argument
  excludes it by parity: $y$ must be even, so $y\pm i$ are coprime.

Repairing the certificate (cube units, and a coprimality case at the ramified prime) unlocks
**only this curve**: units other than $\pm1$ occur in $\mathbb Z[\sqrt{-D}]$ only for $D=1$.

**Joined with the `expert_push` bounded scan.** `expert_scan_join` in the receipt joins the scan by
$k$, keeping signed points, points with $y\ge0$ and distinct $x$ separate:
- the scan covers all 200 curves up to $x\le10^5$, with 103 nonempty;
- 98 of the 155 unresolved curves are nonempty in it;
- all 155 match the published signed count.

This is membership evidence, not completeness.

The broader method wins by a wide margin. A descent in the **maximal order** with a **case split
on $\gcd(y+\sqrt{-D},y-\sqrt{-D})$** addresses every recorded failure of **46 of the 59**
negative-$k$ curves. Of the other 13, twelve have `CLASS_3` and need 3-torsion in the class group
(a genuinely different certificate); the thirteenth is $y^2=x^3-1$.

These counts are an upper bound on what the repaired certificate would prove. They classify the
checks that fail today; they are not proofs.

## 9. Limits

- **Discovery** uses a fixed library of 20 maps on three orbits ($1+\sqrt2$, $\varphi$, $2+\sqrt3$),
  plus a name scan for the set pattern.
- **The definition language** covers:
  - order-2 recurrences whose stated recurrence is a stride of a family;
  - rational generating functions with denominator a stride polynomial, times $(1-x)$ at most;
  - coordinate expressions and the `D k^2 + c` set pattern.

  Continued fractions, floors, Pisot sequences and combinatorial definitions stay unproved.
- **Mordell leads** rest on published counts and bounded scans. The obstruction classes are
  diagnostic, not proofs.
- **Observation theorem hypotheses:** the growth bounds must be geometric and two-sided, and
  disjointness must be proved for each instance.
