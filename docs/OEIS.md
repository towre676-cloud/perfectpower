# OEIS as a discovery layer: one orbit, many sequences

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
1. **Discovery** (`discover`): the coordinates of $(1+\sqrt2)^k$ under 20 observation maps,
   on all, even or odd powers, are looked up in the global index. The index truncates its last
   term, and the loader drops it. This gives 39 candidates.
2. **Acquisition:** those 39 entries, plus four Mordell entries, are fetched from the export and
   stored **unmodified** in `data/oeis/seq/`, with SHA-256 hashes (CC BY-SA 4.0, see
   `data/oeis/SOURCE.md`).
3. **Verification** (`make verify` → `receipts/oeis_sqrt2_atlas.json`): every candidate is
   re-checked against its **full** entry, term by term with exact integers at the entry's own
   offset. The outcome is one of:

| outcome | rule | count |
|---|---|---|
| `DEFINITION_PROVED_EQUIVALENT` | in the `PROVED` table: definition formalized with the same offset, Lean theorems present, every term agrees | 13 |
| `TERMS_AGREE_UNPROVED` | every term of the full entry agrees with the discovered coordinate | 23 |
| `REJECTED` | first counterexample recorded; `agrees_from_term` when only initial values differ | 3 |

The three rejections are A052542, A176981 and A215928. Each has a different $a(0)$ and agrees
from $a(1)$ on. The 23 unproved agreements include:
- A001333, defined by continued-fraction convergents;
- A046090 and A115598/9, defined by Pythagorean triples;
- A078057, defined by a generating function;
- squares of other entries (A008843, A008844, A079291);
- duplicates (A048624, A090757).

Their definitions are not formalized, and nothing is claimed for them.

**The Mordell cross-check.** A081119 and A081120 give the number of integral solutions of
$y^2=x^3\pm n$ for $n\le100$. The comparison with Lean covers every $k$ with $|k|\le100$ whose
complete list Lean certifies: registry curves, pointless curves, descent certificates and the
Fermat family. That is **41 curves, with 0 disagreements**.

For the 155 curves the compiler cannot enumerate, the published count and a scan to
$x<10^5$ are recorded as **leads**:
- 98 are nonempty;
- in all 98 the scan finds exactly the published number of points;
- they are ranked nonempty first, then by $|k|$.

A081119 cites Gebel–Pethő–Zimmer (1998) and Bennett–Ghadermarzi (2015) for the computation. It
also records a proof route: when the rank is $0$, the integral points are the torsion points. A
published count is not a proof. Turning a lead into a theorem means supplying
`Transport.IntegralPointsOnImage` by a Lean-checked route, as `Descent.lean` does for
$y^2=x^3-D$. For the first lead, $y^2=x^3-1$ (only $(1,0)$), the descent certificate fails at
the norm-1 representation $0^2+1^2$, that is, at the unit $i$ of $\mathbb Z[i]$.

**The problem export** (`receipts/oeis_problems.json`, `make_oeis_problems.py`) still lists
PerfectPower's own coordinates, with their terms, recurrences, constants and Lean names, for
comparison with any snapshot (`python -m perfectpower oeis`, `make oeis`).

## 4. Limits

- **Discovery** uses a fixed library of 20 maps and three index filters on one orbit. Other
  orbits, other norm equations and other maps are not searched yet.
- **Promotion** requires a human-written Lean definition matching the entry's text. Parsing
  `%N` lines into Lean is not automated, and entries defined by convergents, generating functions
  or combinatorial objects stay unproved.
- **Mordell leads** rest on published counts and bounded scans, and are never promoted
  automatically.
- **Observation theorem hypotheses:** the growth bounds must be geometric and two-sided, and
  disjointness must be proved for each instance.
