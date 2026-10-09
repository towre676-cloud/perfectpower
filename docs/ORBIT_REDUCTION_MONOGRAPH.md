# From original equations to complete orbit populations

PerfectPower 0.9.0 extends the previous family engines in three connected directions. It recognizes exact polynomial reductions from the original coefficients, makes generalized Pell equations queryable through finitely many checked seeds, and proves saturation at 2 for the supplied bases of all 457 curves in the hard Mordell completion census. Each advance has a precise mathematical scope. In particular, the census advance is not a claim that those curves now have fully proved integral-point lists.

## The practical question

A caller usually has an equation such as `y² = 2x² + x + 1`, rather than a declaration that it belongs to a particular arithmetic family. The new automatic route starts with that equation. It selects a supported exact reduction, constructs a complete finite population in the requested domain, and emits a theorem whose conclusion still uses the original polynomial and original coordinates. Queries can then impose conditions, count the selected points, choose ranks, or minimize an objective with all ties retained.

This changes how the existing engines are reached. The caller can supply ascending polynomial coefficients and let the producer recognize square-plus-constant, a supported cube-plus-constant, or a positive-leading quadratic norm equation. Recognition itself is not trusted as a proof. The resulting polynomial identity and the completeness transport are checked by Lean.

An unrecognized equation is rejected explicitly. The route does not quietly replace a request for a complete solution family with a finite scan. Infinite Pell-type quadratics require an absolute input cutoff. The finite square and supported cubic reductions can be complete over all integer inputs without a cutoff.

## Generalized Pell equations

The generalized equation is

\[
 y^2-Dx^2=N,
\]

with positive nonsquare integer `D`. The previous release concentrated on `N=1`, where a fundamental unit gives a single nonnegative orbit. For general `N`, several seeds can be necessary. Generating many terms from one seed cannot establish completeness: a second orbit may never meet the first.

For example, `y²−2x²=7` has positive-root seeds `(X,Y)=(3,1)` and `(5,3)`, where the seed convention uses `X=y` and `Y=x`. Multiplication by the unit `3+2√2` sends

\[
 (X,Y)\longmapsto(3X+4Y,2X+3Y).
\]

The first seed produces original points `(1,3)`, `(9,13)`, `(53,75)`, and further points. The second produces `(3,5)`, `(19,27)`, and further points. Both are needed. Including the coordinate signs gives 20 solutions with `|x|≤100`.

The implementation uses a proved descent already present in the repository's Pell theory, extracted into a small arithmetic core. Suppose a positive unit `(A,B)` satisfies `A²−DB²=1`, `A>1`, and `B>0`. Its inverse sends a norm solution to

\[
 (AX-DBY,\ AY-BX).
\]

Outside the finite box

\[
 DY^2\le |N|A^2,
\]

this inverse preserves the positive-root, nonnegative-input quadrant and strictly decreases the positive root coordinate. Descent therefore cannot continue indefinitely. Every solution reaches the finite box.

The new machinery goes further and uses terminal positive seeds: the inverse would have a nonpositive first coordinate or a negative second coordinate. A terminal seed must lie in the same proved box. Otherwise the existing descent theorem would supply a positive predecessor, contradicting terminality. Strong induction then proves that every positive-root, nonnegative-input solution lies on the forward orbit of a terminal seed.

The seed box is executable. Its coordinate caps are chosen with integer square roots, but Lean checks the strict square inequalities that justify them. It then checks that the literal seed list equals the filtered finite box. The caller supplies no assumption that the proposed seeds are complete.

Solutions with root coordinate zero are handled separately. For instance, negative norms can admit such points. This separate branch also handles `N=0`, whose only solution for a supported nonsquare `D` is the origin. Empty seed lists, empty populations, zero coordinates, and sign duplicates are retained correctly. The final population is a finite union, so its count does not depend on an unproved assertion that independently generated lists are disjoint.

## Closing a cutoff and selecting distant terms

Within each positive seed orbit, the original input coordinate strictly increases. The producer finds the first orbit index beyond the requested cutoff by exponential bracketing and binary search. A checked boundary value then proves that every term inside the cutoff has an earlier index. This turns finitely many orbit prefixes into a complete cutoff population.

Binary unit powering supports distant selections without stepping through every preceding term. A generic theorem connects the binary calculation to the mathematical unit power, and another connects that power to the orbit recurrence. A selected term therefore has both an exact coordinate certificate and a unique rank within its named seed orbit.

These ranks are per-orbit ranks. They are not advertised as ranks in a globally merged, signed ordering. Finite queries over the complete cutoff population do provide ranks in their declared ordering. A more efficient merged count-only and global selection interface remains a useful next extension.

The implementation bounds resource use rather than silently truncating a mathematical answer. `D` lies in `2..1000000`; input integers use the existing 128-bit specification limit. The fundamental-seed proposal is subject to a configurable seed budget. The complete seed rectangle and emitted orbit population must fit `work_limit`, which is at most 65536. Binary coordinates must stay within 4096 bits. A rejected large seed box means that this particular implementation route could not finish within its budget, not that the equation has no solutions.

## Automatic polynomial reductions

For a polynomial `P`, the producer first attempts exact coefficient extraction of

\[
 P(x)=U(x)^e+k,\qquad e\in\{2,3\}.
\]

Starting at the leading coefficient, triangular coefficient equations determine the proposed integer coefficients of `U`. Exact expansion confirms that all nonconstant coefficients agree. For `e=2`, a nonzero `k` reaches the complete difference-of-squares engine. For `e=3`, `k` must match one of the proved Mordell sources, including the descent atlas. The complete source population is pulled back through all integer fibres of `U`. This preserves repeated roots, zero fibres, negative inputs and the original output signs.

Positive-leading quadratics receive a second treatment. Write

\[
 P(x)=ax^2+bx+c,\qquad a>0.
\]

When `a` is nonsquare, completing the square gives

\[
 (2ax+b)^2-4ay^2=b^2-4ac.
\]

This is a generalized Pell norm equation with `D=4a`. Its first norm coordinate must lie in the residue class `b` modulo `2a`. The inverse coordinate is

\[
 x=\frac{X-b}{2a}.
\]

The checked affine pullback retains that divisibility condition. It does not interpret an integer floor quotient as an inverse when the numerator is indivisible.

For an absolute input cutoff `T`, an elementary bound gives

\[
 y^2\le aT^2+|b|T+|c|.
\]

The norm-engine root cutoff is derived from this bound and checked by a strict adjacent-square inequality. Thus every original solution inside the requested input domain reaches the complete norm population. The final filter returns exactly the original input cutoff and domain, including negative original inputs when requested.

When `a=r²` is square, the norm form splits instead. The automatic route uses

\[
 (2ry)^2=(2ax+b)^2+(4ac-b^2).
\]

The square-difference engine is finite when the offset is nonzero. The inverse output scaling keeps only outputs divisible by `2r`. This supports quadratics whose completed-square inner polynomial would have a fractional constant coefficient, such as `x²+x+1`. Degenerate rational-square quadratics with zero offset require a separate infinite-family interface and are explicitly refused by this route.

## A common census obstruction, now a group theorem

The 457 hard census curves have equations `y²=x³+k` and retained rational bases of rank one or two. Previously, their finite-reduction saturation evidence did not by itself supply a Lean connection to the actual rational point group. The new advance closes a specific prime without needing that reduction-map connection: saturation at 2.

If an affine point with abscissa `u` has a rational half, the half's abscissa is a rational root of the monic quartic

\[
 H_u(t)=t^4-4ut^3-8kt-4uk.
\]

This is connected to Mathlib's actual elliptic doubling formula. It is not merely an identity about a coordinate simulator. Write `u=p/q` in lowest terms. Scaling a root by `q` gives an integer root of the monic integer polynomial

\[
 z^4-4pz^3-8kq^3z-4pkq^3.
\]

The rational-root integrality theorem justifies that statement. A small exhaustive residue scan can then prove that the integer polynomial has no root modulo a chosen modulus. Such a scan excludes every integer root, hence every rational root of the original halving quartic, and therefore every actual rational half of the target point.

All 457 retained bases admit these certificates. There are 443 rank-one bases and 14 rank-two bases. For rank one, the nonzero parity representative is the basis point itself. For rank two, the representatives are `P`, `Q`, and `P+Q`; their actual group addition is checked. This gives 485 halving obstructions.

The branch cubic `t³+k` also has a checked modular root obstruction for every census curve. Its absence of rational roots excludes nonzero rational two-torsion, so doubling is injective. A generic parity theorem now finishes the argument. If `2R=mP+nQ`, subtract the integer halves of the coefficients. A nonzero remainder would supply a rational half of `P`, `Q`, or `P+Q`, contradicting the checked obstruction. The coefficients are therefore even, and injective doubling shows that `R` already lies in the supplied lattice. The rank-one theorem is the corresponding one-generator statement.

The resulting saturation-at-2 theorems are unconditional statements in the actual rational elliptic point groups. They do not require the external rank upper bounds, backend saturation flags, or an assumed global integral-coordinate bound.

## What this does not close

The number of fully formalized hard census completions remains zero. Saturation at 2 is a substantial shared obligation removed from all 457 curves, but full completion still needs curve-specific rank upper bounds, saturation at every remaining relevant prime, and a justified complete integral-point bound or another global completeness argument. A proved subgroup closure at one prime must not be confused with a complete rational basis or a complete integral-point list.

Likewise, automatic reduction covers the families stated above. It is not arbitrary-polynomial automation. The general Baker bounds, broader number-ring norm solvers, general Sturm variation proof, arbitrary infinite-family optimization, and certified smooth higher-genus geometry remain distinct projects. Python packet reconstruction and a private Lean rebuild check each proposed result; this does not formalize the entire Python interpreter or compiler.

## Reproduction and public interfaces

The command `checked-pell-orbits` accepts `D`, `norm`, an absolute input cutoff, optional finite queries, and per-orbit global selections. The command `checked-auto-population` accepts ascending original polynomial coefficients, optional queries, an optional cutoff, and the input domain. Their JSONL/HTTP operation names are `checked_pell_orbits` and `checked_auto_population`. The ordinary result is an emitted proposal; `--check` rebuilds the selected sources privately and checks the packet with Lean 4.20.0 and the pinned Mathlib dependencies.

For example:

```bash
python -m perfectpower checked-pell-orbits --D 2 --norm 7 --cutoff 100 --global-ranks '[{"orbit":0,"rank":1000}]' --check
python -m perfectpower checked-auto-population --coefficients '[1,1,2]' --cutoff 1000000000000 --check
python -m perfectpower checked-auto-population --coefficients '[1,1,1]' --check
```

The focused gates are `make check-orbit-reduction` and `make check-mordell-parity`. The census atlas is split into 29 proof blocks to control compilation memory. `receipts/mordell_parity_atlas.json` records the actual curve audit set and source hashes; `receipts/orbit_reduction_queries.json` retains the checked query replays. The release includes an installed-wheel replay and complete repository archives. The focused checks are reported separately from the repository's much larger historical release verification.

## Retained validation for this release

All 29 census blocks passed their kernel checks, yielding 1,399 audited curve declarations and the 457 unconditional saturation-at-2 conclusions. The generic audit contains 23 declarations with standard Lean axioms only. Eleven retained query replays cover multiple orbits with rank-1,000 selections, negative and zero norms, an empty norm population, finite square/cubic sources, scaled output coordinates, a positive input domain, and an original quadratic cutoff of one trillion. Independent scans agree across 297 generalized-norm parameter pairs, 40 composed-power inputs and 71 quadratic inputs. The focused six-method suite passed, including eight private rebuilds. The installed 0.9.0 wheel passed asset, arithmetic and HTTP checks outside the source checkout. The full historical release-verify was not rerun.
