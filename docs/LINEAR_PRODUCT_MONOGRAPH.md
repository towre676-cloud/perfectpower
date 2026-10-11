# Complete linear-product solution charts

This release completes one arithmetic application from a supplied equation to a finite, queryable solution set and, for retained instances, a Lean theorem that characterizes every integer solution. Its supported equations are

\[
 y^2=(an+b)(cn+d),\qquad a,c\ne0,\quad ac=s^2>0,\quad ad-bc\ne0.
\]

All four coefficients are integers. Both coordinates range over all signed integers. There is no user-selected coordinate rectangle and no implicit cutoff on the size of a solution. The program accepts unequal slopes and negative slopes when their product is a positive square. It rejects a nonsquare leading product, a negative leading product, a repeated linear root, and higher-degree factors. Such rejection is a boundary of this solver, not a declaration that the rejected equation has no solutions.

**What becomes executable.** The earlier Euclidean machinery could prove an integral polynomial Bézout identity and use its nonzero constant to identify exceptional primes. Its branch compiler covered the possible power residues at those primes but left the resulting equations unsolved. The new `solve-descent` operation closes every branch for the family above, including branches with no solutions, and retains zero-product solutions separately. A standalone `solve-linear-product` operation avoids constructing the full exceptional-prime packet when only the complete point set is needed. A population interface then counts, ranks and selects those points under coordinate and congruence restrictions, and finds exact optima. Assignment to the old descent branches and population queries remain tested Python. The Lean certificate characterizes the original equation's entire point set.

**The finite reduction.** Write

\[
 q=ac=s^2,\qquad t=ad+bc,\qquad \Delta=ad-bc.
\]

Expansion gives the polynomial identity

\[
 (2qn+t)^2-4q(an+b)(cn+d)=\Delta^2.
\]

If the original equation holds, the identity becomes

\[
 (2qn+t-2sy)(2qn+t+2sy)=\Delta^2.
\]

Set the two factors equal to \(u\) and \(v\). Because \(\Delta\ne0\), their product is nonzero and there are only finitely many signed divisor pairs. Conversely, a pair with \(uv=\Delta^2\) gives potential coordinates

\[
 n=\frac{u+v-2t}{4q},\qquad y=\frac{v-u}{4s}.
\]

Both fractions must be integral. The implementation explicitly checks both congruences before accepting a point and checks the original equation afterward. These congruences matter: rounding the fractions and checking only the resulting equation can admit duplicate chart entries from pairs that did not reconstruct integrally. The Lean chart includes the same integrality conditions.

This is a classical difference-of-squares reduction. The engineering contribution is its integration with the existing resultant evidence, complete signed enumeration, a usable query interface, and generated all-integer proofs. No new theorem about arbitrary Diophantine equations is claimed.

**How the resultant is reused.** For the two ascending coefficient lists `[b,a]` and `[d,c]`, the integral resultant is \(\Delta\). The existing routine supplies polynomials \(U,V\) with \(UA+VB=\Delta\), binding the arithmetic obstruction to the original factors. The new solver factors \(|\Delta|\), doubles each prime exponent, and generates divisors of \(\Delta^2\) from that factorization. It does not trial-divide every integer up to \(|\Delta|\) merely to list divisors of the square. The factorization work, divisor expansion and pair traversal all consume the declared work budget. Exhaustion raises `WorkLimit`; it never returns a shortened list labeled complete.

The default Python budget is one million operations as counted by these stages. This is an algorithmic operation budget, not a uniform wall-clock guarantee: large-integer multiplication and input processing still have costs. The existing resultant module also limits coefficient size. The results include the exact transform, factorization, signed divisors, accepted pairs, sorted points and consumed work. Canonical replay rejects changed inputs, omitted points, missing pairs, and altered completeness metadata.

**A small complete example.** For \(y^2=n(n+6)\), the complete signed point set is

\[
 \{(-8,-4),(-8,4),(-6,0),(0,0),(2,-4),(2,4)\}.
\]

There are exactly six coordinate pairs and four distinct inputs. Restricting to \(n\ge0\) and \(y\ge0\) leaves \((0,0)\) and \((2,4)\). Zero-based selection at rank one returns \((2,4)\); maximizing \(y\) gives value four at that point. Rank and selection use lexicographic order on coordinate pairs, and an absent point has no rank. Optimization returns every tied optimum rather than arbitrarily choosing one. Empty restricted populations have no optimum.

A shift by \(10^{80}\) produces the corresponding six points with their first coordinates shifted by that amount. The divisor work is unchanged because the resultant remains six. This demonstrates why a finite arithmetic chart is different from scanning coordinates: moving solutions far away need not enlarge the enumeration. It does not make arithmetic on eighty-digit coordinates free.

**What Lean proves.** `PerfectPower/LinearProductChart.lean` imports the existing Std-only Euclidean foundations. It proves that every nonzero integer divisor lies within the bounded signed range used by its reference enumeration, that its pair list contains exactly the pairs whose product is the specified nonzero constant, and that integral reconstruction recovers the original coordinates. Its generic `complete` theorem equates an equation satisfying the stated transform identity with membership in the finite chart.

The source emitter proves an actual coefficient-list identity for each supplied polynomial, evaluates it using the already proved Horner addition, multiplication and scaling laws, and checks the finite chart against the submitted solution list. Its final `all_integer_solutions` theorem states

\[
 \forall n,y\in\mathbb Z,\quad y^2=(an+b)(cn+d)
 \iff (n,y)\in\texttt{solutions}.
\]

It is a completeness theorem, not merely a collection of checks that listed points satisfy the equation. Both positive and negative output coordinates are included. The proof also binds the quadratic polynomial back to the two supplied linear factors.

Seven retained sources cover adjacent factors, a nontrivial six-shift example, negative slopes, unequal slopes, an empty solution set, an odd midpoint and an eighty-digit coordinate translation. All seven passed Lean. The generic theorem and accepted sources use only standard Lean axioms `propext`, `Classical.choice` and `Quot.sound`; there is no `sorryAx` in the accepted log. Deliberately changing a polynomial or deleting a solution makes Lean reject the source. Those failures are retained separately in `kernel-rejection.log` and must not be mistaken for accepted proofs.

**The proof-generation boundary.** The Python solver enumerates divisors using factorization. The Std reference chart uses a deliberately simple bounded signed enumeration. Generated instance checking therefore has a separate budget: by default, \(2\Delta^2+1\) must not exceed one hundred thousand. A large Python chart can be complete while this proof emitter refuses to enumerate its reference chart. The generic chart theorem remains available, but the faster Python execution and its large output have not thereby been kernel checked. A faster formally proved divisor enumerator is a concrete next improvement. Compiler manifests say `kernel_checked: false` when generated; the separate successful-run receipt records which exact source hashes were checked.

**Measured comparison.** The release retains twelve calibration cases and sixty-seven deterministic synthetic evaluation cases, with inputs saved separately. The baseline uses the repository's existing `divisor_square.signed_divisors` routine on the same transformed constant, followed by congruence reconstruction. Both methods receive a two-hundred-thousand-operation budget. Each completed case is timed five times; the report retains raw samples and uses their median. The order of the two methods alternates by case. Timing covers complete Python requests and excludes Lean proof checking.

The new route completed all sixty-seven evaluation cases. The baseline completed sixty-five; its two work-limit failures remain in the report and are excluded from the comparable-case speed ratio. All sixty-five common complete cases had identical point sets. The summed median runtimes were approximately 0.0109 seconds for the new route and 0.3510 seconds for the baseline, a ratio of about 32.2. The median per-case ratio was about 23.8. Three evaluation cases were slower with the new route. Ten of twelve calibration cases were slower, even though their aggregate runtime favored the new route because the larger cases dominated the total.

These timings establish a useful advantage over this particular divisor-listing baseline on this synthetic family. Their absolute runtime difference is only about a third of a second for the common evaluation set. They do not establish superiority over strong external number-theory systems, a general SMT advantage, or a customer workload improvement. The corpus is synthetic and reproducible, not a public industrial corpus. Future comparisons should include established external Diophantine solvers and application-specific tasks before commercial performance claims are made.

**Independent correctness coverage.** Nine new test methods include exhaustive small-coefficient comparisons against an independent coordinate scan covering the mathematically bounded input range, deterministic random cases, factor swapping, simultaneous sign changes, the old descent classifier, branch partitioning, complete zero cases, packet corruption, work exhaustion and query edge cases. The retained run also passes fourteen Euclidean regression tests, nine divisor-reuse tests and seventeen graph-method tests. Coordinate scanning is used as an independent test on small inputs; it is not the new production solver.

**Running the application.** From the repository root, use `PYTHONPATH=python python3 -m perfectpower euclid solve-linear-product examples/linear_product/solve.json`. Replace the operation with `solve-descent` to retain the closed exceptional-prime branch partition. Run `query-linear-product examples/linear_product/query.json` for the restricted population example. Windows users can set `PYTHONPATH` to the repository's `python` directory and use their available Python launcher. Coefficients are always in ascending order.

`make linear-product` runs the new tests and regenerates the exact examples and emitted sources. `make linear-product-kernel` checks the generic proof, all seven sources and the two rejection cases; it requires Lean 4.20.0 and honors `PERFECTPOWER_LEAN`. `make linear-product-benchmark` reproduces the timed comparison. New wall times will differ, so the complete report contains the inputs and timing method rather than pretending the recorded ratios are constants of the algorithm.

**Where the application now stands.** This release closes one supported arithmetic family all the way through exact enumeration and proof of completeness for retained instances. It provides an executable example of the repository's larger goal: a mathematical reduction becomes a complete solution space that another program can query. The next expansion is not to label every polynomial branch solved. It is to extend this route to further families, improve kernel divisor enumeration, and measure those applications against credible external baselines. Nonsquare leading products require an appropriate generalized Pell treatment; proportional factors need an infinite-family representation; higher-degree factors need additional branch solvers. Those remain separate obligations.
