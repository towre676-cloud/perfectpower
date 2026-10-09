# Polynomial populations with reusable query semantics

Version 0.6.3 advances the connection between an original equation and the questions asked about its solutions. It supplies sixteen general Lean theorems, a small exact arithmetic query language, and an executable batch certificate route. A batch builds one bounded source population and supports up to sixty-four restrictions, counts, rank selections, and polynomial objectives in both original coordinates. The generic library imports Std and the existing bounded library; it needs no Mathlib compilation.

## Original equation and completeness scope

The source equation is
\[
y^d=P(x),\qquad P(x)=c_0+c_1x+\cdots+c_mx^m.
\]
The public certificate accepts integer coefficients, degree at most thirty-two, and an exponent between two and sixteen. The user supplies an integer x interval. An optional y interval narrows the source domain. Without a y interval, the existing source checker proves that its automatically chosen root cap contains every integer y above the supplied x interval. Reversed bounds yield the empty population.

Let A be the resulting ordered list of pairs. The source theorem states
\[
(x,y)\in A\iff \ell_x\le x\le u_x\ \land\ y^d=P(x),
\]
with the explicit y bounds added when requested. The ordering is x ascending, then y ascending. These are original coordinates, including negative roots and zero. A finite x interval is not a global height bound. Nothing in this release turns a bounded computation into an unconditional solution of an arbitrary Diophantine equation.

## Arithmetic expressions and coordinate substitution

An expression consists of integer constants, x, y, addition, multiplication, and natural powers. Its Lean interpreter evaluates in integers. In the executable AST, powers are limited to zero through sixteen to bound checking cost. The generic theorem itself imposes no such exponent limit.

The polynomial constructor converts a coefficient list into a Horner expression. The theorem polynomial_correct proves for every coefficient list and every integer coordinate pair that evaluation agrees with the source polynomial interpreter. The theorem monomials_horner identifies Horner evaluation with the explicit sum of coefficient times monomial, starting at any exponent. Consequently polynomial_monomials identifies the query expression with the mathematical polynomial rather than only another executable representation.

For expressions s_x and s_y, symbolic substitution replaces x and y throughout an expression e. The universal statement is
\[
\operatorname{eval}(e[s_x/x,s_y/y],p)
=\operatorname{eval}\bigl(e,(\operatorname{eval}(s_x,p),\operatorname{eval}(s_y,p))\bigr).
\]
It is proved by induction over expression construction. The original_equation_pullback theorem specializes it to the source perfect-power equation. This provides a semantics-preserving mathematical operation for arbitrary polynomial coordinate maps. It does not assert that a supplied map is invertible, nor that a noninvertible pullback enumerates every original point. Those are separate obligations when a chart is used as a global solver.

## Restrictions as mathematical conditions

The condition language includes equality, weak inequalities, modular congruences, conjunction, disjunction, and negation. Its mathematical interpreter returns a proposition; its executable interpreter returns a Boolean. The theorem test_correct proves these agree for every condition tree and every integer pair.

The public congruence form requires a positive modulus and compares normalized residues. Negative coordinates and negative requested residues therefore have the usual congruence interpretation. The Lean expression is a remainder equality, so its precise meaning is visible in the reconstructed theorem.

If C is a condition and the source list is complete for a predicate S, the restricted population B is defined by filtering A. The universal restriction theorem establishes
\[
p\in B\iff S(p)\land C(p).
\]
The composition theorem proves that applying two restrictions consecutively gives exactly the list produced by their conjunction. The identity theorem establishes that a selected restricted point belongs to the original source list. Filtering does not change the coordinates or their meaning.

This is a reusable proof over any supplied complete finite source list. The shipped certificate emitter currently supplies such a list through the bounded original-equation checker. Existing globally complete families could use the same theorem once their source completeness theorem is connected; that adapter is not included in this release.

## Rank, selection, and counting

Rank returns the first index of a point, or none when the point is absent. Selection returns the point at a zero-based index, or none when the index lies outside the population. The rank_select theorem proves that every successful rank selects the original point. The rank_exists_iff theorem proves that a rank exists exactly for members of the list.

Duplicates require care: the first occurrence of an item cannot invert selection of a later duplicate. The converse theorem therefore requires a no-duplicates proof. Each emitted query checks that proof in the kernel. For every point p and index i, it then establishes
\[
\operatorname{select}(B,i)=\operatorname{some}(p)
\implies \operatorname{rank}(B,p)=\operatorname{some}(i).
\]
This statement applies to every index of the reconstructed query, not just requested example ranks. The emitted rank-domain theorem also identifies exactly which original solutions have a rank after restriction. Count is the checked list length; the no-duplicates theorem ensures that it counts distinct coordinate pairs. Requested out-of-range selections are checked as none instead of being silently clipped.

## Bivariate polynomial optimization

Objectives use the same integer expression language, so they may involve x, y, their product, and powers. For a nonempty query population, the emitter proposes an integer minimum v and the list T of every tied minimizer. The checker proves the lower-bound assertion over the complete restricted list, then uses the generic objective theorem to conclude
\[
S(p)\land C(p)\implies v\le F(p).
\]
It also checks the exact filtered tie list and proves
\[
p\in T\iff S(p)\land C(p)\land F(p)=v.
\]
The generic objective_attained theorem states how a list member attaining v supplies a witness in the source domain. An empty population returns no minimum. A query without an objective also returns no minimum; its original specification distinguishes these cases. Objectives are query-local, so a neighboring query cannot change whether optimization is requested.

For example, y²=x² on −2≤x≤2 has nine integer pairs. Restricting to y≥0 leaves five. Minimizing x²+y² produces the unique pair (0,0) with value zero. Restricting instead to odd x and minimizing y produces both (−1,−1) and (1,−1), each with value −1. The new route checks these facts against the source equation and proves the associated general rank statements.

## Executable interface and acceptance

The Python functions are population_certificate and check_population in perfectpower.checked_population. The CLI command is checked-population, with --coeff, --d, --x, --queries, optional --y, and --check. The HTTP query operation checked_population returns a proposal through the existing isolated worker. HTTP dispatch does not run Lean or mark the proposal accepted.

An expression is an integer, "x", "y", ["add",a,b], ["mul",a,b], or ["pow",a,n]. Conditions use ["eq",a,b], ["le",a,b], ["mod",a,residue,modulus], ["and",a,b], ["or",a,b], ["not",a], or a Boolean. Each query has condition, ranks, and optional objective fields. Missing condition means true and missing ranks means an empty request list.

The checker reconstructs the entire batch from the specification, rejects any changed packet, and compiles both generic libraries and the reconstructed query in a private directory. It requires Lean 4.20.0. A successful receipt binds the source, specification, and both library hashes. The source population appears once in the batch; queries share that definition. Kernel reduction may still revisit shared definitions, so this is not a demonstrated performance improvement or a proof-cache claim.

The emitted status is a proposal. Kernel acceptance sets proof_status to kernel_checked while execution_verified remains false: the Python interpreter, JSON parser, process execution, and operating system are outside formal program refinement. Proofs concern the reconstructed Lean specification. No arbitrary supplied Lean source is executed. The acceptance check rejects sorry, ofReduceBool, and dependencies outside the three standard Lean axioms.

The rectangle budget defaults to 4,096 points and permits at most 65,536. A batch permits sixty-four queries, sixty-four requested ranks per query, expression depth thirty-two, and at most 128 AST nodes per query. It charges source population size times AST-node count, capped at 262,144. Evaluated expression integers are limited to 4,096 bits. These limits describe the delivered execution route, not the generic mathematical theorems.

## Remaining work

Whole-compiler correctness, the general Sturm variation theorem, global height bounds, and arbitrary unbounded optimization remain open. This release addresses a reusable part of the compiler and population proof boundary. It does not close the entire twenty-five-finding ledger. The next mathematical extension is to attach globally complete source families to these generic query theorems, then broaden the verified reductions that supply such families.

The dedicated check audits sixteen generic theorems and runs actual kernel batches over signed, zero, empty, modular, and explicitly bounded sources. Independent Python scans check randomized equations and optimization results. Mutation checks reject altered answers and altered source specifications. Installed-wheel checks exercise the public API and confirm that the generic library is packaged. Full historical repository verification is a separate expensive gate; focused release evidence must not be described as a fresh audit of every older theorem.
