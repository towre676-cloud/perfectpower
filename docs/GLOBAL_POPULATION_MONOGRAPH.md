# Globally complete populations and original input recovery

Version 0.6.4 connects an existing unconditional integral-point theorem to the reusable query machinery. The source family is y²=x³−2. Its global integral-point proof is rebuilt before a query is accepted. Every nonzero integer affine input x=an+b supplies a derived family y²=(an+b)³−2. Restriction, count, rank, selection, and bivariate objective answers retain global completeness over the declared input domain. The API has no search interval.

## The source theorem

The classical equation y²=x³−2 has exactly the integral points (3,−5) and (3,5). The repository already proved this using the Euclidean ring of integers Z[√−2]. The present release does not claim a new proof of that classical result. It connects the theorem to executable queries and separates its integral-point proof from unrelated density and asymptotic imports.

MordellMinus2Core contains the existing elementary proof, with the same declaration names. The old MordellMinus2 module imports this core and retains the natural-index hit theorem, preserving its public interface. The core proves Euclidean division using rounded integer quotients, establishes that the units are ±1, factors x³ as (y+√−2)(y−√−2), proves the factors coprime, and reduces the cube relation to an integer coefficient equation. That equation forces x=3 and y=±5. No Matveev, externally computed rank, or finite-search premise is introduced.

GlobalMordellPopulation identifies the explicit two-point list with the original equation over all pairs of integers. This theorem supplies the source predicate required by the generic population query library. Finite storage here comes from a globally proved finite solution set, not a finite search domain.

## Exact affine input recovery

Suppose the user's input is n and the source coordinate is x=an+b, with nonzero integer a. Recovering n requires a to divide x−b. Integer division alone would otherwise round a nonintegral preimage into a false candidate.

AffinePopulation defines encode(a,b,(n,y))=(an+b,y) and decode(a,b,(x,y))=((x−b)/a,y). It proves decode_encode for every integer pair when a≠0, encode_decode for every source pair satisfying exact divisibility, and injectivity of encoding. Its pullback first filters source pairs by divisibility and then decodes them.

For any complete source list A and predicate S, the general theorem is
\[
(n,y)\in\operatorname{pullback}(A,a,b)
\quad\Longleftrightarrow\quad S(an+b,y).
\]
The proof works in both directions. A recovered candidate re-encodes to exactly its source pair because divisibility was checked. Conversely, any original solution encodes to a source member, satisfies the divisibility condition automatically, and decodes back to itself. The theorem is generic over any complete finite source population, not specific to the two-point Mordell list.

For the delivered family, the recovered input must be n=(3−b)/a. If a does not divide 3−b, there are no integer solutions anywhere. If it does, the two possible pairs are (n,−5) and (n,5), subject to the requested domain. Negative scales are supported. Zero scale is rejected because the equation becomes independent of n and can have an infinite input fibre, requiring a different population representation.

For example, y²=(5n−7)³−2 has exactly n=2 and y=±5. The expanded polynomial is 125n³−525n²+735n−345. A generated ring proof identifies the affine expression with that original coefficient polynomial for every integer n. The returned polynomial coefficients and coordinate recovery therefore refer to the actual input equation.

The family y²=(5n)³−2 has no integer solutions: 5 does not divide 3. For y²=(2n+5)³−2, the integral solutions have n=−1. Restricting the domain to positive inputs removes both globally. Choosing b=3−10³⁰ returns n=10³⁰ directly, without enlarging a search rectangle or performing a scan.

## Domains and subsequent queries

Supported source domains are all integers, nonnegative integers, and positive integers. Domain restrictions become mathematical conditions on the recovered original input. The source completeness theorem includes that domain and contains no coordinate search bounds.

Each batch then uses the established query language: integer expressions in the original input and y, polynomial arithmetic, equality and inequality conditions, modular congruences, conjunction, disjunction, and negation. Query x denotes the recovered original input n. It is not the intermediate source coordinate an+b.

For every restricted query, membership is equivalent to the original affine equation, declared input domain, and query condition. Counts are checked list lengths with separately checked absence of duplicates. Successful rank and selection operations satisfy the generic inverse theorem. Out-of-range selections return none. Polynomial objectives may involve either coordinate, their products, and powers. The checker establishes an objective lower bound over every admissible integer solution and checks the exact list of all tied minimizers.

Thus minimizing y² on the base family gives value 25 and both signed points. Requiring y≥0 leaves (3,5). On the affine example 5n−7, the same restriction leaves (2,5), and minimizing n·y gives 10. These guarantees cover all integer solutions in the declared domain.

## Executable route

The public functions are global_population_certificate and check_global_population in perfectpower.checked_global_population. The CLI command checked-global-population accepts --queries, --scale, --shift, --domain, and --check. The HTTP operation checked_global_population emits a proposal through the existing isolated worker.

The emitter reuses the finite-source query compiler rather than introducing separate restriction and optimization implementations. Both bounded and global APIs therefore share AST validation, expression evaluation, and theorem emission. Existing bounded certificates retain their explicit interval scope.

Acceptance reconstructs the complete packet from its original specification. Changed points, results, polynomial coefficients, scope, or Lean source are rejected. The checker copies and rebuilds BoundedNative, QueryNative, AffinePopulation, MordellMinus2Core, and GlobalMordellPopulation in a private directory, then audits the source completeness theorem and compiles the reconstructed query. A preexisting repository .olean for the Mordell proof is not substituted for this source rebuild.

Lean 4.20.0 and the pinned Mathlib dependencies must be available. Successful receipts bind the specification, emitted source, and every rebuilt source module by hash. Standard-axiom checking remains part of acceptance. The Python interpreter, JSON parser, and process execution remain outside formal program refinement, so execution_verified is false. A packet is emitted until the kernel checker accepts it.

## Impact and remaining obligations

This closes the missing connection between a globally proved source family and the finite population query interface. It also proves a reusable exact affine input transformation, including divisibility and source-domain preservation. It does not establish global completeness for all 457 externally computed Mordell curves or remove the analytic premises in other families.

The delivered global source is one classical curve and its affine input pullbacks. Further unconditional finite families can enter through the same source-predicate interface. Pell families require a proved infinite generator and corresponding counting operations, so they cannot simply be materialized as finite lists. General Sturm correctness, deeper global bounds, arbitrary number-ring representative completeness, and unbounded optimization over infinite populations remain separate work.

The release records actual global query acceptance for the base curve, a nontrivial affine input, a missing integer preimage, a negative scale, a domain-excluded input, and a very large recovered coordinate. The dedicated proof gate audits the rebuilt source theorem and the new bridge theorems. Focused API and installed-wheel tests accompany these mathematical checks. This evidence is scoped to the changed route; it is not a fresh full historical repository verification or an industrial speedup claim.
