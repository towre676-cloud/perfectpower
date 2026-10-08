# Factored intersections and concrete predicate covers

## From coprime products to simultaneous equations

The shared branch now has an explicit gcd-fiber intersection service in `residue_atlas_intersection.py` and its companion chapter. This extension preserves that service and adds a separate factored packet schema, independent local replay, exact simultaneous source scans and concrete typed predicate covers. The existing explicit population API still returns an integer in canonical-root order; the new factored API returns count metadata and uses prime-group tuple order. Both cover the same mathematical domain. Every input retains its original polynomial and assigned modulus. The result covers the conjunction of all original modular conditions, with a period equal to the least common multiple of the input periods. It also supplies complete simultaneous integer-source scans in declared rectangles.

For positive moduli m and n, a residue pair a modulo m and b modulo n is compatible precisely when the two coordinates agree modulo gcd(m,n). Coordinate CRT then gives one canonical pair modulo lcm(m,n). Consequently the intersection cardinality is the number of compatible input pairs, rather than the product of the two input cardinalities. The repository already proves the scalar signed-integer LCM intersection law in `PerfectPower/GeneralCRT.lean`. Here complete prime-power input evidence makes compatibility constructive without an arbitrary-modulus square search.

## Local projection and completeness

Flatten each input product into its certified local constraints, keeping all distinct polynomial/modulus pairs and their complete lifting evidence. Group these constraints by prime. For a prime p, let M be the largest assigned power of p. Choose any complete table at that maximal modulus as the seed. A seed residue z survives exactly when its reductions lie in every other table in the group.

$$
R_p=\{z\in R_{\mathrm{seed}}:\ (z_x\;\mathrm{mod}\;m_i,z_y\;\mathrm{mod}\;m_i)\in R_i\ \mathrm{for\ all}\ i\}.
$$

This filter is complete. If an integer point satisfies every source congruence, its reduction modulo M belongs to the seed and projects to every required lower table. Conversely, a retained residue satisfies every group condition by completeness of those tables. The crucial identity is signed reduction through a divisor: reducing x modulo M and then modulo m is the same as reducing x modulo m whenever m divides M. Equal maximal powers with different equations are filtered in exactly the same way.

The Lean `CoverPacket P m` records positivity, canonical roots and an equivalence between reduced membership and an arbitrary predicate P on the original integer coordinates. `ofAtlas` turns an existing source atlas into such a cover. `nested_complete` and `nested` construct a complete cover of the conjunction when the right modulus divides the left. The predicate abstraction is essential: an intersection of different polynomial congruences cannot honestly be labelled as a root table for only one source.

No smoothness premise enters this projection. All children in the input singular lifting packets remain available, and every compatible singular branch survives. `nested_card_le` proves that joining another constraint cannot enlarge a maximal-power seed table. Exact duplicate input packets are removed; ordering the canonical evidence makes input permutation and repetition immaterial.

## Coprime assembly after shared factors are resolved

The normalized prime groups have pairwise coprime moduli. Coordinate CRT therefore bijects the Cartesian product of their complete tables with the global canonical cover. The period and root count are

$$
L=\prod_p M_p=\mathrm{lcm}(m_1,\ldots,m_r),\qquad |R|=\prod_p |R_p|.
$$

The new generic `merge` construction allows two different predicates P and Q. Its complete cover proves P and Q on the original coordinates, with product period for the coprime group moduli. `pair_left`, `pair_right`, `roots_card` and `roots_complete` derive projection, injectivity, exact cardinality and completeness from the existing coordinate CRT identities. Iterating nested joins inside each prime group, then coprime merges between groups, gives a typed proof of the whole intersection.

If any normalized group is empty, the entire conjunction is impossible at every integer coordinate. `CoverPacket.empty_obstruction` proves this global modular exclusion. This implication is global because the congruence cover is complete; a nonempty cover still supplies no height bound or global solution list.

## Exact rectangle populations and addressing

Canonical global roots partition the candidates into disjoint two-coordinate residue cells. For inclusive signed bounds, an axis cell has population

$$
A(L,r;u,v)=\lfloor(v-r)/L\rfloor-\lfloor(u-1-r)/L\rfloor.
$$

The exact candidate population is the sum over retained global roots of the product of the two axis populations. The general `card_candidates` theorem proves this identity for any predicate cover; `candidates_complete` identifies precisely the bounded points satisfying that predicate. Bounds may be negative and enormous. The count uses signed integer division and does not enumerate the coordinate rectangle.

The Python packet keeps normalized prime tables factored when the global class count exceeds its explicit limit. It reuses the coprime traversal only after shared factors have been resolved. Prefix branches are pruned solely when an exact axis population is zero, so every possible descendant in the rectangle is empty. Explicit and factored packets have the same declared ordering: prime-group root tuples first, then x and y ascending inside each final cell. Rank and selection use that ordering, and budget exhaustion raises an error rather than returning an incomplete population or scan. The full JSON traversal and addressing implementation remains tested Python, with a generic Lean interpreter refinement still to be built.

An exact source scan tests every distinct original polynomial equality at each modular candidate. It does not accept modular agreement as an integer solution. The generic `solutions_complete` theorem proves complete source solutions in a declared rectangle whenever the source predicate implies the cover predicate. Native programs derive that implication from the literal original equations and check their returned point lists.

## Six worked intersections

For the parabola y equals x squared modulo 8 and the line y equals x modulo 4, the retained canonical pairs are (0,0), (1,1), (4,0) and (5,1). There are 25 modular candidates in [-8,9] by [-9,8], but only the simultaneous integer-source solutions (0,0) and (1,1). Thus the intersection operation distinguishes simultaneous modular candidates from actual simultaneous zeros.

For the parabola modulo 12 and the line modulo 18, the output period is 36, with 24 compatible pairs. The two input periods share both 2 and 3. Their product, 216, would overstate the period and introduce redundant classes. In [-6,7] by [-7,6] there are four modular candidates and the same two simultaneous source points.

The singular example joins y squared minus x squared modulo 8 with x plus y modulo 4. Its complete local table has 16 retained pairs. Its declared square [-8,8] contains 73 modular candidates and all 17 simultaneous source zeros on y equals minus x. The empty-conflict example joins y modulo 4 with y minus 1 modulo 2 and yields a kernel-proved global impossibility of the simultaneous equations.

The enormous factored example combines the parabola modulo 360 with the line modulo 4. The normalized local root counts are 4, 9 and 5, so there are 180 global classes. In the square with endpoints minus and plus ten to the fortieth, its exact population is 555555555555555555555555555555555555555944444444444444444444444444444444444445. The native program proves that literal integer through the residue-cell count theorem. No scan of that rectangle is attempted. The sixth packet repeats the parabola constraints modulo 4 and 2; its period and roots remain those of the modulus-4 table, and it returns all five exact source points in [-5,5] squared.

## Execution evidence and scope

`python/perfectpower/residue_atlas_intersection_factored.py` exposes intersection, independent replay, membership, population, rank, selection, simultaneous scans and native generation. Replay checks all original local atlas evidence, canonical constraint ordering, each group partition, and a fresh full-square census at each maximal prime power using every original source congruence. It then reconstructs cardinality, period and explicit roots when required. It rejects corrupted sources, omitted classes, false verification flags and inconsistent group metadata.

The release contains six generated native Lean programs and fourteen audited generic declarations, including the three typed cover constructions. The full audit checks 352 declarations with standard axioms only or no axioms. Eleven focused tests cover noncoprime products, different equations, singular and empty groups, negative bounds, huge populations, evidence corruption, addressing, budgets and public dispatch. An independent nested-Horner census compares 120 cases over 162000 LCM-square coordinate pairs; roots, periods, exact source scans, counts and rank/select all agree, including 76 empty intersections. Neighboring residue tests also pass. Native replay checks concrete source identities, complete local tables, all nested filters, coprime coefficients, final counts and supported literal point lists. The audit receipt records the exact declaration count and allowed axioms.

This completes the supported prime-power/product atlas intersection service and its generic typed mathematical bridge. It does not prove a generic JSON parser, Python traversal or source-to-native compiler refinement. Arbitrary incomplete residue sets are rejected rather than promoted to complete source evidence. The next bounded theorem is an interpreter refinement for normalized factor traversal and offsets; global Mordell rank bounds, Matveev premises and singular-period certification remain independent research fronts.
