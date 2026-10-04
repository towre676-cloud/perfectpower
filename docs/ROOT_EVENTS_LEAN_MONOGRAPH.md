# Complete integer-root witnesses and finite graph-event laws

This development follows the monograph push and preserves the documentation reorganization at af68d0d and the subsequent machinery push at 67baee3. It formalizes two operational gaps: proving that interval pruning retains every integer root, and proving arbitrary finite inclusion/exclusion graph events from checked determinant moments. The general real-root Sturm variation theorem is not claimed here. Integer-root completeness is proved directly with Bernstein exclusion witnesses, while the graph theorem applies over arbitrary commutative rings and is instantiated with exact rational distributions from the stored corpus.

## Integer roots without a trusted Sturm count

The Python Sturm routine is a discovery mechanism. Its root list, variation counts, squarefree decomposition and subdivision choices are not premises in the resulting Lean completeness theorem. For any nonconstant integer polynomial with nonzero leading coefficient, the already-proved Horner height bound contains every integer root. Inside that bound, `BernsteinRootTree.Tree` partitions half-open intervals (a,b] using empty nodes, width-one cells, certified exclusions and exact binary subdivisions. Induction proves that its returned finite set contains exactly the roots in that interval. Combining this with the outer bound proves completeness on all of ℤ.

The exclusion witness writes the original polynomial, up to a nonzero rational scalar, in the unnormalized Bernstein form

\[
F(x)=s\sum_{i=0}^{n} c_i(x-a)^i(b-x)^{n-i},\qquad s\ne0,\quad c_i\ge0,\quad c_n>0.
\]

For a<x≤b every term is nonnegative and the last term is positive. Thus F(x) cannot vanish. Lean checks coefficient signs by kernel reduction and checks the exact polynomial identity with `ring`. It separately evaluates every width-one cell, including cells containing real roots that are not integers. A missed integer root cannot be hidden by a mistaken Sturm variation count: the corresponding exclusion identity would be false, or its sign conditions would fail.

Seven closed fixtures cover separated giant roots, a degree-six polynomial with a repeated root, a half-integer root, a positive quadratic, a fractional linear root, negative roots, zero, and four consecutive roots. Together their witnesses contain 57 nodes, including 18 certified exclusions and 14 width-one cells. The two giant examples each use nine nodes, compared with 1,329 and 1,331 nodes in their stored Sturm discovery transcripts. Their complete integer-root theorems concern the original coefficient lists, with no named analytic or root-count premise.

`SturmChainAlgebra` additionally proves local signed-remainder invariants: opposite signs at a middle zero under positive rescaling, propagation of common zeros, separation by an explicit Bezout identity, and preservation of zero sets by positive multiplicities. These lemmas support future chain verification. They do not constitute the classical analytic proof that variation differences count all distinct real roots.

## Arbitrary finite graph events

A principal restriction is represented by `padded K S`, which keeps rows of K indexed by S and puts identity rows elsewhere. Its determinant is the usual identity-padded principal determinant. `PaddedPrincipalMinor` proves equality with the principal submatrix determinant and connects the shifted principal determinant used by the event implementation to the padded formula. This representation fixes the ambient matrix type across different event subsets and avoids repeated conversions between dependent index types.

Multilinearity of the determinant yields a general forbidden-row expansion. For disjoint required and forbidden sets I,J, `DeterminantalEvents.mixed` is the signed determinant obtained by subtracting identity entries on forbidden diagonal positions and restricting to I∪J through identity padding. The theorem proves its finite subset expansion for any commutative ring and any finite index type. No two-edge or fixed-size restriction remains.

`FiniteGraphProbability.mixed_probability` connects that algebra to a finite weighted law. If every inclusion moment equals the corresponding padded determinant, the mixed determinant equals the total weight of outcomes containing I and avoiding J. The inclusion-moment identity is an explicit hypothesis in the general theorem. Nonnegative normalized weights imply event masses lie in [0,1]; refinement decreases mass, and conditional probabilities lie in [0,1] whenever the conditioning mass is positive. Both real and rational event bounds are formalized.

The fixtures prove facts about explicit matrices, outcome sets and normalized weights copied from the source receipts; they do not prove the Python JSON reader or derive cyclotomic basis weights from incidence matrices. The closed corpus fixtures discharge the inclusion-moment hypothesis for all 64 stored nonsingular models whose transfer kernels are rational. Their normalized basis weights are rational even in some models where the unnormalized cyclotomic weights are not. Deduplication produces 14 distinct finite laws. Lean proves nonnegativity, normalization, all 444 inclusion moments, and the mixed-event theorem and probability bounds for every disjoint pair of subsets. This covers 4,788 possible required/forbidden/unconstrained assignments across the distinct laws, by general theorems rather than a separate evaluation of each assignment.

## Efficient determinant witnesses

Checking a determinant by enumerating permutations is unnecessarily expensive. `TriangularDeterminant.checked` instead accepts a unit lower-triangular elimination matrix E and an upper-triangular matrix U with EA=U. Their triangular shapes, E's unit diagonal, the matrix product and U's diagonal product are all checked by Lean. The determinant theorem follows from det(E)=1 and determinant multiplicativity. Python Gaussian elimination only proposes E and U; an incorrect elimination result cannot satisfy the checked matrix equation.

The current fixture producer requires elimination without pivot exchange. It explicitly refuses an unsupported zero pivot with a nonzero entry below it. This is a producer limitation, not an extra hypothesis hidden in any accepted determinant theorem. It suffices for all the rational graph laws in this corpus. The certificate reduces arithmetic checking from permutation enumeration to finite matrix multiplication. Moment proofs are emitted in batches of eight per module, so the kernel can release reduction caches between batches. Inclusion completeness is assembled by membership case splits rather than an expensive powerset equality computation.

## Reproduction and scope

Run `scripts/check_root_events.sh` to regenerate the witnesses, build their dependencies and 91 proof modules, and audit every new theorem. The focused audit records source and module SHA-256 hashes and rejects nonstandard axioms, missing declarations, errors and warnings. The main Lean workflow includes this focused reproduction. The standard Python suite ran 690 tests: 686 passed and four optional tests were skipped. Those skipped historical Lean integration tests depend on a broader build cache; every new module in this development is compiled separately. A complete rebuild of the historical library was not performed locally.

Remaining work is the classical real-root Sturm variation/root-count theorem and verified general chain generation; acceptance-completeness and uniform resource bounds for the Bernstein witness producer; the general weighted Cauchy–Binet derivation of inclusion moments for arbitrary connection graphs; and closed replay for the 120 nonsingular stored models with nonrational kernels. The other twelve stored models have rank-deficient positive support, so the normalized basis measure is undefined there. None of these remaining obligations is inferred from the 64 closed rational instances.
