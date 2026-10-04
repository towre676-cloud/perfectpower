# Lean formalization of the monograph development push

This push formalizes new work introduced at d2721b4, following the inherited fb20e9f certificate audit. It adds six hand-written proof modules and fourteen generated operator fixture modules. All twenty modules compile against Lean 4.20.0 and the pinned Mathlib. The focused audit checks every new theorem for standard axioms only; Python produces candidate terms, and `decide +kernel` checks finite identities without `native_decide` or `ofReduceBool`.

## Exceptional roots and rational power gaps

`ExceptionalPowerSearch.complete` proves completeness of a finite search assembled from a finite ordinary box and a separate finite set of residual roots. The tail hypothesis forces every solution outside the box to have zero residual. This prevents discarding exceptional roots that lie far beyond a short exclusion threshold. `SharpPowerGap` proves increasing and decreasing gaps between nonnegative real powers, their absolute-value form, and the rational-grid step: an integer lying less than 1/D from p/D must satisfy Dz=p. Its nonnegative-tail theorem shows that D|R| < Q^(d−1), together with y^d=Q^d+R, forces R=0 on the specified nonnegative branch.

`ExceptionalQuartic.solutions` proves unconditionally that y²=x⁴+x−100 has exactly (100,−10000) and (100,10000). The ordinary search uses only the integer interval [−10,10]; the residual root 100 is retained separately. The tail contradiction uses a verified integer power-gap theorem, and the finite packet is evaluated by the kernel.

`IntegerRootFibres` proves exact interval splitting, width-one fibre isolation, the difference-of-squares factor-pair identity, and the integer roots of (x−A)³(2x+1)(x²+1). It also proves directly that y²=((x−1)(x−10^100))²+1 has exactly the four points with x=1 or 10^100 and y=±1. These are direct proofs of the examples; they do not claim correctness of the Python Sturm transcript algorithm.

## Generated operator spaces

`GeneratedOperatorAlgebra` defines words in a generator family and their linear span. A unital subspace closed under left multiplication by generators contains every word. If its proposed basis consists of generator words, it therefore equals the full word span. Further lemmas prove functional separation, propagation of commutation from generators to words, and injectivity from a matrix left inverse.

The fixtures replay all 139 rational operator models in the latest receipt: 135 recurrence models, three small algebra examples, and the field-756 unit model. For each model, Lean checks every saved basis word, every generator-times-basis expansion, and the saved column-matrix decoder equation D X=1. It then proves that the proposed matrix span is exactly the generated word span. The decoder equation is checked for its explicit column matrix; this push does not add a general flattening identification theorem or claim a complete verified dimension/commutant computation. The input manifest binds the source operator receipt and every new Lean module by SHA-256. The generator's linear solver is a witness producer, not a trusted proof oracle.

## Connection projection algebra

`ConnectionProjection` proves idempotence and trace equal to the vertex-space cardinality for T=W B N C under the explicit inverse identity N(C W B)=1 over any commutative ring. It proves the required/forbidden two-edge determinant identity and conditional division under a nonzero denominator. These are reusable algebraic foundations; the actual cyclotomic graph packets, general mixed-event determinant law, positivity, and normalized probability interpretation remain separate proof obligations.

## Reproduction and remaining scope

Run `scripts/check_monograph_push.sh` to regenerate the operator fixtures, compile their dependencies and all twenty modules, and audit every theorem. The GitHub Lean workflow includes this focused check. The complete Python `make test` run passed: 667 tests run, 663 passed, four skipped. Every new Lean module compiled successfully; a complete rebuild of the historical library was not rerun locally.

The general Sturm variation/root-count theorem, squarefree decomposition certificate correctness, Horner tail threshold and its minimality, all sign branches of the sharp-gap algorithm, graph event distribution certificates, and commutant/bicommutant profile certification remain open. General Baker bounds, arbitrary-polynomial automation, number-ring solvers and GPU/WASM deployment are also open. None is inferred from the exact examples or finite operator proofs here.
