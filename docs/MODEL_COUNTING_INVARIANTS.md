# Exact counting invariants behind the new implementation

Let `F` be an unweighted CNF over declared variables `V`, and let

\[
Z_V(F)=\sum_{a\in\{0,1\}^{V}}\prod_{C\in F}\mathbf{1}[a\models C].
\]

These are mathematical explanations of the executable algorithms, not new Lean
certificates. Exhaustive and sanitizer checks exercise the implementation.
The native wire format is internal: the Python CNF constructor supplies clauses
with duplicate literals/clauses and tautologies removed, while retaining the
original declared universe. Native search assumes this normalization. SCC
substitution removes any new tautologies it introduces. The public DIMACS
interface is the validating Python parser, not the internal C ABI.
The `equivalence_variables` diagnostic is cumulative over search nodes in a
query. It counts substitutions performed, including separate occurrences of a
variable in different branches; it is not a count of distinct original inputs.

## Propagation and free variables

If unit propagation proves assignments `u` on `U`, then

\[
Z_V(F)=Z_{V\setminus U}(F\mid u).
\]

If propagation finds a contradiction, the count is zero. After simplification,
let `A` be the variables still occurring and `R=V\setminus(U\cup A)`. Then

\[
Z_V(F)=2^{|R|}Z_A(F\mid u).
\]

The occurrence queue stores unprocessed literal counts and the bitwise XOR of
unprocessed signed literal values per clause. When this count reaches one, the
XOR is the remaining literal. Clauses satisfied by an assignment are marked
before occurrences of its negation are processed. Each assignment is queued
once; each falsified occurrence is visited once. The reconstructed formula
contains precisely the unsatisfied clauses with assigned literals removed.
No pure-literal SAT reduction is used: it would not preserve model counts.

## Signed equivalence quotient

For each binary clause `(a or b)`, add implications `not a -> b` and
`not b -> a`. Literals in one strongly connected component imply one another.
If a component contains `x` and `not x`, no model exists.

Otherwise choose one representative per complementary pair of components.
Every removed variable is a representative or its negation. If `q` is the
substitution and `W` is the retained variable universe, then restriction and
unique extension give a bijection

\[
\operatorname{Mod}_V(F)\cong\operatorname{Mod}_W(q(F)),
\qquad Z_V(F)=Z_W(q(F)).
\]

Duplicates and tautological clauses introduced by substitution are removed.
Crucially, the removed variables do **not** contribute a factor `2^k`. Retained
representatives that disappear from all remaining clauses are free and do
contribute their ordinary factor of two. Both SCC traversals are iterative.

Original-variable locks are applied before every quotient. Thus each conditional
query counts original full assignments. The existing lexicographic select and
rank routines use these conditional counts; they do not expose representatives
as original variables. Cache keys contain complete normalized formulas; cache
entries count their active universes, with external free-variable factors kept
outside the stored values.

## Elimination planning and evaluation

Each clause scope creates a clique in the primal graph. When eliminating `v`,
the union of factor scopes containing `v` is exactly `{v}` together with its
current graph neighbors. Summing out `v` connects those neighbors into a clique.
The bitset planner performs this graph update directly, selecting the lowest
degree live variable, with the same deterministic variable-order tie break.

For bucket factors `B_v`, the outgoing factor is

\[
g(y)=\sum_{b\in\{0,1\}}\prod_{h\in B_v}h(y,b).
\]

Finite sum/product distributivity proves that repeated elimination preserves
`Z`. Factor values use arbitrary-size integers. The planner rejects scopes over
18 variables or an estimated total over eight million enumerated states before
allocating the tables. The estimate is a work heuristic, not a proof of runtime
or peak memory. Search remains available when a plan is rejected.

For disjoint component universes and a decision variable `x`, respectively,

\[
Z(F_1\land\cdots\land F_k)=\prod_{j=1}^{k}Z(F_j),
\qquad Z(F)=Z(F\mid x=0)+Z(F\mid x=1).
\]

The engineering gains are empirical. These identities prove counting semantics;
they do not prove that a heuristic beats another solver or that general #SAT
becomes tractable.
