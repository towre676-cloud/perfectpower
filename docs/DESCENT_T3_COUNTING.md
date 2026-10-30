# T3: two-isogeny counting with the torsion correction retained

**Status: mathematical argument and Lean proof candidate, NOT replay-verified.**
Prepared on 2026-10-30 against main `1f6b07f90c3a7bc05444a099da444a7839f37ae3`.
The first focused CI run, 41089312295, ended in `startup_failure`; its jobs
endpoint returned zero jobs. No compiler diagnostics or fresh axiom-audit output
exist. The local environment has no Lean/Lake/elan executable, and direct
GitHub downloads timed out. Consequently this work must remain a draft pending
`bash scripts/check_descent_t3.sh` in a working pinned Lean environment.

## 1. What was independently inspected

Main's `IsogenyIndexBridges.lean` proves, for f:G→H and g:H→G,

    [G : g(f(G))] = [H : f(G)+ker(g)] [G : g(H)].

Its kernel-correction lemma is the subgroup tower identity. Combining the two
gives c [G:2G] = [H:f(G)] [G:g(H)] when gf=[2], where

    c = [f(G)+ker(g) : f(G)] = [ker(g) : ker(g) ∩ f(G)].

The implementation uses `f.range.relindex (f.range ⊔ g.ker)`. This is exactly
the correction above, not the order of ker(g) in all circumstances. Main's
`DescentRankBridge.lean` then substitutes the doubling-index formula obtained
from an explicit additive equivalence G ≃ F×T, with F finite free over Z and T
finite. That substitution is valid; the equivalence remains a hypothesis.

PR #9 head `5315dcfe7107833c2b713e15bd85faa2eb8bd647` and PR #10 head
`f23520a7ba3340bcb661fb71e02704c04dccb8e7` were inspected through their actual
source files as well as their descriptions. Both PRs were open. Their source
modules live under `independent_checks/lean_gap`, not under the buildable module
paths their imports name. The new branch promotes the files to `PerfectPower/`
without changing their mathematical contents. It also promotes the squareclass
uniqueness dependency and preserves both original axiom-audit lists.

In the repository's notation E=E(a,b), D=E(-2a,a²-4b), f=phiHom:E→D,
g=dualHom:D→E. The descent map deltaPhi is on D and deltaDual is on E.
Thus the exact pairings are

    ker(deltaPhi) = image(phiHom),
    ker(deltaDual) = image(dualHom).

PR #9 supplies the easy inclusions, the homomorphism laws, and finite image
bounds for integer parameters. PR #10 supplies the reverse inclusions by
explicit quartic-cover preimages, including the exceptional coordinate zero.
The final kernel identifications have only the nonsingularity assumptions
b≠0 and a²-4b≠0. A globally soluble family of arbitrary-label quartic covers is
not a premise of these kernel identities: their construction needs only the
trivial label. These observations are source inspection; the prior reports'
successful compiler/axiom claims have not been freshly replayed here.

## 2. The general kernel-counting identity

Let K=ker(g)∩image(f). Restrict f to ker(gf). Its kernel is ker(f), and its
image is K: if g(f(x))=0, f(x) belongs to K; conversely, every element of K has
a preimage x with g(f(x))=0. Hence

    0 → ker(f) → ker(gf) → K → 0.

For finite kernels this says |ker(gf)|=|ker(f)| |K|. Also
c |K|=|ker(g)| by the subgroup index formula. Multiplication yields

    c |ker(gf)| = |ker(f)| |ker(g)|.                       (1)

The Lean candidate `kernel_composition_count` proves the corresponding
Nat.card identity using Mathlib v4.20.0's `relindex_inf_mul_relindex`,
`relindex_ker`, and `map_comap_eq`. It uses no cancellation. Consequently its
natural-card formulation also handles infinite groups using Mathlib's convention
that Nat.card of an infinite type, and an infinite natural index, are zero.
One must not read zero as an actual finite cardinality. In the elliptic
application below both isogeny kernels are explicitly finite.

Equation (1) is more general than a two-isogeny theorem: it applies to any
pair of homomorphisms between abelian groups. In particular it does not assume
that the correction is two, or that the product of the two kernel orders is
four. Those are separate facts to establish in a particular application.

## 3. Exact descent images and divisor four

The first isomorphism theorem and the two kernel identifications give

    |image(deltaPhi)| = [D(Q):phi(E(Q))],
    |image(deltaDual)| = [E(Q):dual(D(Q))].

The candidate `exact_descent_count` combines these with the existing index
identity, while `elliptic_exact_descent_count` instantiates it with the actual
point-group homomorphisms and PR #10's exactness theorems. Neither requires
Mordell–Weil decomposition, saturation, or height bounds.

Since gf=[2], equation (1) becomes

    c |E(Q)[2]| = |ker(phi)| |ker(dual)|.                  (2)

The unconditional torsion-normalized form, with no rank premise, is

    |image(deltaPhi)| |image(deltaDual)| |E(Q)[2]| = 4 [E(Q):2E(Q)].

`elliptic_torsion_normalized_count` obtains this by multiplying the existing
index equation by |E(Q)[2]| and substituting (2); it does not cancel a possibly
zero natural index.

Each explicit rational isogeny kernel consists of O and (0,0), so each has
order two. `phi_kernel_card` uses main's `phi_eq_zero_iff`. The new
`dual_eq_zero_iff` handles x=0 using `rawDual_some_zero`; for x≠0,
`dual_some` produces an affine image, which cannot be O. The generic
`card_two_of_description` supplies the cardinality without assuming a finite
point group. Thus the candidate specializes (2) to c |E(Q)[2]|=4.

If a genuine decomposition E(Q)≃F×T is supplied, then

    [E(Q):2E(Q)] = 2^rank(F) |T[2]|,
    |E(Q)[2]| = |T[2]|.

The first equality is already proved in main. The new candidate
`doubling_kernel_card_from_decomposition` constructs an equivalence of the
two kernels; the free coordinate of a two-torsion point is zero because a free
Z-module has no nonzero element killed by 2. Substituting into exact descent
counting and using (2) proves

    |image(deltaPhi)| |image(deltaDual)| = 4 · 2^rank(F).  (3)

`elliptic_divisor_four_from_decomposition` states precisely (3) with the
actual equivalence still present. `rank_count_of_doubling_index` is the general
version, with denominator |ker(f)| |ker(g)| and an explicitly stated
doubling-index interpretation. No theorem constructs a Mordell–Weil
decomposition from finite descent images alone.

The classical notation 2^r=(|image(deltaPhi)| |image(deltaDual)|)/4 therefore
has two distinct ingredients: unconditional group counting, and a justified
interpretation of the doubling quotient in terms of Mordell–Weil rank.
It is not valid to replace an unproved decomposition with a computed integer
called rank. The statement concerns actual descent images; a finite collection
of locally soluble covers is not automatically that image. A Selmer computation
may instead provide an upper bound until the relevant global solubility gap is
resolved.

## 4. Exceptional intersection and rational torsion

For these nonsingular models, E(Q)[2] consists of O, (0,0), and any rational
roots of x²+a x+b. Because b≠0 and a²-4b≠0, the quadratic contributes either
zero or two distinct nonzero roots. Accordingly:

| Condition | Rational two-torsion order | Kernel intersection order | c |
|---|---:|---:|---:|
| a²-4b is not a rational square | 2 | 1 | 2 |
| a²-4b is a rational square | 4 | 2 | 1 |

In the second case the nonzero dual kernel point is already a phi-image of
a rational two-torsion point. Ignoring this intersection would give the wrong
doubling index. In both cases c|E(Q)[2]|=4, so the final divisor-four formula
survives once rank is legitimately interpreted. Additional rational four-torsion
does not change this calculation; the relevant factor is T[2], not |T|.
The general cardinal theorem formalizes the cancellation; the coordinate
square/nonsquare case classification in this section is a mathematical
explanation and exact Python test, not a separate compiled Lean theorem.

## 5. Exact tests actually run

`python3 scripts/check_descent_t3.py` passes using only the Python standard
library and exact fractions. It tests these curves (a,b):

| a | b | Rational two-torsion order | Intersection order | c | Explicit order-four point |
|---:|---:|---:|---:|---:|---|
| 0 | 2 | 2 | 1 | 2 | — |
| 0 | -1 | 4 | 2 | 1 | — |
| 1 | -2 | 4 | 2 | 1 | — |
| -1 | 1 | 2 | 1 | 2 | (1,1) |
| 3 | 1 | 2 | 1 | 2 | (-1,1) |

The y=0 roots give the entire rational two-torsion set exactly. Their phi
images compute the entire kernel intersection using gf=[2]. The tests also
check 104 bounded rational-point composition occurrences and explicitly
double the order-four witnesses to (0,0). These checks do not assert total
torsion classifications or Mordell–Weil ranks.

The same script exhausts all 372 homomorphism pairs between the groups
0, C2, C3, C4, and C2×C2. It checks both the general composition-index and
kernel-counting identities. Of these pairs, 120 factor doubling, and every
degree-two-kernel example has correction times two-torsion equal to four.
The deterministic receipt is `receipts/descent_t3/exact_checks.json`.

## 6. Exact dependency and verification ledger

| Statement | Mathematical hypotheses | Current evidence |
|---|---|---|
| Composition and corrected doubling index | actual group homomorphisms; gf=[2] for doubling | already in main; source independently inspected |
| deltaPhi, deltaDual are homomorphisms | b≠0, a²-4b≠0 as appropriate | PR #9 source promoted unchanged; fresh replay blocked |
| Both descent kernel/image equalities | nonsingular rational models | PR #10 source promoted unchanged; fresh replay blocked |
| Finite descent images | integer coefficients and nonzero relevant coefficients | PR #9 finite image bounds; fresh replay blocked |
| General kernel-counting identity | abelian groups and homomorphisms | new Lean candidate; exact finite tests passed |
| Elliptic correction times two-torsion equals four | b≠0, a²-4b≠0 | new Lean candidate; five exact curve tests passed |
| Classical rank/image formula | actual free-plus-finite decomposition (or explicit justified doubling-index formula) | new conditional Lean candidate; decomposition not discharged |
| Generated subgroup is the entire rational point group | PrimeSupport plus PrimeSaturated at its primes, or BoundedIndex plus required prime saturation | existing conditional MordellCompletionBridge results; inputs remain open |
| Finite integral-point enumeration is globally complete | hbound for all integral solutions, plus the enumeration equality | existing conditional result; global height/coordinate bound remains open |
| Full Selmer/global cover theory | arbitrary-label cover equivalences and relevant local/global analysis | not established by this work |

The audit runner replays the original 18 delta and 16 cover declarations and
the 17 new counting declarations. It requires exactly one axiom listing per
declaration and rejects anything outside propext, Classical.choice, Quot.sound,
including sorryAx and Lean.ofReduceBool. The new source contains no sorry,
admit, or added axiom declarations. This source property is not a substitute
for compiling and inspecting the transitive axiom dependencies.

No main merge, release, Explorer synchronization, unconditional rank theorem,
saturation closure, or global height bound is claimed. The next acceptance
gate is a successful pinned Lean replay and axiom audit; only then should the
draft be presented as formal closure of T3's group-counting part.
