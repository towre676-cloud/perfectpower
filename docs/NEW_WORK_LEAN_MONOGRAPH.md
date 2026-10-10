# Lean closure of the recovered structural work

PerfectPower 0.9.1 carries the new PSG, SOE and structural mathematics through a separate Lean compilation and exact axiom audit. The release repairs the twenty PSG proof sources that arrived without a recorded compiler run and adds formal results for partial-state semantics, adaptive diagnosis, rational inequality certificates, structural exponent coordinates and a nonlinear chart. There are 384 audited declarations. The most substantial finite atlas consists of 324 all-future state-quotient theorems, one for each retained two-state, two-action, binary-observation partial deterministic model.

The guarantee attaches to the compiled statements. A certificate generator supplies coefficients, tables and witnesses; Lean checks the resulting propositions. The Python generators, JSON decoder, discovery routines and public console execution do not thereby become formally refined programs. This distinction is especially consequential for the elliptic rank work: the classical two-isogeny descent identity remains an explicit mathematical premise, rather than a theorem about the actual rational elliptic point group established by this release.

## Recovered PSG algebra

Write a source equation as

\[
 P(t)=A+tB+(t^2-D)C.
\]

The generic algebra module proves the identity

\[
 A^2-DB^2=(A-tB)(A+tB+(t^2-D)C)
 +(B^2-(A-tB)C)(t^2-D).
\]

Consequently, the original source condition together with the auxiliary equation implies the norm equation. This is a polynomial identity over a commutative ring, so no numerical root selection is involved. The generated recovered source is checked as a literal polynomial, and its separately emitted norm polynomial is proved equal to the norm expression. The final source-soundness theorem composes those two identities with the generic implication.

On the regular stratum B is nonzero. The only possible rational auxiliary coordinate is t=-A/B. Lean proves both its uniqueness and its reconstruction: the norm condition implies t squared equals D, and substitution into the original source gives zero. The new closure module packages this as a bidirectional existential statement. The nonzero-B hypothesis is retained. It cannot be removed by cancellation without losing the exceptional stratum, where the auxiliary equation can have no, one or two rational solutions.

Six literal Darboux cofactor identities are also checked. The recovered numerator, denominator, factors and cofactors are compared by exact ring normalization. This establishes the stated polynomial directional identities. It does not assert global existence of an analytic differential flow or safe division through a vanishing denominator. The existing Python finite-jet machinery continues to report finite coefficient conclusions, rather than infinite convergence.

Compilation exposed two practical defects in the incoming draft. An unnecessary tactic followed a tactic that had already solved the reconstruction goal. The large norm expression also exceeded the default recursion depth during elaboration. Both are repaired in the sources, and the generator retains the options needed to regenerate compilable output. Imports name the required Mathlib modules explicitly.

## Future equivalence for partial machines

A supplied machine has states, actions, an observation function and a transition returning either a successor state or none. None denotes a disabled action. A word runs by repeated option binding. Its behavior is the final observation if execution succeeds, or none if it fails. Considering every finite word also considers every prefix, so observations along a trace and disabled actions remain distinguishable.

A quotient projection q is accepted only when observations commute with q and transitions satisfy

\[
 \operatorname{map}(q,\operatorname{step}(s,a))
 =\operatorname{target}(q(s),a).
\]

Lean proves by induction on words that this identity transports arbitrary executions. Observation transport follows. States with the same quotient coordinate therefore have identical behavior for every finite action word. There is no maximum word length in this theorem.

Soundness alone does not establish that the quotient is coarsest. The second ingredient is a distinguishing word for every source pair whose quotient coordinates differ. Lean checks that the word produces different behavior. Combining the two ingredients proves

\[
 s\sim t\quad\Longleftrightarrow\quad q(s)=q(t),
\]

where the left side quantifies over all finite action words. This also gives a generic witness theorem: one checked distinguishing word refutes equivalence.

The retained atlas exhausts the 324 models: four binary observation assignments and 81 partial transition tables. Each model has its own source observations, partial transition function, quotient projection, quotient observations and target transition table. Finite obligations are proved with ordinary decide. Each instance then applies the generic all-word theorem. The original Python development compared a bounded set of words; the new theorems strengthen the retained instances to an unbounded semantic statement. They do not prove the Python partition-refinement or shortest-word discovery algorithms correct for every possible input.

## Adaptive diagnosis has a genuine optimality proof

The retained example begins with four states having the same current observation. Three unit-cost resettable probes have binary outcomes. Probe a partitions the states into two pairs. Probe b distinguishes the first pair, and probe c distinguishes the second. The adaptive policy first runs a and then chooses the appropriate second probe.

The Lean model includes a recursive policy type, execution semantics, a maximum-path measurement cost and a correctness predicate. The displayed policy is proved correct and its cost is two. Every first probe has a collision. The lower-bound proof considers an arbitrary correct policy: a policy with cost at most one has only leaf children and cannot resolve that collision. Hence every correct policy costs at least two. This is an optimality theorem over all finite binary policy trees in this probe model, rather than a check of the displayed tree alone.

For fixed schedules, all three probes identify the four states. Every ordered pair of probes has a collision, including repeated probes. Thus two fixed measurements cannot suffice, and three do. The already distinguishable states in the original six-state example require no probe because their current observations are different. The formal ambiguity problem is the four-state initial observation class.

This theorem does not establish arbitrary Python Bellman search correctness or handle non-resettable measurements, noisy observations or unknown machines. It establishes the exact adaptive advantage claimed for the retained example. A separate generic cost-contract theorem records the usual attainability-and-lower-bound criterion without confusing supplied premises with a proved discovery algorithm.

## Rational inequality certificates

The generic structural module proves nonnegativity of finite sums of weighted rational squares with nonnegative weights. A Gram acceptance theorem combines this with a supplied, checked identity. Zero weights are admitted; singular positive semidefinite matrices are not discarded. The domain theorem adds products of nonnegative constraints and arbitrary multipliers of equations that vanish on the stated domain. It proves a lower bound while retaining every inequality and equality hypothesis.

The literal matrix instances are tied to the saved rational coefficients. They include two Lyapunov metrics, a singular Toeplitz example and a Toeplitz example extremely close to a singular frontier. Each quadratic form is proved equal to its weighted-square LDL expression, and nonnegativity follows. For the two Lyapunov examples, Lean also proves the exact quadratic dissipation identity for the retained operator and decay parameter. The theorem is the algebraic identity; a continuous-time solution theorem or exponential comparison theorem is not added here.

The sum of the six retained PSG factor squares has the rational lower bound 1/5. Lean checks the completed-square identity giving that bound. On the declared v=0 slice, the energy is

\[
 89(a-44/89)^2+22/89.
\]

The slice bound and its attainment at a=44/89 are both proved, with p unrestricted. These statements are about the declared polynomial over rational coordinates. They do not identify it as a physical energy, and this release does not advertise a new formal theorem over all real coordinates.

## Structural species and coordinate transport

Occupations encode a nonincreasing exponent pattern by adjacent differences. Reconstruction takes suffix sums. Lean proves that applying the difference map to a reconstructed occupation list returns the original list. This is an exact finite coordinate identity. The theorem does not justify erasing trailing zeros or silently sorting an arbitrary list.

A monomial theorem proves that raising a finite product to degree d agrees with multiplying every exponent by d. The bounded power-exponent theorem establishes

\[
 dj\le e\quad\Longleftrightarrow\quad j<\lfloor e/d\rfloor+1
\]

for positive d. This is the local counting rule used for power divisors. The complete species dynamic-programming traversal, its least-representative ordering and its rank/select implementation remain tested Python code.

The nonlinear SOE chart x'=x+y squared, y'=y has a global polynomial inverse. The closure module checks both inverse compositions and determinant one. These literal rational chart results complement the generic PSG affine norm-expansion theorem. They do not certify every polynomial chart accepted by the Python interpreter.

## Elliptic descent boundary

The structural additions also retain complete candidate squareclasses and finite exclusion calculations for rational two-torsion models. Lean now checks the rational quartic-cover-to-curve substitution with its nonzero denominator hypothesis. It proves the negative quartic exclusion when the leading and final coefficients are negative and the middle coefficient is nonpositive. This is one supported real-place exclusion branch.

The numerical rank-bound combination is proved under an explicit descent-dimension identity and bounds on the two image dimensions. The classical identity, squareclass completeness for actual rational points, prime-power projective-chart exhaustiveness and the complete retained rank-zero census are not promoted to unconditional Lean group theorems. The 99 rank-zero models remain exact Python calculations supported by classical descent reasoning. Formalizing those group-theoretic and arithmetic bridges is the next independent mathematical task; a renamed assumption would not close it.

## Reproduction and retained evidence

Run make new-work-kernel in an environment with Lean and Mathlib 4.20.0. The gate regenerates the SOE and structural instances from the retained receipts and rejects any byte difference. It compiles every module in dependency order, requires silent successful compiler output and checks an audit containing exactly the declarations found in the source modules. Every declaration must occur in order and may depend only on the standard axioms propext, Classical.choice and Quot.sound. Custom axioms, sorryAx, native reduction axioms and unparsed output fail the audit.

The verification receipt binds the compiled source files, generators, input receipts and audit script by SHA-256. Each successful compile has a retained log. The Python PSG, SOE and structural suites supply separate execution evidence. An installed wheel is checked outside the source checkout. This focused release does not claim a rerun of the entire historical release-verification suite. The complete archive contains the incoming work, formal closure, receipts, documentation and installed package, with independent ZIP parts that should all be extracted into the same directory.

## General finite-machine proof packets

The source-bound compiler now supports supplied finite deterministic partial machines with pair-specific quotient experiments. The public `soe-states --kernel-check` option requires rebuilt Lean acceptance. See [the general compiler monograph](SOE_GENERIC_LEAN_MONOGRAPH.md) for its contract, reproducibility commands and explicit limits. This verifies individual results; the Python partition-refinement implementation remains tested rather than formally verified.
