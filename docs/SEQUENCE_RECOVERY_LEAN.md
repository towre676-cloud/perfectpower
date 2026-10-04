# Lean foundations for the recovered sequence machinery

The preceding release brought recurrence evaluation, modular reconstruction, formal operator replay and primary-module arithmetic into exact Python. This follow-up proves six reusable mathematical statements in Lean and connects the reconstruction output to its uniqueness theorem. It does not claim that a finite sequence match proves an OEIS definition, or that a Python execution is formally verified.

## Bounded rational reconstruction

BoundedReconstruction.unique proves the strict bound used by modular_reconstruction.reconstruct. Suppose |a|,|c|≤A, positive denominators b,d≤B, and both a-rb and c-rd are divisible by M. If M>2AB, then a/b=c/d over the rationals. This establishes uniqueness independently of whether a reconstruction algorithm succeeds. It does not assert existence, certify the extended-Euclidean implementation, or identify the mathematical meaning of a reconstructed coefficient.

The proof forms the cross-difference ad-cb. It is divisible by M, and its absolute value is at most |a|d+|c|b≤2AB. Any nonzero multiple of M has absolute value at least M, contradicting the strict bound. The cross-difference therefore vanishes, and nonzero denominators yield equality of fractions. No assumption that b or d is invertible modulo M is needed for this uniqueness implication. The Python implementation retains invertibility because its reconstruction API uses modular fractions.

The audit includes the boundary collision 1 and -1 modulo 2 with A=B=1. Both satisfy the modular condition and bounds but differ as rationals. Thus replacing M>2AB by M≥2AB would be false. reconstruct_system now names PerfectPower.BoundedReconstruction.unique alongside its existing execution_verified=false field. The theorem reference describes the mathematical uniqueness contract; it does not promote the returned result to a kernel-checked execution certificate.

## Universal coefficient annihilation

RecoveredOperators.hypergeometric_coefficient proves the identity behind the recovered operator

    Θ(Θ-1/4)(Θ-3/4) - t(Θ+1)^3.

For arbitrary rational n,a,previous, the coefficient recurrence (4n-3)(4n-1)a=16n² previous implies n(n-1/4)(n-3/4)a-n³ previous=0. The proof is a polynomial identity obtained by multiplying the recurrence by n/16. It does not use an analytic convergence assertion.

hypergeometric_all lifts this to a sequence a:ℕ→ℚ. If its recurrence is proved for every positive index, every formal coefficient residual vanishes, including the zero coefficient. This is stronger than checking 24 supplied coefficients, but it explicitly requires an all-index recurrence hypothesis. The new theorem is stated as a coefficient identity, rather than claiming that a complete formal-power-series differential-operator API has been implemented. Analytic continuation and zeta identities remain outside its conclusion.

## Wilson projectors

RecoveredOperators.wilson_projectors works in any commutative rational algebra with q³=-11q. It proves that e₀=1+q²/11 and e₁=-q²/11 sum to one, are individually idempotent, and are orthogonal. Multiplying the cubic relation by q gives q⁴=-11q²; that identity proves every projector equation. The rational algebra assumption supplies the inverse of eleven.

The theorem applies to the rational polynomial quotient used by the recovered projector code, when its cubic relation is supplied. It does not prove the generic Python CRT projector algorithm, pairwise-coprime factorization machinery, or reconstruction of the original Wilson matrix. Its commutative-algebra scope is explicit; a matrix-algebra extension needs either evaluation of these polynomial identities or a noncommutative formulation with central rational scalars.

## From recurrence certificates to infinite equality

RecurrenceRecovery.order_three_unique proves that two sequences over any semiring agree at every natural-number index when they satisfy the same order-three linear recurrence and agree at indices zero, one and two. Strong induction uses precisely those three preceding values. padovan_unique specializes this result to f(n+3)=f(n+1)+f(n), yielding equality of the complete functions.

This supplies a rigorous promotion route for a recovered Padovan candidate: prove the source sequence's recurrence and initial values, then apply the theorem. A finite-prefix match alone does not provide the recurrence premise. The current theorem concerns forward natural-number indices. The Python engine's signed evaluation, arbitrary-order recurrence arithmetic and invertible backward shift are not formalized by it.

## Validation and remaining work

scripts/check_sequence_recovery_lean.sh compiles the three new modules, checks six theorem axiom reports and runs the sequence-recovery Python tests. Only propext, Classical.choice and Quot.sound are permitted in the audit. The main PerfectPower module imports these new foundations. Checks are targeted; no fresh complete historical Lean build is claimed.

The next useful extensions are constructive bounded reconstruction certificates, arbitrary-order recurrence uniqueness, verified signed shift evaluation, generic polynomial CRT projector certificates, and a complete coefficient-level operator API. Primary-module subgroup censuses and their phase classification also remain executable Python rather than Lean results. These boundaries keep the recovered numerical and combinatorial evidence useful without silently enlarging its mathematical conclusions.
