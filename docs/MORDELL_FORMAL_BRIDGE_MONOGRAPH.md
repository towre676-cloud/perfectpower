# A formal bridge for Mordell completion

October 8, 2026. The 457-curve computational release remains complete. This continuation proves ten generic composition and enumeration theorems in Lean 4.20.0, audits their axioms and records the exact curve-specific proof inputs still missing. It does not finish the requested formal closure: zero of the 457 external completion packets have been promoted to unconditional Lean complete-basis or integral-list theorems by this continuation.

## What the kernel now proves

MordellCompletionBridge formalizes prime saturation in an additive point group. Strong induction on a positive multiple shows that saturation at all prime factors suffices to recover membership in a subgroup. One interface takes a proved numerical denominator bound. A second accepts a proved finite prime-support set, allowing exceptional reduction primes in addition to those selected by a height bound.

The bridge also proves that a genuinely finite quotient supplies a positive denominator at most the quotient's cardinality, using the additive order of each coset. With that global mathematical input and the required prime-saturation statements, the subgroup is the whole group. This proves the composition step, rather than treating a backend status bit as a theorem.

Exact additive homomorphisms transport divisibility to reduction groups. An obstruction in a reduced group excludes rational divisibility. A reduction-separation premise implies prime saturation. These theorems explicitly require the homomorphism and its compatibility with the rational group; a finite-field computation by itself does not construct that compatibility proof.

For integral enumeration, integralBox filters the full product of two integer intervals by the Mordell equation. Membership is proved equivalent to the coordinate inequalities and the equation. A proved global coordinate bound upgrades that finite enumeration to a complete integral-point set, and equality of the enumeration with a supplied finite list transfers the result to the list.

## Counterexamples guard the trust boundary

The audit proves that the subgroup 17 Z of Z is saturated at every prime at most 13 and is still proper. Consequently, the native prime cutoff cannot supply a global saturation bound. The required global prime support remains a separate input.

The audit also checks the equation y squared equals x cubed minus 2. The box with coordinate limits 2 and 4 is empty, while (3,5) is an actual integral point. The larger box with limits 3 and 5 contains exactly (3,-5) and (3,5). These kernel checks show why finite enumeration cannot establish its own global coordinate bound.

## What is still missing

Every frontier curve still needs a Lean proof connecting the external descent computation to an upper bound on the actual rational point-group rank. Matching native witnesses provide lower-bound evidence; they do not supply the upper-bound proof.

Every curve also needs a proved global saturation prime-support bound, including exceptional reduction primes. The eclib logs retain numerical bounds and the selected primes, but do not contain Lean proof terms establishing those bounds. The rational-to-finite-group connection for the 788 native exclusions is another explicit formal interface to instantiate.

Finally, every curve needs a proved global integral-coordinate bound or an equivalent completeness theorem for the elliptic-logarithm and LLL argument. The existing verbose enumeration logs record the computation, not a checked analytic inequality chain or a Lean proof of the global bound. The new finite-enumeration theorem supplies the final step once such a bound is proved.

No new axioms, admissions or externally evaluated proof shortcuts are introduced. The existing computational frontier remains closed, while the new formal ledger explicitly leaves all curve-specific global inputs unproved. Importing a statement as a hypothesis would preserve conditional correctness but would not satisfy the requested unconditional formal closure.

## Import investigation

The pinned Mathlib version in this repository contains elliptic-curve group-law machinery but no implementation of this completion pipeline. Michael Stoll's EllipticCurves project, inspected at commit 3bfe12446d7b2f5ac5c4ca138c932620fe24331c, contains Mordell-Weil and explicit 2-descent developments. Its current toolchain is Lean 4.35.0-rc3, while this repository uses 4.20.0. The inspected rank example concerns y squared equals x cubed minus x plus 1. It does not instantiate the 457 completion receipts. No theorem from that project was imported in this continuation.

An import effort would require a deliberate toolchain migration or compatible backport, followed by the per-curve algebraic-number-theory and local descent proofs. It would still leave the specific global saturation and elliptic-logarithm enumeration obligations to discharge. General finite generation is not a certificate for a particular rank, basis or integral list.

## Verification and reproduction

Run make check-mordell-completion-bridge. The script compiles the new module, checks the six concrete audit examples and prints the axioms of ten declarations. It accepts only propext, Classical.choice and Quot.sound, and rejects failed builds, missing declarations, admissions and unexpected axioms. The resulting status receipt binds the audited sources and logs by SHA-256 and lists the unresolved inputs for every curve.

Four focused Python regressions check the actual audit and source identities, preserve the unproved curve flags, and reject unsafe or incomplete axiom reports. The new module is imported from the library root. Verification uses the standard lake env lean compiler path; a separate lake build attempt encountered a ProofWidgets frontend-cache issue, which is unrelated to the kernel checks and is not reported as a successful whole-library build.

The computational receipts and all 457 lists are preserved unchanged. The new result is a verified formal composition layer with an honest obstruction ledger. Completing the requested task still requires the global mathematical proofs above.
