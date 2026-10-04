# Complete effective quartic solving, from theorem to compiler

## What changed for a user

PerfectPower now has a complete solver for a new class of quartic equations. It can recognize an expanded integer polynomial, derive a finite interval that contains every possible integer solution, enumerate the solutions using exact square roots, and emit a Lean command that independently checks the list and proves its completeness. The mathematical bound is proved inside Lean. No supplied height theorem, Sage integral-point list or Matveev premise is needed for this route.

The central family is y²=(Lx²+ax+b)²+cx+d, with integer coefficients, L≠0 and (c,d)≠(0,0). The push further handles every integer quartic with a nonzero integer-square leading coefficient for which the normalized remainder described below is nonzero. Completing the square may use rational coefficients; the second solver clears their denominators for the bound while retaining the original equation for enumeration. These are new supported solver families in the repository, not claims of priority for classical Runge mathematics.

## A concrete completed problem

The equation

    y²=x⁴+x³+x²+x+1

has exactly the six integer points (-1,-1),(-1,1),(0,-1),(0,1),(3,-11),(3,11). The complete point theorem is generated and checked in Lean. RepunitQuartic.inputs proves that an integer square occurs exactly at x=-1,0,3. RepunitQuartic.positive proves that among positive integers only x=3 works. In ordinary terms, 1+3+9+27+81=121=11², and no other positive integer substituted into this five-term geometric sum produces a square.

This example was outside the integer square-plus-constant route: its square completion has fractional coefficients and a nonconstant remainder. The compiler now recognizes it, returns COMPLETE_FINITE with the sole positive-input hit 3 and witnesses -11,11, and can emit a Lean-native proof command. Asking for a million inputs does not trigger a million-input search. Its complete coefficient-derived interval is [-103,103], and exactly 207 fibres suffice to settle the equation over all integers.

## The elementary global bound

For the integral quadratic-square family, set P=Lx²+ax+b and R=cx+d. If R≠0 and y²=P²+R, then (y-P)(y+P)=R. Every integer factor of a nonzero integer has absolute value at most that integer's absolute value. The existing square_bounds theorem consequently gives |P|≤|R|. The triangle inequality gives |R|≤|c||x|+|d|, while

    |L||x|²≤|P|+|a||x|+|b|.

Since nonzero integer L has |L|≥1, every solution on such a fibre satisfies

    |x|²≤(|a|+|c|)|x|+|b|+|d|.

An elementary integer inequality rules out |x|>|a|+|b|+|c|+|d|+1. The proof makes this exclusion explicit rather than appealing to an asymptotic approximation of a branch.

The exceptional fibre R=0 must be retained. If cx+d=0, the nonzero perturbation assumption forces c≠0, and |c||x|=|d| gives |x|≤|d|. It lies inside the same global interval. Here y can equal ±P; dropping this fibre would lose valid solutions, including zero-valued points. The bound therefore covers every solution without an unproved exception.

LinearPerturbation.coordinate_bound establishes

    |x|≤B, B=|a|+|b|+|c|+|d|+1.

The leading magnitude |L| does not enlarge this bound. An example with L=10^40 still needs only seven x fibres when a=b=0,c=d=1. Arbitrary-size integer arithmetic is retained; no floating-point square test is used.

## Exact fibres and native point lists

Instead of scanning a two-dimensional rectangle, the enumerator visits each x in [-B,B] and computes F(x). A verified square-root candidate routine tests only the positive and negative integer square roots, retaining zero once and rejecting negative or nonsquare values. LinearPerturbation.squareRoots_complete proves that these candidates recover every integer solution of y²=F(x). The implementation uses the existing proved Newton square-root routine, avoiding trial enumeration in the y coordinate.

LinearPerturbation.complete combines the global interval and exact fibres into an equivalence between the equation and membership in its computed finite point set. expanded connects the quadratic-square presentation to the ordinary ascending coefficient list

    [b²+d, 2ab+c, a²+2Lb, 2La, L²].

The native_linear_perturbation command proposes a literal point list and generates its complete theorem. The finite set equality is checked by decide +kernel. The elaborator is allowed to compute proposals, but a proposed list cannot bypass the kernel proof. Zero perturbations and zero leading coefficients are rejected, and a work limit prevents an oversized enumeration from being represented as a completed partial search.

## Removing the integral-completion restriction

For F(x)=L²x⁴+ux³+vx²+wx+z, define

    S=8L³, QL=8L⁴, A=4L²u, B=4L²v-u²,
    C=S²w-2AB, D=S²z-B².

Lean proves the polynomial identity

    S²F(x)=(QLx²+Ax+B)²+Cx+D.

The factor S clears the rational coefficients introduced by square completion. If L≠0 and C,D are not both zero, a solution of the original equation yields a solution of the proved integral perturbation family with ordinate Sy. Its x coordinate therefore obeys |x|≤|A|+|B|+|C|+|D|+1.

SquareLeadingQuartic.complete enumerates square roots of the original F(x) inside that interval. It does not enumerate every scaled ordinate and assume it can be divided by S to give an integer. This preserves integrality directly and avoids a spurious reconstruction step. The bound is coarse and may grow substantially after normalization; the compiler prefers the smaller integral-completion route whenever available.

The normalized zero-remainder case is excluded by the finite theorem's explicit hypothesis. Negative or nonsquare leading coefficients, higher-degree inputs and oversized normalized intervals retain the other compiler routes or their unresolved status. This is a complete supported family, not a general solver for every quartic or every finite-type polynomial.

## A checked catalogue, not a bounded guess

The push contains 420 equations y²=x⁴+cx+d, with c ranging from -10 to 10 excluding zero and d from -10 to 10. Every one is emitted as a native complete theorem and checked by the Lean kernel. The catalogue has 850 integer points across its separate equations; 132 equations have no integer points, and 288 have at least one. The total of 850 and the count of 132 empty sets are themselves kernel-checked census theorems.

The 850 total counts points separately for each equation; a coordinate pair appearing on two different equations is counted once in each equation's solution set. Computed descriptive metadata identifies 418 nonsingular quartics and two singular ones; the completeness proof applies to all 420 and does not require nonsingularity. The compiler finds positive-input points in 171 catalogue equations. The catalogue coefficient interval does not constrain the general theorem: the theorem accepts arbitrary integer coefficients subject to its stated hypotheses.

Additional native examples check a nonmonic quadratic square, a zero-perturbation fibre, odd cubic coefficients requiring fractional completion, a fractional quadratic completion, and leading coefficient four. False proposed point membership is rejected in the audit. The public CLI emitter is compiled separately, so validation covers both handwritten native commands and commands emitted by Python.

## Compiler and command-line use

The new route sits after the existing divisor solver and before the harder finite-type fallbacks. It first recognizes an integral quadratic square plus a linear perturbation. If that is unavailable, it tests for square leading coefficient and constructs the denominator-cleared normalization. A successful complete enumeration produces COMPLETE_FINITE, an exact positive-input hit table and the appropriate Lean theorem reference. Work exhaustion raises internally and leaves the other routes available; it never returns a truncated list as complete.

From the repository root, commands include

    PYTHONPATH=python python3 -m perfectpower solve --expr='n**4+n**3+n**2+n+1' --d=2 --N=1000000
    PYTHONPATH=python python3 -m perfectpower lean --coeff=1,1,1,1,1 --d=2 --name=repunit
    PYTHONPATH=python python3 -m perfectpower linear-perturbation --parameters=1,0,0,2,1

The first reports the complete positive-input answer. The second emits a self-contained Lean command that computes and proves the integer point list. The third gives the original quadratic-square presentation's complete integer points. Existing specialization machinery can consume COMPLETE_FINITE plans, replacing a repeated search with the literal proved-family answer table. Python execution remains marked unverified; theorem-backed mathematical completeness is distinct from a formal refinement proof of Python.

## Validation and practical limits

scripts/check_linear_perturbation.sh regenerates and compiles the 420-case catalogue, checks 428 axiom reports and runs the focused regression tests. scripts/check_square_leading.sh checks the broader normalization, concrete raw quartics, the integrated geometric-series theorem and a separately emitted CLI proof, validating ten additional reports. Only propext, Classical.choice and Quot.sound are permitted. These are targeted new-module checks, not a fresh rebuild of every historical large Lean module.

The regression tests compare 500 integral presentations and 100 raw quartics against independent wider interval enumerations, exercise recognizer round trips, preserve zero fibres and repeated zero roots, reject infinite or invalid inputs, check work-limit failures, and test complete positive-domain compiler outputs. The full package suite passes 428 tests with four skips. Such implementation tests do not replace the universal Lean bound and fibre proofs; they exercise the bridge from user input to those mathematical specifications.

This push advances completed arithmetic rather than adding another conditional interface. It proves a global bound, supplies a complete enumerator, automates instance proofs, closes a concrete geometric-series equation and checks a substantial catalogue of empty and nonempty equations. The remaining rank-two Matveev and general Mordell height premises are not discharged by it. The next mathematical extension is a similarly explicit solver for broader perturbation degrees or other branch configurations; the next performance improvement is a sharper normalized bound that preserves the current completeness guarantee.
