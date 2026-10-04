# Recovered arithmetic becomes Lean mathematics

This push formalizes the reusable mathematical core of the two preceding Python releases, arithmetic information planning and covering/lattice arithmetic. It adds three Lean modules with eight audited theorems. The result is a connected route from integer matrix images through periodic signed unit actions, together with rational covering maps and a general characterization of target recovery. These are universal mathematical proofs, not claims that Python execution has become formally verified.

## Integral pullbacks

Let A be any finite square integer matrix with nonzero determinant, and let b be an integer vector. IntegralPullback.image_iff proves

    (exists integer x, Ax=b) iff (for every i, det(A) divides (adj(A)b)_i).

The proof uses both adjugate identities. Necessity follows from adj(A)Ax=det(A)x. For sufficiency, divisibility supplies integer coordinates x with adj(A)b=det(A)x. Multiplying by A yields det(A)Ax=det(A)b; cancellation of the nonzero integer determinant gives Ax=b. Neither positivity nor determinant one is required. Thus the statement also applies to embeddings of nontrivial additive index, where rational inversion alone would lose the integral image.

IntegralPullback.pullback proves that the explicit vector with coordinates (adj(A)b)_i / det(A), using integer division, maps to b whenever these divisibilities hold. This upgrades the result from a membership test to a constructive reconstruction theorem. There is no claim here of a Smith algorithm for rectangular matrices, unimodular Smith transformation matrices, or a proof of every Python determinantal-divisor routine.

IntegralPullback.orbit_residue_iff combines image membership with the earlier RankTwoSieve theorem. For group elements U,V with certified positive periods M,N, and any integer-vector readout of their product, membership in the integral image of A is equivalent to membership of the signed exponent residues in a finite allowed set. The group and readout are generic: a modular action, seed and coordinate receiver can be supplied without making the seed invertible. The actual periodicity hypotheses must hold for the group being used. Infinite integer unit groups do not acquire finite periods merely because their modular images have periods. This theorem does not establish a global exponent bound.

## Rational covering and isogeny maps

CoveringMaps.covering proves that, for nonzero rational d,v, a point satisfying

    w²=du⁴+Au²v²+(B/d)v⁴

maps under x=du²/v² and y=duw/v³ to

    y²=x³+Ax²+Bx.

The algebraic theorem is slightly more general than the Python integer constructor: it works with rational coefficients and does not require d to divide an integer B. The integer constructor's divisibility requirement ensures that its quartic coefficients are integral; it is not necessary for the rational identity itself.

CoveringMaps.isogeny proves that a source point on this elliptic model with x≠0 maps under

    X=x+A+B/x, Y=y(1-B/x²)

to the model with coefficients -2A and A²-4B. Both proofs retain the excluded denominators explicitly. Nonsingularity is not needed to establish these algebraic implications; describing nonsingular models as elliptic curves and completing the maps across exceptional charts requires the appropriate additional geometry. The concrete source (-1,1;1,1) and target (2,-3;1,0) are checked in the audit.

These theorems establish forward maps. They do not classify covering square classes, prove Selmer membership, identify all rational points, or formalize the Fisher example's Cassels–Tate pairing and global obstruction. Those remain separate substantial obligations.

## Target recovery and ambiguity

For arbitrary state, observation and target types, TargetDecoder.decoder_iff proves that a total decoder exists exactly when the target is constant on every observation fibre. The target type is assumed nonempty to define the decoder on observation values that no state realizes. On realized values, the theorem chooses a representative and proves that its target is independent of that choice. This decoder-existence proof uses classical choice; it is a mathematical characterization, not an executable decoder algorithm.

TargetDecoder.separation_iff proves the equivalent statement that every pair with different targets has different observations. TargetDecoder.collision_no_decoder proves that two states with equal observations and different targets refute every possible decoder. The audit applies this to parity observations on natural numbers: no function of parity can recover the original natural number for all inputs.

An observation bundle can be represented by a function into a tuple or function type. The theorem consequently applies to selected arithmetic readouts without demanding recovery of the complete source state. Finite planning still needs certificates for the selected observations, finite domain and declared costs. This push does not prove the Python planner's weighted optimum, an exhaustive set-cover implementation, or any extension of a bounded decoder to all integers. It supplies the exact logical criterion those future certificates must establish.

## Integration, verification and next steps

The three modules are imported by PerfectPower.lean. scripts/check_recovered_bridges.sh compiles them individually, checks the audit examples and validates eight axiom reports against propext, Classical.choice and Quot.sound. This is a targeted check; it does not claim a fresh build of every historical heavy module. Python regression tests cover the preceding releases' covering, lattice, information and signed-sieve interfaces, but are independent of the Lean proof of their specifications.

The next natural connection is to instantiate integral pullbacks for the 23 existing order maps and discharge each adjugate congruence certificate. A further modular instantiation can use the actual certified unit matrices and combine the resulting readout predicates. Covering maps can then be paired with complete source point sets and explicit exceptional-chart handling. Target recovery can acquire finite certificates for sufficiency and cost optimality. The central global obstacles—Matveev lower bounds, effective Mordell heights and complete pairing coverage—remain visible and unchanged by these elementary bridges.
