# Kernel-proved Heisenberg coordinates and orbit dimensions

## The matrix-to-orbit bridge is now concrete

The preceding orbit chapter proved the all-level dimension formulas and commutativity on paper. Its Lean symmetry theorem required a supplied family of symmetric spanning matrices. This extension constructs the actual Heisenberg basis, derives both literal generator actions, and turns matrix commutation into the corrected coefficient equations. At odd levels it identifies the concrete commutant with functions on the actual orbit quotient. There is no supplied rank, assumed basis, assumed conjugation identity or assumed spanning family in this result.

Thirty-five general theorems and six proof-carrying constructions are audited across two new Lean modules, for forty-one declarations. `PerfectPower/WeilMonomial.lean` contains the concrete character and matrix argument. `PerfectPower/MonomialOrbitSpace.lean` contains the general quotient, gauge and reflection transport. Both compile with Lean 4.20.0 and the pinned Mathlib revision. The focused audit admits only the standard axioms and rejects sorryAx and Lean.ofReduceBool.

For a finite commutative ring A, a characteristic-zero field K and a primitive additive character psi from A into K, define the Fourier matrix by psi(xy), the chirp by psi(x squared), and the clock-after-shift Heisenberg matrix by the entry psi(tx) when x=y+s and zero otherwise. This is exactly the convention of the preceding release, including the negative chirp conjugation phase. The assumptions allow cyclic odd, cyclic even and more general finite rings; the global gauge and quotient-dimension specialization additionally require an element h with 2h=1.

## Analysis and synthesis prove the basis

The coefficient of E_(s,t) is the Fourier transform of the shifted diagonal x mapped to C[x,x-s], divided by the cardinality of A. Conversely, the entry C[x,y] is reconstructed from the clock coefficients with shift s=x-y.

$$
a_C(s,t)=|A|^{-1}\sum_x C[x,x-s]\,\psi(-tx).
$$

$$
C[x,y]=\sum_t a_C(x-y,t)\,\psi(tx).
$$

`coeff_synth` and `synth_coeff` prove the two inverse identities by character orthogonality. In the first direction, the inner character sum is zero unless the two clock indices agree. In the second direction, it is zero unless the two row coordinates agree. Characteristic zero makes the cardinality scalar invertible. No cyclotomic rank elimination or floating-point test is involved.

These identities define `coordinates`, a linear equivalence from the full matrix space to coefficient functions on A squared. `Basis.ofEquivFun` then constructs the basis, and `basis_apply` proves that its vectors are the literal E_(s,t) matrices. `basis_repr` identifies their representation coefficients with the displayed analysis formula. Finally, `expansion` proves that every matrix is the sum of its coefficient-weighted Heisenberg vectors.

This is stronger than observing N squared independent operators at individual levels. It is one general construction and two inverse proofs, valid for every primitive character under the stated field hypotheses.

## Literal Fourier, chirp and transpose actions

The entry calculations give intertwining identities before any inverse is used. Multiplying the Fourier identity by its previously proved inverse gives literal conjugation. The chirp inverse is the same diagonal character evaluated at minus x squared; both inverse orders are proved directly. The synthesized coefficient action follows by distributing over the now-proved basis expansion and reindexing the finite sums.

$$
F E_{s,t}F^{-1}=\psi(st)E_{-t,s},\qquad
T E_{s,t}T^{-1}=\psi(-s^2)E_{s,t+2s}.
$$

$$
E_{s,t}^{\mathsf{T}}=\psi(st)E_{-s,t}.
$$

The phase -s squared is now established by the kernel for the actual matrix definitions. Its sign is not a convention inferred from a numerical experiment. `transpose_synth` likewise proves the coefficient action of ordinary transposition on an arbitrary synthesized matrix.

A two-sided inverse makes conjugation-fixedness equivalent to commutation. Combining this fact with the unique coefficient representation yields `commutant_iff`: a literal matrix C belongs to the simultaneous Fourier/chirp commutant precisely when both coefficient laws below hold.

$$
a_C(-t,s)=\psi(st)a_C(s,t).
$$

$$
a_C(s,t+2s)=\psi(-s^2)a_C(s,t).
$$

`commutantEquiv` packages this as a linear equivalence between the concrete matrix commutant and the monomial coefficient subspace. This part works at even levels too; it does not assume that all monomial orbits survive.

## The general orbit quotient theorem

Supply any family of permutations of an index type. Define the orbit relation as the equivalence closure of their edges, so it includes forward edges, reversed edges, concatenations and identity paths. A fixed coefficient function has equal values along every such path. `fixed_respects` proves this by induction on the equivalence closure.

`quotientEquiv` descends each fixed function to the orbit quotient and pulls quotient functions back to the index set. The two constructions are inverse and linear. When the index type is finite, the dimension is therefore exactly the cardinality of the quotient. This is a theorem about the quotient itself, not a presumed numerical orbit count.

$$
\dim_K\{c:c(\gamma w)=c(w)\}=\operatorname{card}(\Omega/\mathrm{orbits}).
$$

For a monomial action, a nonvanishing gauge g satisfying g(gamma w)=phase(gamma,w) times g(w) identifies plain fixed functions with phase-fixed functions by multiplication by g. Its inverse divides by g. Nonvanishing of the phase is derived from the gauge equation and nonvanishing of g. `gaugeEquiv` checks the two inverses and both linearity laws. `phase_finrank` consequently gives the orbit-cardinality dimension of any system with such a global gauge.

A phase-inconsistent system need not have a global gauge. The theorem does not silently count its dead orbits as surviving ones. The even-level support restriction must be proved before this construction can be applied to that surviving subspace.

## The concrete odd-level dimension theorem

For 2h=1, set g(s,t)=psi(-hst). Every character value is nonzero, and the previous gauge identities prove the required consistency for both literal matrix actions. Composing the concrete matrix coefficient equivalence with inverse gauging and quotient descent gives `oddOrbitEquiv`.

$$
\operatorname{Comm}_K(F,T)\simeq_K
((A^2/\langle S,U^2\rangle)\to K).
$$

This produces `odd_commutant_finrank`: the dimension of the actual matrix commutant equals the number of its actual rotation/even-shear orbits. `odd_level_finrank` specializes to every positive odd cyclic modulus and derives h from oddness, rather than requiring the caller to supply it.

The result does not yet identify that quotient cardinality with tau(N). The paper orbit classification establishes that mathematical identification; formalizing the elementary orbit arithmetic is the remaining task. Independently normalized roots and coefficient-field transport also retain their separate scope. The theorem fixes the primitive character and coefficient field explicitly.

## Reflection now needs no spanning premise

The earlier symmetry bridge assumed a spanning family of symmetric matrices. The new quotient equivalence discharges the spanning issue at odd levels. Suppose reflection (s,t) mapped to (-s,t) lies in the same rotation/even-shear orbit as (s,t). A gauged fixed function takes the same value at both points. Multiplying the gauge back in gives exactly the coefficient relation required by transposition.

`reflection_coeff` proves this transport for a general monomial system. `odd_commutant_symmetric` applies it to the literal character matrices and proves that every commutant matrix is symmetric. `odd_commutative_of_reflection` then applies the already proved algebra argument: C, D and CD are symmetric, and transposition reverses multiplication.

$$
CD=(CD)^{\mathsf{T}}=D^{\mathsf{T}}C^{\mathsf{T}}=DC.
$$

The only orbit hypothesis is explicit reflection connectivity. There is no assumed spanning family, no assumed dimension and no assumed commutativity. The paper content classification implies this connectivity. The kernel still needs that arithmetic statement. At even levels, the sign-clock obstruction and surviving even-index quotient must be formalized before the same argument can be used there.

## Validation and the next bounded implementation

Run `make check-weil-monomial`. It builds both modules and audits all forty-one declarations, including the inverse coordinate maps, literal basis, both generator actions, both chirp inverses, exact commutant membership equivalence, quotient and gauge equivalences, dimension laws and the concrete reflection-to-commutativity theorem. Every dependency is standard; there is no admitted declaration or native evaluation axiom.

The preceding 166-level exact phase/reflection census remains unchanged. It continues to supply concrete regression examples and agrees with all 63 finite cyclotomic dimension certificates. This release adds general kernel mathematics, rather than another numerical census. The arbitrary Python or JSON interpreter is not claimed to be formally refined, and no Mordell case is closed.

The highest-value next bounded push is odd prime-power orbit arithmetic. Prove that elementary shears preserve content and act transitively on primitive vectors over ZMod(p^a). Then build the quotient equivalence indexed by valuations zero through a, derive its cardinality a+1, and prove reflection connectivity as a consequence. This immediately plugs into `odd_level_finrank` and `odd_commutative_of_reflection`, closing concrete odd prime-power dimensions and commutativity in the kernel.

The even branch is separate: prove the half-period chirp power is the sign clock, its Fourier conjugate is the half-period shift, and both force odd-index coefficients to vanish. Identify the remaining coefficient subspace with the halved theta-action square, then formalize its valuation and parity orbit classes. The expected orbit count is two classes per nonzero valuation plus zero. The paper all-level formulas, complex multiplicity-free decomposition, explicit irreducible projectors and general root/field normalization retain their precisely stated scopes.
