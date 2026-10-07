# Exact Fourier/chirp commutants and the CRT bridge

The subsequent [kernel dimension extension](WEIL_DIMENSION_MONOGRAPH.md) completes the coefficient-expansion dimension proof and actual cyclic CRT-compatible-character instantiation in Lean. References below to the paper-only dimension assembly describe the preceding release. Independently chosen roots and coefficient-field normalization remain a separate transport task.

## The convention and the mathematical result

At level N, this repository uses the unnormalized Fourier matrix F[x,y]=zeta_N to the power xy and the diagonal chirp T[x,x]=zeta_N to the power x squared. The even-level chirp uses an Nth root, not a 2Nth root. Changing that convention can change the answer. Write c(N) for the dimension, over the cyclotomic field, of the matrices commuting with both F and T.

The general mathematical conclusion is multiplicativity at coprime levels. The proof consists of the CRT factorization, recovery of an odd local Fourier generator from chirps, separation of the two local matrix algebras, and the centralizer dimension identity. It requires neither a multiplicity-free decomposition nor a conjectured prime-power formula. The full argument below is a paper proof. Seventeen reusable algebraic declarations are proved in Lean, including the general Gauss identity and a typed generator-separation theorem. The final all-level cyclotomic CRT instantiation and centralizer dimension assembly have not been packaged as a single Lean theorem.

$$
c(ab)=c(a)c(b),\qquad \gcd(a,b)=1.
$$

## Why the two tensor products are insufficient

Use the scaled CRT coordinates x=bu+av modulo ab, with u modulo a and v modulo b. Coprimality makes this section a bijection. Expanding xy or x squared shows that all cross terms are multiples of ab. The two global matrices become tensor products of local matrices, with root twists b modulo a and a modulo b. The same twist acts on both the Fourier matrix and its chirp. A root twist is a Galois automorphism, so it preserves the dimension of the local simultaneous commutant.

There is a genuine missing step if one stops here. Two synchronized tensor-product generators can generate a smaller algebra than the tensor product of the two independently generated local algebras. Consequently their commutant can be larger. The following odd-level identity recovers the separate generators and removes that obstruction for this pair.

## The Gauss identity, including composite odd moduli

Let A be a finite commutative ring, let psi be a primitive additive character into a field of characteristic zero, and choose h with 2h=1 in A. Define R[x,x]=psi(hx squared), F[x,y]=psi(xy), and Fminus[x,y]=psi(-xy). Let g(h) be the sum of psi(hz squared) over z in A. Character orthogonality gives F Fminus=Fminus F=|A| I. Thus J=Fminus divided by |A| is a two-sided inverse of F.

Completing the square and translating z by x-y gives the exact matrix identity

$$
R(FRJ)R=\frac{g(h)}{|A|}F.
$$

The nonvanishing proof does not need the classical closed-form phase of a Gauss sum. Multiply g(h) by g(-h), and change variables from (z,w) to (z-w,z+w). This is a bijection because 2 has inverse h. The exponent becomes huv. For each nonzero u, primitivity makes the sum over v vanish; u=0 contributes |A|. Therefore

$$
g(h)g(-h)=|A|,\qquad g(h)\ne0.
$$

For an odd cyclic modulus, h can be taken as an integer exponent modulo N, so R is literally a power of T. All the identities remain valid after multiplying the exponent of the primitive root by any unit. This covers both CRT twists, including odd composite factors. The Lean file proves completion of the square, translation invariance, orthogonality, the Gauss product and nonvanishing, both Fourier inverse identities, normalized recovery, literal chirp powers, and existence of a half at every odd modulus.

## Separating the local algebras

Denote the twisted local generators by FA, FB, TA and TB. After CRT, F=FA tensor FB and T=TA tensor TB. Choose a nonnegative exponent e with e=1 modulo a and e=0 modulo b. Then T to the power e is TA tensor I. The opposite exponent gives I tensor TB. The Lean `project_power` lemma checks this using finite-order equations and explicit exponent witnesses.

At least one of a and b is odd; suppose b is odd. A power of I tensor TB gives I tensor RB. Conjugation by F gives I tensor (FB RB FB inverse). The Gauss identity recovers I tensor FB as a scalar multiple of a word in the global generators and their checked inverses. Multiplying its inverse into F recovers FA tensor I. Thus the global generated algebra contains all four separate generators. The converse containment is immediate from the two product formulas.

`SeparationData` records the two product identities, the two projected chirp powers, two-sided Fourier inverses and the scalar recovery word. `commutant_separates` proves, for every element C of an associative algebra, that commuting with the global pair is equivalent to commuting with all four separate generators. These data are explicit identities; the theorem does not assume the desired equality of commutants. The Gauss and projection theorems provide their mathematical construction.

## Why dimensions multiply

Work over a common characteristic-zero field containing both sets of roots. Expand an arbitrary operator on the tensor product as a sum of operators on the first factor times a basis of all operators on the second. Commutation with the first local algebra forces each first coefficient into its centralizer. Now expand in a basis of that centralizer. Commutation with the second local algebra forces every second coefficient into the second centralizer. This proves that the global centralizer is exactly the tensor product of the local centralizers. Linear independence of tensor products of bases gives the product of dimensions. Extending either cyclotomic field to the common field preserves ranks and dimensions.

The Lean `kronecker_commute` theorem proves the tensor-product sufficiency direction for actual finite matrices. The full coefficient-expansion and cyclotomic base-change dimension argument above remains a paper proof. This distinction separates the delivered general kernel theorems from the stronger assembled mathematical conclusion.

## Exact dimensions beyond the old level cap

The new finite-level method uses two independently checkable bounds. First, explicit integer matrices are substituted into the chirp equation and the Fourier commutator. Fourier entries are reduced as integer polynomials modulo the cyclotomic polynomial, with no numerical tolerance. A nonzero modular minor among flattened basis vectors certifies their independence over the rationals and hence over the cyclotomic field.

Second, the chirp forces C[i,j]=0 unless i squared equals j squared modulo N. On those remaining entries the Fourier commutator is a homogeneous linear system over the cyclotomic field. Choose a prime q equal to 1 modulo N and a primitive Nth root z in the prime field. Evaluation sends the integral cyclotomic ring into that field. A nonzero minor after evaluation cannot have been zero in the original cyclotomic ring. It therefore gives a lower bound on the equation rank, and an upper bound on the commutant dimension. If that upper bound equals the number of independent commuting matrices, the dimension is exact.

The packet stores the integer basis, q, z, original equation row coordinates and selected columns of a square rank minor. Replay checks root order and the cyclotomic equation, substitutes every basis matrix exactly, checks basis independence, reconstructs the selected original-equation minor, and computes its determinant using a separate dense algorithm. The producer selects its minor with sparse elimination. No conjectured dimension is used as a certificate premise. Resource exhaustion raises an error rather than returning a partial result.

## Constructing useful commuting matrices

Parity commutes with both generators. If N=d squared times m, an old-level matrix C lifts to the integer matrix whose xy entry is C[x/d modulo m,y/d modulo m] when d divides both coordinates, and zero otherwise. The underlying embedding U is supported on multiples of d and constant on the d fibres. Its identities are F_N U=d U F_m and T_N U=U T_m; the lifted matrix is U C U transpose. This supplies the successive old-level projectors and their parity partners.

At levels divisible by four, use the half-period shift S and the sign clock Z[x,x]=(-1) to the power x. Both commute with T, and Fourier conjugation exchanges them. Thus S+Z and SZ commute with F as well. Their parity products, together with lifted old-level matrices, provide the dyadic basis candidates. Coprime products use integer tensor bases transported through the scaled CRT section. Every candidate is independently checked before it can contribute to a certified dimension; the construction is not a general irreducibility theorem.

## Delivered census and arithmetic frontier

The persisted census contains complete exact dimension packets for every level from 2 through 64, together with all 42 unordered coprime pairs whose factors are at least two and whose product is at most 64. All packets replay successfully. In particular, c(16)=7, c(25)=3, c(27)=4, c(32)=9, c(49)=3 and c(64)=11. The odd-prime-power pattern a+1 and dyadic pattern 2a-1 fit the tested levels. The all-exponent formulas remain unproved here; multiplicativity does not settle their local representation theory.

The separate Mordell reconciliation joins the actual conditional census rows with generated unconditional descent theorem names and the unconditional curve-list registry. It finds 485 conditional census rows, 28 elementary-descent closures, no additional unconditional list closures among those rows, and 457 remaining cases. Of those, 323 have empty computed lists and 134 have known listed points. The latter need completeness arguments preserving those points. An empty computed list is not a proof of emptiness. The new ledger claims no newly solved curve.

The deep-gems chapter now attributes the quartic identity to Roger Frye and the quintic identity to Lander and Parkin, with primary publication links. This arithmetic and attribution work preserves the recently merged prime-division, certified genus-two-period and wall calculations.

## Reproduction and next bounded theorem

Run `make check-weil-commutant` with Lean 4.20.0 and the pinned Mathlib revision. It rebuilds the 63-level exact census, reconciles the Mordell frontier, runs the focused tests and audits every general Lean theorem. The public service operations are `certified_weil_commutant`, `verify_weil_commutant` and `weil_crt_commutant`. The last operation certifies both local dimensions and the entire product level independently for coprime products at most 64. These Python packets continue to report execution_verified=false; there is no claim that their arbitrary JSON interpreter is kernel-refined.

The next formal push is the coefficient-expansion centralizer dimension theorem, followed by a ZMod CRT matrix reindexing instantiation of `SeparationData`. Together with the delivered Gauss and projection results, that would assemble the complete all-level multiplicativity statement in Lean. The next representation-theoretic push is an all-exponent decomposition proving the prime-power dimensions. Neither step needs another floating-point SVD census.
