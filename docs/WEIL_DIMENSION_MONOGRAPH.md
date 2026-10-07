# Kernel-proved CRT commutant dimensions

## The dimension gap is closed

The previous release proved the Gauss recovery word and generator separation in Lean, but left the coefficient-expansion dimension argument as a paper proof. This extension implements that argument, connects it to ordinary matrix commutants, constructs the cyclic separation packet from primitive characters, and proves the actual CRT-character product law. Thirty new general declarations compile and pass the focused axiom audit. Together with the preceding seventeen declarations, the bridge has forty-seven audited general theorems.

The precise cyclic theorem works over one field K of characteristic zero containing the two primitive additive characters. Let a and b be positive coprime moduli, with b odd. Let psi_a and psi_b be primitive characters on the two cyclic rings, and form Psi on the cyclic ring of order ab by transporting their product through the standard ring CRT equivalence. Then

$$
\dim_K\operatorname{Comm}(F_{\Psi},T_{\Psi})=
\dim_K\operatorname{Comm}(F_{\psi_a},T_{\psi_a})\,
\dim_K\operatorname{Comm}(F_{\psi_b},T_{\psi_b}).
$$

This is `WeilTensorDimension.crt_character_finrank`, a general Lean theorem. It has no assumed local dimension, assumed matrix factorization, assumed equality of centralizers, numerical rank premise, or conjectured prime-power formula. For any coprime pair, at least one modulus is odd; the theorem is oriented with that factor second. Comparing independently chosen primitive roots and independently chosen cyclotomic coefficient fields is a separate field-transport statement. The delivered theorem fixes the common field and CRT-compatible characters explicitly, so that its meaning does not depend on an implicit root convention.

## A constructive coefficient space

For finite index sets I and J, choose subspaces U of K-valued functions on I and V of K-valued functions on J. Define S(U,V) to contain all rectangular matrices whose columns lie in U and whose rows lie in V. The first new module proves the exact dimension formula

$$
\dim_K S(U,V)=\dim_K U\,\dim_K V.
$$

Choose a basis b_t of U. Assemble a matrix from V-valued coefficient rows c_t by setting its ij entry to the sum of b_t(i)c_t(j). Every column is a linear combination of vectors in U; every row is a linear combination of vectors in V. Basis independence makes the assembly map injective: equality of the columns forces equality of all their basis coordinates.

Surjectivity is the mathematical point that the informal proof had left implicit. A coefficient functional on U extends to the ambient function space using a linear left inverse of the inclusion of U. Applied to the columns of a matrix, that extended functional produces a linear combination of the original rows. Since every original row lies in V, the resulting coefficient row lies in V. The basis reconstruction formula then assembles exactly the original matrix. This proves that the assembly map has range S(U,V), and gives a linear equivalence from a finite product of copies of V to S(U,V).

The proof covers zero subspaces and empty finite index sets without special mathematical premises. `finrank_separated` chooses a finite basis of U and uses the general finite-product dimension theorem. It neither presumes a tensor basis nor inserts its desired dimension as an input. The only nonconstructive choice is the ordinary vector-space extension of a linear map, reflected in the standard Lean axiom audit.

## From rectangular entries to matrix commutants

The second module defines `pairSpace F T` as the vector subspace of ordinary matrices commuting with F and T. It reindexes a square matrix on the product of two index sets into a rectangle whose row index is an entry of the first local matrix and whose column index is an entry of the second. The regrouping is a linear equivalence with an explicit inverse.

Four entrywise multiplication identities show what separate actions do. Multiplication by F tensor identity acts on every first-factor block by multiplication with F. Multiplication by identity tensor G acts on every second-factor block by multiplication with G. Consequently commuting with the two first-factor generators means that each rectangular column belongs to their local commutant. Commuting with the two second-factor generators means that each rectangular row belongs to their local commutant.

`regroupEquiv` identifies the full four-generator commutant with S(U,V). `fourSpace_finrank` therefore proves product dimensions for arbitrary finite local matrix pairs over any field. This result is broader than the cyclic Fourier application: it applies whenever two collections of local generators act separately on a product carrier.

Finally, `crt_finrank` combines the dimension theorem with the earlier `SeparationData` theorem. A separation packet records the global product formulas, projected chirp powers, checked inverses and recovery word. Those identities force the global two-generator commutant to equal the separate four-generator commutant. The new theorem then derives its dimension product automatically. There is no remaining coefficient-expansion or centralizer-dimension premise in that theorem.

## Constructing the cyclic packet

The third module supplies the separation packet rather than asking a caller to assume one. Natural-number CRT produces an exponent equal to one modulo a and zero modulo b, and another exponent with the opposite residues. A general Kronecker power identity and the literal chirp-power theorem turn these into the two separate chirps. This construction uses the actual moduli and does not depend on selected numerical examples.

An odd b has a half h with 2h=1. The earlier Gauss theorem proves nonvanishing and the recovery identity over the entire finite cyclic ring, including composite odd b. Its normalized reverse Fourier matrix is a checked two-sided inverse. The new `recovery_word` lifts that identity into the second tensor factor; the first Fourier factor cancels against its inverse. The resulting scalar word is exactly the recovery field required by the packet.

`tensor_finrank` now proves the dimension product for the global tensor Fourier/chirp pair from positive coprime moduli, primitive characters and an odd second factor. All powers, inverses and Gauss scalars are derived in the proof. The caller supplies no representation-theoretic decomposition or rank certificate.

## Actual cyclic CRT coordinates

The product character sends (x,y) to psi_a(x)psi_b(y). The cyclic character Psi is its pullback through Mathlib's ring equivalence between the cyclic ring of order ab and the product of the two local cyclic rings. The new code proves that the product character and its cyclic pullback are primitive when both local characters are primitive.

For the Fourier matrix, the ring equivalence preserves multiplication, so the phase of xy becomes the product of the two local Fourier phases. For the chirp, it preserves squares and the diagonal carrier. Reindexing both rows and columns therefore gives exactly the two tensor matrices. These are proved matrix equalities, not supplied factorization hypotheses.

An algebra equivalence transports an entire simultaneous commutant. `pairEquiv` constructs the linear equivalence explicitly and checks both directions of the commutation equations. Applying it to the CRT matrix reindexing preserves the dimension, and the tensor theorem supplies the final equality. This completes the common-field, compatible-character version of the multiplicativity bridge in the kernel.

## Relationship to the finite census

The preceding exact census remains available at every level from 2 through 64, including all forty-two unordered coprime pairs with product at most 64. Its integer commuting bases and independently replayed modular rank minors certify finite dimensions without floating-point tolerance. This extension changes no Python packet, numeric dimension, root convention or census receipt. Its contribution is the general dimension proof that previously existed only on paper.

The subsequent [orbit dimension and symmetry chapter](WEIL_LOCAL_DIMENSION_MONOGRAPH.md) supplies paper proofs of the all-exponent formulas and commutativity. Its orbit classification is not yet a Lean theorem. Multiplicativity remains independently proved under the compatible-character hypotheses above. The reconciled 457-case Mordell frontier likewise retains its existing arithmetic obligations. No rank-conditional curve is closed by a commutant theorem.

## Reproduce and extend

Run `make check-commutant-dimension` with Lean 4.20.0 and the pinned Mathlib dependencies. It builds all three new modules and checks every printed theorem dependency against the standard axioms. The audit includes the two dimension laws, explicit commutant equivalences, cyclic packet construction consequences, character primitivity and actual CRT matrix identities. No sorryAx or Lean.ofReduceBool is admitted.

The next useful formal bridge is root and field normalization: transport commutant dimensions under the relevant cyclotomic automorphisms and under extension to the common coefficient field, then specialize the compatible-character theorem to the repository's separately normalized primitive roots. The next formalization is the monomial fixed-space bridge and the local orbit classification proved on paper in the subsequent chapter. These are distinct tasks; the tensor coefficient-space and common-character product law are implemented and proved.
