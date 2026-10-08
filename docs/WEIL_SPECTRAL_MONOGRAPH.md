# Explicit rational blocks of the Fourier/chirp representation

## From the latest push to a complete spectral algebra

The preceding shared-main push establishes the all-level orbit dimension formula and proves commutativity on paper, with a conditional transpose bridge in Lean. Its explicit next target is primitive idempotents, their dimensions and characters. This chapter supplies those objects by recursion in the original matrix coordinates. It uses the same convention throughout: F[x,y] is zeta_N raised to xy, and T[x,x] is zeta_N raised to x squared, including the N-th-root chirp at even levels. Changing that even-level convention changes the problem.

Let A_N be the commutant over Q(zeta_N). Write N = 2^a m, with m odd. The orbit theorem gives dimension tau(N) for odd N and (2a-1)tau(m) when a is positive. Together with the construction below, it implies that A_N is a split commutative algebra with a basis of rational symmetric primitive idempotents. Over the complex numbers their images are the pairwise non-isomorphic irreducible constituents of the unitary Fourier/chirp representation.

$$
A_N \cong \mathbb{Q}(\zeta_N)^{c(N)},\qquad I=\sum_{j=1}^{c(N)}P_j,\qquad P_iP_j=\delta_{ij}P_i.
$$

The projectors have rational entries even though the Fourier and chirp matrices live over a cyclotomic field. This does not assert that the irreducible representations themselves admit rational matrices. The Python implementation returns compressed original-coordinate formulas through level 1,000,000, and exact dense algebra packets through level 64. The all-level completeness and primitivity statement is a paper theorem using the preceding orbit classification; it is not an all-level Lean theorem.

## The old-level isometry

Suppose N = d squared times M. Embed the M-dimensional carrier by setting (U_d v)(x) = v((x/d) mod M) divided by the square root of d when d divides x, and zero otherwise. Each residue class modulo M occurs d times among the supported x, so U_d is an isometry. Direct substitution gives T_N U_d = U_d T_M: for x = d(u + kM), the phase x squared divided by N differs from u squared divided by M by an integer.

For the Fourier operator, sum over the d preimages of each local coordinate. The geometric sum vanishes unless d divides the output coordinate. On that support it contributes d, giving F_N U_d = d U_d F_M for the unnormalized matrices. Since N = d squared times M, the normalized Fourier operators intertwine exactly. Their inverses intertwine too, so the image and its orthogonal complement are invariant. Consequently U_d Q U_d transpose commutes with the original F_N and T_N whenever Q commutes at level M.

Its entries are Q((x/d) mod M, (y/d) mod M)/d when d divides both x and y, and zero otherwise. Thus the square root disappears from every projector. The old identity E_d has rank M. Parity R sends x to -x, commutes with both source operators, and intertwines under U_d. These facts also establish that parity commutes with the embedded projectors.

## Every odd prime power

At level one use the identity of rank one. At level p, for p odd, the projectors (I+R)/2 and (I-R)/2 have ranks (p+1)/2 and (p-1)/2. At level p raised to a, for a at least two, embed every projector from level p raised to a-2 with d = p. Their sum is E_p. On the complementary space put Q = I-E_p and take Q(I+R)/2 and Q(I-R)/2.

Both new projectors have rank (p^a-p^(a-2))/2. Indeed the trace of R on an odd carrier is one, and its trace on the embedded odd carrier is also one. Hence the trace of QR is zero, while Q has the stated dimension. They are nonzero, orthogonal and complementary to all the old projectors. The count increases by two every two exponents, giving a+1 blocks.

$$
P_{a,j}^{\mathrm{old}}=U_pP_{a-2,j}U_p^t,\qquad P_{a,\pm}^{\mathrm{new}}=\frac{(I-E_p)(I\pm R)}{2}.
$$

All factors in these products commute, so idempotence and orthogonality follow by multiplication. For even a the recursion terminates in the rank-one level-one carrier. For odd a it terminates in the two parity blocks of level p. For example level 243 has ranks 2, 1, 12, 12, 108, 108; level 729 has ranks 1, 4, 4, 36, 36, 324, 324.

## Every dyadic level, with the level-four exception

Level two has only the identity projector, of rank two. For N divisible by four let A shift by N/2 and let B multiply the x-coordinate by (-1)^x. Both are involutions. They commute because (-1)^(N/2) is one. Fourier swaps A and B, while chirp commutes with each: the shift changes x squared by Nx+N squared/4, a multiple of N.

Use three Fourier-stable projectors: E_++ = (I+A+B+AB)/4, E_-- = (I-A-B+AB)/4, and E_mix = (I-AB)/2. These are pairwise orthogonal and sum to I. The first is exactly the old-level projector E_2, as can be checked from its entries. Embed all the level N/4 primitive projectors in it. Split each of E_-- and E_mix by parity using E(I+R)/2 and E(I-R)/2. Parity commutes with A and B, so these are still orthogonal source-commuting projectors.

For N at least eight, trace R = 2, trace AR = 2, trace BR = 2 and trace ABR = 2. These follow by solving respectively 2x = 0 or 2x = N/2 modulo N and evaluating the clock signs at the two solutions. Therefore trace RE_-- = trace RE_mix = 0. The E_-- parity blocks each have rank N/8, and the E_mix parity blocks each have rank N/4. The total count increases by four when the exponent increases by two.

At N = 4 those signs are different: trace BR = 2 and trace ABR = -2. E_-- has only a negative parity block, of rank one; E_mix has only a positive parity block, of rank two. Together with the old rank-one block this gives ranks 1, 1, 2. Retaining the vanished blocks would falsely produce five constituents. The implementation omits precisely these two zero projectors. With the bases at N = 1, 2 and 4, the recursion yields exactly 2a-1 positive-rank blocks for every a at least one.

| Level | Number of blocks | Ranks, in increasing order |
| --- | --- | --- |
| 4 | 3 | 1, 1, 2 |
| 8 | 5 | 1, 1, 2, 2, 2 |
| 16 | 7 | 1, 1, 2, 2, 2, 4, 4 |
| 32 | 9 | 1, 1, 2, 2, 2, 4, 4, 8, 8 |
| 64 | 11 | 1, 1, 2, 2, 2, 4, 4, 8, 8, 16, 16 |

## CRT in the actual global coordinates

Let q_i be the pairwise coprime prime-power factors of N. Use the section x = sum_i (N/q_i)u_i modulo N, so u_i = (N/q_i)^(-1)x modulo q_i. In these coordinates the Fourier and chirp phases split into local phases twisted by the units N/q_i. The recursive rational projectors commute with every such unit twist: the embedding identities remain valid, parity still commutes, and the dyadic signs are unchanged because the twisting unit is odd. Equivalently, apply the Galois automorphism sending each local primitive root to its unit power: every rational projector is fixed, so its commutation identities survive the twist.

Take the tensor products of the local primitive projectors and transport them by this section. Explicitly the global (x,y) entry is the product of local projector entries at u_i(x), u_i(y). Their ranks multiply, they sum to the global identity and remain pairwise orthogonal. Their number is the product of the local counts, exactly c(N). This supplies a compressed construction without enumerating an N squared carrier. At level 1,000,000 = 2^6 times 5^6, it yields 11 times 7 = 77 positive-rank blocks summing to dimension 1,000,000.

Each constructed block is nonzero. Orthogonal nonzero projectors are linearly independent, so their c(N)-dimensional span exhausts A_N by the orbit dimension theorem. Each is primitive: any further nontrivial splitting in A_N would increase that dimension. Every commuting operator is therefore scalar on each block. This proves both completeness and the split-algebra assertion, rather than inferring them from numerical eigenvalues.

## Multiplication, characters and exact operator calculus

At dense levels 2 through 64, use the preceding release's integer commutant basis B_i. Products are expanded in that basis by the inverse rational Gram matrix, and reconstructed entry by entry. Express each recursive P_j in the same basis and calculate its character chi_j(B_i) = trace(B_i P_j)/rank(P_j). Check B_i P_j = chi_j(B_i)P_j exactly. The packet contains the complete multiplication table, the character table and all projector coordinates.

For C = sum_i c_i B_i, its scalar on block j is lambda_j = sum_i c_i chi_j(B_i). The trace is sum_j rank(P_j)lambda_j, and the determinant is the product of lambda_j raised to rank(P_j). C is invertible exactly when every lambda_j is nonzero; then its inverse is sum_j P_j/lambda_j. These formulas also handle singular operators: the zero eigenvalues identify their exact kernel blocks. Separator coefficients t raised to i are chosen by bounded search for distinct block eigenvalues; this identifies the blocks but is not needed for their construction.

The API operations are `weil_projector_plan`, `weil_spectral` and `weil_operator_spectrum`. A plan gives ranks and recursive entry formulas. A dense packet optionally includes literal matrices and the existing dimension certificate. An operator packet accepts one exact rational coefficient per basis element. Budget failures return no partial algebra. Packet outputs are independent copies, so changing a returned projector cannot alter the cached algebra.

## What Lean checks and what remains paper mathematics

`PerfectPower/WeilSpectral.lean` proves eleven general declarations: closure of centralizers under addition, scalar multiplication, multiplication and finite sums; the transpose-product commutativity criterion; symmetry of a reflecting orbit kernel; polynomial-factor transport of commutators to roots; spectral resolution; and complementary-projector identities. The symmetry theorem explicitly requires that all centralizing matrices are symmetric, as does the preceding session's spanning bridge. It does not formalize the missing all-level orbit classification.

The native sources at levels 3, 4, 8 and 9 contain literal rational matrices and the literal polynomial Fourier and chirp matrices. For each projector the Fourier commutator is exhibited as Phi_N times a literal polynomial matrix, and the chirp commutator is zero. Lean checks the factor identity entry by entry and transports it through any polynomial ring homomorphism annihilating Phi_N. Thus it checks commutation at an actual cyclotomic root, rather than checking only an unrelated abstract multiplication table. Rational idempotence, pairwise orthogonality, symmetry, the partition of identity and the trace values are checked in the kernel as finite identities. Trace equals rank for these characteristic-zero idempotents: the decomposition into image and kernel puts each projector in the form diag(I_r,0). That identification is a paper argument here; the native rank-labelled theorem states the literal trace.

There are 76 native declarations and 11 generic declarations in this release. The generated sources are proof-carrying witnesses; their Python producer is not verified. All audit results admit only the standard axioms propext, Classical.choice and Quot.sound, with no sorry axiom or unchecked reduction oracle. The packet itself continues to say kernel_checked=false unless a consumer separately compiles its generated source; the audit receipt records precisely the checked source hashes.

The exact dense census covers 63 levels and 260 projectors. It checks source commutation by cyclotomic polynomial reduction after clearing denominators, compares dimensions against the preceding complete certified census, and reconstructs every product and character identity over the rationals. Independent dense tests compare traces, determinants, eigenspaces and inverses at worked levels. Compressed tests cover levels 1 through 499 and larger prime powers, including the million-level example. Reproduce with `make check-weil-spectral` and `make weil-spectral-receipts`.

The next mathematical formalization is now concrete: prove the old-level isometry and literal Fourier/chirp intertwining in Lean; formalize the dyadic clock/shift trace calculation; and combine these recursions with a kernel proof of the local orbit upper bounds. The existing independent-root field normalization obligation remains separate. These additions close the explicit paper spectral decomposition and bounded exact execution target; they do not alter the Mordell frontier, global height bounds or singular-endpoint period obligations.
