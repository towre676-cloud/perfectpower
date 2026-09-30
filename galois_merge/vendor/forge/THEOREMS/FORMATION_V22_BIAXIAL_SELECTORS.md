# Formation v22 biaxial selector import

Formation Polarization v22 studies the first noncyclic zero-gap selector problem for
\[
M(L_3(4))_{(2)}\cong C_4^2.
\]

The named inclusions
\[
L_3(4)<M_{22},\qquad L_3(4)<U_4(3)
\]
both induce primitive surjections \(C_4^2\twoheadrightarrow C_4\), but the pullback covers lie in inequivalent selector orbits:
\[
4_1.L_3(4)\quad\text{for }M_{22},\qquad
4_2.L_3(4)\quad\text{for }U_4(3).
\]

For either selector \(f\), the v17 integral signature is its graph
\[
\Lambda_f=\{(f(h),-h):h\in C_4^2\}\le C_4\oplus C_4^2,
\]
of order 16. With \(C_4\) coefficients, the relation has four states, so each selector permits one primitive four-frequency line and masks the other twelve target frequencies.

The two selector orbits have identical coarse arithmetic invariants (source, target, image size, kernel type and rank) and are separated only by the marked Schur selector. This is imported as an exact formation theorem from the supplied v22 package.

**Boundary.** v22 does not provide a simultaneous marked basis of \(C_4^2\) for the \(4_1\) and \(4_2\) maps and does not determine the still-open even 2-primary induced maps from \(A_6\) and \(L_3(2)\) into \(C_4^2\). Forge therefore keeps those two internal rows open rather than guessing coordinates.
