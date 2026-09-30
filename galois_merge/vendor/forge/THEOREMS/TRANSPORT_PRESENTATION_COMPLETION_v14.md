# Transport Presentation Completion v0.14

Let \(A=\operatorname{End}^{*}(Q6)_{\mathbf Q}\) be the 486-dimensional characteristic-zero transport algebra and let \(g,h\) be the two-generator presentation fixed in v0.13.

The 25 filtered relations through degree eight do **not** generate the complete two-sided relation ideal. Through degree nine the free word space has dimension \(1023\), so the exact kernel has dimension \(1023-486=537\). The two-sided consequences of the degree-eight wall have rank exactly \(125=25+100\) through degree nine. Therefore the first genuinely new relation quotient occurs in degree nine and has dimension

\[
537-125=\boxed{412}.
\]

The exact homogeneous degree-nine evaluation has rank 486, hence its homogeneous kernel has dimension \(512-486=26\). If \(U_9\subset A\) is the 100-dimensional image of the one-letter left/right descendants of the old degree-eight wall, then the remaining boundary quotient has dimension \(486-100=386\). Thus the new degree-nine obstruction has the filtered decomposition

\[
\boxed{412=26+386}.
\]

The old leading image has projection ranks
\[
\operatorname{rank}(\pi_S U_9)=25,\qquad
\operatorname{rank}(\pi_+U_9)=36,\qquad
\operatorname{rank}(\pi_-U_9)=100,
\]
with kernel dimensions \(75,64,0\) respectively. Since the plus projection is already onto \(A_+\), the 386-dimensional boundary quotient is concentrated in the minus-side radical:
\[
A/U_9 \cong K_-/B_{64},\qquad \dim K_-=450,\quad \dim B_{64}=64.
\]

There is **no canonical \(M_5\)-module type** on the 412-dimensional new obstruction quotient. The degree-eight identification with \(M_5\) is a filtered vector-space boundary isomorphism, not a subalgebra action; moreover 412 is not divisible by 5, whereas every finite-dimensional left module over \(M_5(\mathbf F_p)\) has dimension divisible by 5.

A filtered noncommutative diamond completion terminates at degree nine. The package freezes 486 normal words of degree at most eight, 25 degree-eight rewrite rules, and rewrite rules for all 512 degree-nine monomials. Modulo the old degree-eight ideal, 412 degree-nine rules are new. The 25+412 generators span the full kernel through degree nine, every word of length at least nine has a reducible length-nine prefix, and the 486 normal-word evaluations are independent. Hence the quotient is exactly \(A\).

The count and termination lift to characteristic zero by good reduction. This release freezes explicit finite-field rewrite coefficients at \(p=1,000,003\); it does **not** reconstruct all 412 rational coefficient vectors.
