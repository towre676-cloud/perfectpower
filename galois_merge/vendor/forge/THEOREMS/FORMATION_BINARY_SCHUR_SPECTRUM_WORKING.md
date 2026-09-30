# Imported mixed Schur-spectrum theorem — working v12 interface

The user-supplied continuation beyond Formation v11 proposes the following theorem. Let `T_1,...,T_r` be pairwise nonisomorphic finite nonabelian simple groups with Schur multiplier C2, let `E_i -> T_i` be their universal double covers, put `U=prod E_i` with `Z(U)=F_2^r`, and for `N <= Z(U)` let `G_N=U/N`. For nonzero `c in F_2^r`, let `A_c` be the common-central amalgam on `supp(c)`. Then

`A_c in Form(G_N)  <=>  c in N^perp`.

Consequently every binary linear code `C` is realized as a Schur-amalgam spectrum by taking `N=C^perp`, and code inclusion/join become formation inclusion/join. The supplied continuation also states a repeated-component support/parity criterion and an expected criticality classification.

v0.4 treats the code-spectrum equivalence and repeated-component criterion as **working imported mathematics** because the uploaded v11 archive predates this stronger result and does not contain its full audited proof. The package independently verifies all F2 linear-algebra consequences used by Wilson Forge. The final criticality iff statement is not promoted here.
