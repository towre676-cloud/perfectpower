# Two-descent, maximal cubic orders and Brainpool primality

This release supplies general two-descent bounds for the actual Mordell frontier. Every one of its 457 curves has irreducible two-division cubic and no rational two-torsion. General two-descent over the cubic field now supplies an upper rank bound for every curve. Exact point-witness lower bounds determine 289 ranks, including eleven rank-two corrections to records previously labelled rank one. There are 1,027 retained quartic covers, 278 improvements from the Cassels pairing, and 100 auxiliary cubic fields whose power order is nonmaximal.

A separate fifteen-stage elliptic-curve primality certificate proves the Brainpool-384 field modulus prime. An independent exact arithmetic check reduces it to the 45-bit prime 23354449048573, whose primality is established by exhaustive trial division. The release also supplies reversible nonmonic binary-cubic norm transport. It keeps the source coefficient divisibility condition that an unrestricted norm equation would lose.

## What the descent bounds mean

For E over the rationals, the Kummer exact sequence embeds E(Q)/2E(Q) into the two-Selmer group, with quotient Sha(E)[2]. If C is the Selmer dimension and T the rational two-torsion dimension, then C=T+rank(E)+dim Sha(E)[2]. The Cassels pairing identifies an even-dimensional nondegenerate quotient of dimension s. Its removal gives rank(E) at most C-T-s. This bound does not require an analytic-rank calculation or a claimed rational point on every locally soluble cover.

Here T=0 for all 457 inputs. The implementation retains a basis of locally soluble quartic covers from PARI's ell2cover and the upper bound from ellrank. In every result the number of covers minus s equals the upper bound. The cubic-field class-group and unit computations are explicitly certified through bnfcertify, removing the provisional GRH assumption of a bare bnfinit calculation.

For k=-9955, the Selmer dimension is three and the pairing removes two dimensions, giving upper rank one. The rational point (7891/361,151704/6859) has an independently checked lower bound of one from the repository's exact good-reduction character machinery. Its rank is therefore exactly one. Across the frontier, 443 upper bounds equal one. The remaining fourteen upper bounds equal two.

The release distinguishes PARI's reported lower endpoint from the lower bound supplied by actual rational witnesses. Only the latter enters rank_determined. Of the fourteen upper-bound-two curves, thirteen have two independently certified points and exact rank two. The remaining curve, k=-9257, has the interval one to two. Another 167 curves have upper bound one without a retained non-torsion witness. A bounded effort-three search did not close those gaps; they remain visible rather than being settled by a parity assumption.

## Eleven corrections to the historical census

The following parameters were recorded as rank one and now have exact rank two: -9682, -9041, -9005, -7738, -6553, -6458, -5522, -5490, -3326, 5522 and 9034. Their point lower bounds and descent upper bounds agree at two. The old raw census remains an archival input; the reconciled frontier records its old value separately as census_rank and uses the new proved value for rank.

This correction matters for the integral-point program. A rank-one list calculation cannot silently become complete when the curve is actually rank two. The frontier therefore keeps all 457 integral-list obligations, including the 323 empty computed lists and 134 nonempty lists. No integral list is promoted by rank determination alone. A full Mordell-Weil basis, finite-index saturation and the appropriate integral-point bound remain separate requirements.

## Quartic covers as reusable geometric objects

Each retained cover has equation z²=R(t) with degree at most four. Its rational map to the original Mordell model is X=Nx(t)/z² and Y=Ny(t)/z³. Exact polynomial arithmetic checks the universal identity Ny²=Nx³+k R³ for all 1,027 covers. Consequently every rational cover point with z nonzero maps to a rational point on the original curve. The affine chart excludes z=0 explicitly; projective extension is not silently substituted for that denominator condition.

These covers are more useful than a rank number alone. They provide smaller-height point-search models, concrete genus-one equations for the period and continuation machinery, and explicit candidates for studying the residual Tate-Shafarevich classes. Being everywhere locally soluble does not imply having a rational point. The complete Selmer-space calculation and Cassels pairing remain PARI algorithmic results; checking a map identity alone proves neither local solubility nor independence of the Selmer classes.

## Maximal orders and exact multiplication

The descent initialization supplies a cubic field, its discriminant and an integral basis. Every nfcertify call returns an empty list, establishing maximality with no residual prime obstruction. For a monic cubic t³+b t²+c t+d, its polynomial discriminant is b²c²-4c³-4b³d-27d²+18bcd. If the integral-basis rows have determinant delta in the power basis, the field discriminant equals delta² times that polynomial discriminant. The reciprocal absolute determinant is the power-order index.

For every retained field, exact rational arithmetic checks the discriminant identity and constructs all nine basis products. Every product has integer coordinates in the supplied basis. This gives an executable multiplication table for the maximal order used by the external number-field computation. The exact identities establish the declared order arithmetic; maximality and complete class-group data use PARI's certified number-field algorithms.

One hundred fields have power-order index greater than one. This is a material arithmetic distinction: working only in Z[t] can miss integral elements and alter unit or ideal-class calculations. For the field t³-9955 the index is three, and the basis includes (1+t+t²)/3. The class group has invariant factor six. The receipts retain the basis and multiplication table, rather than merely reporting that a maximal order was used.

## Nonmonic norm transport and its reverse domain

Let F(r,s)=a r³+b r²s+c rs²+d s³ with nonzero integer a. If theta is a root of the corresponding nonmonic polynomial, the integral generator t=a theta satisfies G(t)=t³+b t²+ac t+a²d. The exact determinant norm in this cubic algebra satisfies Norm(a r-s t)=a²F(r,s). The algebra identity remains valid with negative leading coefficients and signed source coordinates.

The reverse map is constrained. An element u+v t+w t² comes from the binary source precisely when w=0 and a divides u; then r=u/a and s=-v. An unrestricted norm solver would include elements outside that source domain. The new transport keeps both conditions explicitly and rejects a reverse request that violates either one. Twelve worked signed packets and 405 independently exercised coordinate pairs accompany the implementation.

This closes the coordinate and norm-transport gap for binary cubic sources. It does not by itself solve a unit equation or establish a Skolem bound. General Skolem extraction, effective unit generation in the remaining positive-discriminant orders and complete arithmetic ideal transport still require further work.

## The Brainpool-384 primality proof

The target is the same modulus already defined in PerfectPower.Brainpool384 and RFC 5639. Each ECPP stage supplies N, a trace t, a cofactor s, a curve coefficient a and an affine point P. Set m=N+1-t and q=m/s; the next stage proves q prime. Recover b from the point equation. The checked conditions include nonsingularity at every divisor of N, sP nonzero, q(sP)=infinity, and a large-prime bound stronger than q>(N^(1/4)+1)².

The arithmetic uses affine additions only when their denominators are units modulo N. Thus each operation reduces correctly at every prime divisor. The point sP is affine with projective last coordinate one, so it stays nonzero after every such reduction. If N were composite, it would have a prime divisor l at most sqrt(N); the reduction of sP would have order q. Hasse's bound would give q at most (sqrt(l)+1)², contradicting the checked large-prime inequality. Induction through the chain proves every stage modulus prime.

The independent check uses an integer fourth-root ceiling for a strict sufficient Hasse threshold. It rejects nonunit denominators and singular curves; it does not assume that arithmetic modulo an unproved modulus is field arithmetic. The fifteen stages descend from 384 bits to a terminal 45-bit prime. Exhaustive trial division checks the terminal prime through 4832644. No probable-prime test or unresolved factor of p-1 enters this proof.

This establishes the mathematical field-primality certificate needed by the Brainpool scaling work. The existing Lean file's primality premise has not been replaced with a newly compiled Lean theorem. Translating the ECPP criterion into Lean is a separate formal step; the release adds neither an axiom nor a claimed verified TLS implementation.

## Reproduction and next closures

Set PERFECTPOWER_GP to a PARI/GP executable, or install pari-gp and use the standard executable name. The run here used version 2.15.4. Run make mordell-two-descent-receipts to reproduce the frontier computations and reconciliation. Run make check-mordell-two-descent for exact cover, order, norm-transport and ECPP checks. The committed ECPP chain can be checked without PARI; generating another chain uses develop_brainpool384_ecpp.py with --generate.

The highest-value remaining elliptic work is now narrower: find non-torsion witnesses on 167 upper-rank-one curves, resolve k=-9257, saturate the proved witness subgroups into complete bases, and rerun the affected integral-point calculations. General rank upper bounds for this committed frontier and the Brainpool ECPP certificate are delivered. The full Skolem program, automatic saturation termination from height bounds, and kernel-level descent refinement remain open.

## Mathematical sources

PARI's official Elliptic_curves documentation describes ellrank, ell2cover and the Cassels-pairing bound: https://pari.math.u-bordeaux.fr/dochtml/html-stable/Elliptic_curves.html. Its General_number_fields documentation specifies bnfcertify and the removal of GRH: https://pari.math.u-bordeaux.fr/dochtml/html-stable/General_number_fields.html. The ECPP format and criterion are documented at https://pari.math.u-bordeaux.fr/dochtml/html-stable/Arithmetic_functions.html. Brainpool parameters are specified in RFC 5639: https://www.rfc-editor.org/rfc/rfc5639.txt.
