# Four recovered constructions, with their domains intact

This release goes back to February and March 2025, then follows two concrete lines through March and June 2026. It builds four reusable pieces: exact weighted constraint geometry, complete searches for sums of powers inside declared boxes, polynomial power-coordinate quotients with integer lifting, and exact finite Fourier/chirp commutants and maps between levels. The arithmetic lifting is applied to every one of the present 3,080 complete quartic packets. The geometry is applied to every stored canonical cell model. The source expressions, replay results and provenance are retained in the repository.

For someone coming to the program fresh, the main gain is reuse. A problem may look harder merely because its variable has been disguised as a square or cube. We can solve the simpler equation, keep exactly the coordinates that lift, and recover every answer to the disguised equation. We can also separate a finite signal on a surface into its constrained, boundary and harmonic parts with exact fractions. The other two recoveries replace unsupported old numerical or symmetry claims with computations whose domain and conventions are visible.

The branch baseline is `a9d7c15`, which already contains the January divisor-kernel recovery and `eb096b3`'s actual symplectic cycle integrations and canonical curve geometry. This release does not replace the native Runge engine. A power-coordinate reduction can preserve a useful low-degree solver even when the expanded polynomial has much higher degree. The additions here are standard-library Python constructions and elementary mathematical derivations. No new Lean compilation is claimed, and the recovered classical identities are not presented as discoveries.

## Where the ideas were found

On February 16, 2025, the conversation proposed a mass-weighted adjoint and a regularized constraint operator in a cohomological gravity discussion. The useful finite algebra is recovered here independently of that proposed physical application. The original same-mass notation needs different metrics on the domain and codomain of a rectangular map. Positive regularization also changes the operator: it is generally a filter rather than an exact projector.

The March 29, 2025 conversation supplied two explicit sums of powers and several claimed search bounds. Both identities replay exactly. The quartic identity's alleged common divisor 127 was wrong: its common divisor is one. The old assertion that it was not primitive therefore fails. The original search payloads were not recovered, so the present searches have their own explicit bounds and results.

The March 2026 PSG work supplied a 100-term polynomial `PSG_Q_U_L_Z.txt`, created March 25, and a separately saved deweighted expression in `PSG_resultant_symmetry_probe.txt`, created March 16. Both exact expressions are included under `recovery_sources/deep_gems/`. The quotient and deweighting identities are replayed coefficient by coefficient. The original 26-term source polynomial and its resultant computation are not reconstructed by this release. No physical-branch root isolation or transcendence theorem is inferred from an algebraic quotient.

The June 2026 work supplied the finite Fourier/chirp convention and maps between levels. The source is `level_deformation_monograph_v4_26_0.html`, created June 19, section CS, lines 9237–9243. Its relevant excerpt is retained. In particular, its chirp is `zeta_N^(x*x)` even at even levels. Substituting `zeta_(2N)` would change the problem. Small-level dimension results are checked anew without promoting them to a general prime-power formula. `receipts/deep_gems/provenance.json` identifies these source records and the corrections.

## Weighted constraint geometry

Let `D : X -> Y`, and supply symmetric positive definite rational matrices `M_X` and `M_Y`. Then

\[
D^\dagger=M_X^{-1}D^T M_Y.
\]

Indeed `(Dx)^T M_Y y = x^T M_X D^dagger y`. The implementation checks symmetry and positive definiteness by exact LDL elimination with strictly positive pivots. Floats, singular masses and indefinite masses are rejected. Rectangular dimensions are retained throughout. The finite matrix interfaces have dimension or generator limits of 64.

For a matrix `A` whose columns generate a subspace, choose independent original columns `C` by rational row reduction. The orthogonal image projector is

\[
P_C=C(C^TMC)^{-1}C^TM.
\]

Positive definiteness makes the Gram matrix invertible. Consequently `P_C^2=P_C`, `P_C^T M=MP_C`, and it fixes every column of `C`. Selecting a basis permits rank-deficient input. The zero image returns the zero projector. The exact constraint projector is `I-P_C` with `C` spanning `M_X^-1 D^T`; its image is precisely `ker D` because weighted orthogonality to this normal space is equivalent to `Dx=0`.

The old regularized formula is retained as a distinct API:

\[
P_\epsilon=I-D^\dagger(DD^\dagger+\epsilon I)^{-1}D.
\]

For `D=(1,0)`, identity masses and `epsilon=1`, this is `diag(1/2,1)`. Its square is `diag(1/4,1)`, and `DP_epsilon` is nonzero. Thus it neither projects exactly nor enforces the constraint exactly. The correct kernel projector in this example is `diag(0,1)`.

For a chain `C2 --B2--> C1 --B1--> C0` with `B1 B2=0`, form

\[
\Delta_1=B_1^\dagger B_1+B_2 B_2^\dagger.
\]

The images of `B1^dagger` and `B2` are orthogonal: their cross pairing reduces to `B1 B2=0`. Their orthogonal complement is the intersection of `ker B1` and `ker B2^dagger`, which is the kernel of the Laplacian since its energy is the sum of two nonnegative squared norms. The three projectors therefore sum to identity, annihilate one another and are self-adjoint for the supplied mass. The harmonic dimension is `dim C1 - rank B1 - rank B2`. Every returned projector and harmonic Laplacian identity is replayed exactly.

The runner uses the existing models of genera 0, 1, 2, 3, 4 and 7. Vertex, edge and face masses have diagonal entries `i+2`, `i+3` and `i+5` for zero-based `i`. The harmonic dimensions are 0, 2, 4, 6, 8 and 14. The full three-part decomposition of an actual edge vector is saved for each model and recombines exactly. These supplied rational masses are finite model data; they do not identify the original curve's conformal or Bergman metric. The existing analytic geometry remains a separate layer. A primary background reference for complexes and discrete Hodge theory is Arnold, Falk and Winther, [Finite element exterior calculus: from Hodge theory to numerical stability](https://arxiv.org/abs/0906.4325).

## Sums of powers with complete finite domains

The recovered identities are

\[
95800^4+217519^4+414560^4=422481^4,
\qquad
27^5+84^5+110^5+133^5=144^5.
\]

The quartic is Roger Frye's 1988 counterexample (see [Elkies, On A^4+B^4+C^4=D^4](https://doi.org/10.1090/S0025-5718-1988-0930224-9)); the quintic is [Lander and Parkin's 1966 counterexample](https://doi.org/10.1090/S0002-9904-1966-11654-3). Both are primitive. `power_sum_witness` checks the original equality with integer arithmetic, computes the actual common divisor and returns the normalized identity. A changed coordinate is rejected. The large quartic identity is replayed as a supplied witness; it is not found by a search to 422481.

`search_power_sums` enumerates all sorted positive three- or four-term solutions with target at most `B`. It first stores every pair sum `a^k+b^k` with `1<=a<=b<=B`. For three terms, it enumerates `c<target<=B` and looks up the remaining pair. For four terms, it enumerates `c<=e<target<=B` and looks up the pair, retaining only `b<=c`. Every positive solution has target larger than every summand, so these restrictions lose nothing in the stated domain. Repeated coordinates remain legal. An optional common-divisor test restricts the complete domain to primitive identities.

The pair table has `B(B+1)/2` entries before collisions. Three-term searches perform `B(B-1)/2` remainder lookups; four-term searches perform `B(B-1)(B+1)/6`. A work budget checks the whole operation count before returning any list. Oversized work raises `WorkLimit`, with no partial list presented as complete. Integer degrees 2 through 64 are supported. Storage is quadratic in the bound; this does not solve the unbounded problem.

At degree five, four terms and `B=144`, the only primitive sorted solution is `(27,84,110,133;144)`. This required 10,440 pair entries and 497,640 remainder lookups. The three-term quartic search through 200 returns no solution, with 20,100 pair entries and 19,900 lookups. These results are complete inside their boxes. Neither is a nonexistence theorem outside its box, and neither reproduces the old reported scans through 10000 or 500.

## Polynomial quotients and exact integer lifting

The sparse parser accepts named variables, integer constants, addition, subtraction, multiplication and bounded nonnegative powers. It never evaluates Python code. Node, exponent, term and product budgets reject unsupported work. Sparse coefficients are exact fractions. A polynomial descends from coordinate `x` to `U=x^q` exactly when every nonzero term's exponent of `x` is divisible by `q`. Dividing those exponents gives the quotient; multiplying them reconstructs the original polynomial.

The recovered `Q(U,L,Z)` has 100 terms and degrees `(6,14,4)`. Substituting `U=L^2 W` and removing the common `L^12` changes each exponent triple `(u,l,z)` to `(u,l+2u-12,z)`. All resulting exponents are nonnegative, and the result matches all coefficients of the independently saved deweighted expression. Hence the polynomial identity

\[
Q(L^2W,L,Z)=L^{12}\widetilde Q(W,L,Z)
\]

holds including at `L=0`. The inverse coordinate chart requires `L!=0`; division does not classify the exceptional scale-zero fibre. Pulling `Q` back through squares in its first and third variables and descending again recovers all 100 terms. Passing to a quotient forgets integer image constraints: `U` and `Z` must still be integer squares to lift through those square coordinates.

Matching the outer coefficients does not establish reversal symmetry. At `L=1,Z=2`, the deweighted coefficient vector, in increasing degree, is `[-9,270,-159,4,-55,14,-1]`. The outer ratio is the square 9, but the coefficient defects `c_j-9*c_(6-j)` are `[0,144,336,-32,1376,-2416,80]`. The full coefficient claim fails. This is a concrete obstruction to that proposed shortcut, not a classification of every possible transformed symmetry.

For the arithmetic application, write `F(x)=H(x^q)`. Every integer point `(x,y)` of `y^2=F(x)` maps to the integer outer point `(u,y)=(x^q,y)` of `y^2=H(u)`. Conversely, an outer point lifts precisely when `u` is an integer `q`-th power. Odd powers give one signed root; even powers give both signs for positive `u`, one root for zero, and no root for negative `u`. Substitution verifies every lift in the original equation. Thus a complete outer list transports to a complete original list. Membership checks on an arbitrary supplied outer list do not establish that list's completeness, and the public API states this distinction explicitly.

`solve_power_composition` recognizes the quotient and invokes the existing complete square-leading quartic solvers, including their finite work budgets and global bounds. For example `y^2=x^8+x^2+1` has exactly `(0,-1)` and `(0,1)`: its outer quartic is `u^4+u+1`, whose complete outer inputs are `-1,0`, and only zero lifts through a square. The corresponding cubic substitution retains both `x=-1` and `x=0`, with the two signs of `y`. Exact outer polynomial squares, unsupported outer families and oversized intervals are rejected by this route rather than assigned a false finite answer.

All 3,080 stored quartics are pulled back through both squares and cubes, producing 6,160 equations of degrees eight and twelve. The square pullbacks have 2,810 point occurrences; the cube pullbacks have 2,445, for 5,255 in total. These are counts across labelled equations, not distinct pairs across the entire atlas. The runner binds each input polynomial to the coefficients reconstructed from its proved parameters, matches its literal point packet to `CompleteQuartics.lean`, and checks that file's SHA-256 against the stored complete kernel ledger. All 3,080 packets match. The inherited outer lists were previously kernel checked; the new lifting computation is Python and no new Lean theorem or compilation is claimed. A tampered polynomial, omitted literal point, changed source or partial ledger is rejected by the audit.

## Exact finite Fourier and chirp operators

For a level `N`, use the field `Q[zeta_N]`, implemented as the quotient by the cyclotomic polynomial. Cyclotomic irreducibility is classical background for the field interpretation, not a new certificate emitted by the generic quotient-algebra module. This release uses only those cyclotomic moduli. It takes the unnormalized Fourier matrix `F_N[x,y]=zeta_N^(xy)` and the diagonal chirp `T_N[x,x]=zeta_N^(x*x)`. Multiplying a Fourier matrix by the scalar `1/sqrt(N)` would not change its commutant; omitting that scalar keeps entries in the cyclotomic field.

To construct every matrix commuting with the pair, the diagonal chirp first forces `C[i,j]=0` unless `i^2=j^2 mod N`. On those allowed entries, `CF=FC` is a finite linear system with coefficients in the cyclotomic field. Exact Gaussian reduction constructs a basis of its entire kernel. The number of free coordinates is the commutant dimension. Each basis matrix is independently substituted into both commutation equations. This is a complete finite linear computation, not a sample of proposed commuting matrices.

The levels 2, 3, 4, 5, 7, 8 and 9 have dimensions 1, 2, 3, 2, 2, 5 and 3 respectively. The public commutant calculation permits levels 2 through 9 and caps its field-entry operation budget. Field inversions and rational polynomial bit costs are additional costs; the counter is not a timing model. These bounded results do not prove `c(p^a)=a+1` or a general dyadic formula. The subsequent [CRT commutant extension](WEIL_CRT_MONOGRAPH.md) provides exact dimension certificates through level 64 and the general Gauss/generator-separation bridge; its all-level dimension assembly is described separately.

Clock `Z` and cyclic shift `X` satisfy `ZX=zeta_N XZ`. Distinct clock eigenvalues force a matrix commuting with `Z` to be diagonal, and commuting with `X` forces its diagonal constant, so their commutant is scalar. The runner checks the root phases and relation and also checks `F_N^2=N*parity` with exact cyclotomic sums. This preserves the old distinction between the clock/shift carrier and the potentially larger Fourier/chirp commutant. A primary background reference is [On the Weil representation associated to finite quadratic modules](https://arxiv.org/abs/1108.0202); the actual pair used here is defined by the recovered convention, without a claim to have established all modular-group relations.

For coprime `a,b`, the recovered section is `(u,v)->b*u+a*v mod ab`. It is bijective, but its coordinates are scaled relative to ordinary residue coordinates. Expanding a product or square makes the cross terms multiples of `ab`, giving `F_ab=F_a^(b) tensor F_b^(a)` and `T_ab=T_a^b tensor T_b^a` under this section. The runner checks every phase congruence for factor pairs `(2,3),(3,4),(3,5),(4,5),(5,7)`. The twists are retained explicitly.

For `M=L*d`, define `I[j,k]=[j=d*k]` and `R[j,k]=[j=k mod L]`. The unnormalized identities are `F_M I=R F_L`, `F_M R=d I F_L`, and `T_M I=I T_L^d`. The second follows by summing phases on a fibre: the sum is zero unless `d` divides the Fourier row, when it is `d` times the small-level phase. The replay verifies these identities for `(L,M)=(2,4),(3,6),(3,9),(4,8),(5,10),(4,12)`. Old/new sector induction, categorical conductor transfer and hardware acceleration remain outside this implementation.

## Reproduction and validation

Run `python python/recover_deep_gems.py` to rebuild the six deterministic JSON receipts. The runner resolves source paths from its own location and works by absolute path from another directory. It uses only the standard library. Run `PYTHONPATH=python python -m unittest discover -s python/tests -p test_deep_gems.py` for the 29 focused tests. They compare bounded power searches against independent exhaustive enumeration, exercise dense rational mass matrices and rank deficiency, verify signed and zero lifts, compare the recovered source expressions, reject tampered outer proof inputs, check exact finite symmetries and maps, and exercise all four console commands.

Use `PYTHONPATH=python python -m perfectpower power-composition --coeff '[1,0,1,0,0,0,0,0,1]' --power 2`, `power-sums --degree 5 --terms 4 --bound 144 --primitive`, or `finite-weil --level 8` for the arithmetic and symmetry commands. `weighted-hodge --chain` accepts a JSON object with `boundary1`, `boundary2`, `mass0`, `mass1`, `mass2`; exact rational entries may be strings such as `"3/2"`. All coefficients are ordered from constant term upward where a coefficient list is used.

The full suite and cold archive checks are recorded in `receipts/deep_gems/validation.json`, with the full test log alongside it. A clean archive is extracted to a new directory and replayed with `python -S`, outside the source checkout; all six generated JSON files must match byte for byte. The complete repository ZIP includes source, prior work, exact input expressions, derivations, tests and receipts. Python's `execution_verified=False` flags continue to distinguish tested computation from formal verification of program execution.
