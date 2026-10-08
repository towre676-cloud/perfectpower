# Singular Richelot splittings and cluster stable reduction

## Purpose and position

Two open items were left by the [algebraic curve extensions](ALGEBRAIC_CURVE_EXTENSIONS_MONOGRAPH.md) and [literature curve execution](LITERATURE_CURVE_EXECUTION_MONOGRAPH.md) releases. The existing `richelot_correspondence` refuses a quadratic splitting whose Richelot determinant vanishes ("singular Richelot splittings require a separate product construction"). The existing `root_clusters` builds a geometric double-cover graph for rational split roots, but derives no inertia action, no stable contraction and no conductor, and "broader stable models with several simultaneous collisions" remained open.

This release closes both items within explicit scopes.

1. `perfectpower.singular_richelot` treats y²=G₁G₂G₃ with binary quadratic forms Gᵢ=(c₀,c₁,c₂), so c₂=0 places a root at infinity. When det(Gᵢ)=0 it constructs the pencil squares l₁², l₂², two explicit elliptic quotients E₁, E₂, both quotient maps, their differential pullbacks and the (2,2)-gluing ψ:E₁[2]→E₂[2]. If the squares are irrational, E₂ is the Galois conjugate of E₁ and J(C) is isogenous to a Weil restriction. Every identity is exact. Isogeny invariance is replayed through complete L-polynomials at good primes.
2. `perfectpower.cluster_stable_reduction` implements cluster pictures in the sense of Dokchitser–Dokchitser–Maistret–Morgan (DDMM) for any genus, p odd. Roots may lie in Q, in one quadratic field Q(√D) ⊂ Q̄_p, or in Q[t^{±1/2}] for K=Q((t)). The module computes nested and disjoint clusters, depths, ν_s and principal, twin, cotwin and übereven clusters. It also builds the semistable double-cover graph with explicit sheets and its stable contraction. It derives the tame inertia action on that graph and on the positive-genus components, and from it the toric, abelian and unipotent ranks and the conductor exponent.
3. `perfectpower.cluster_monodromy` independently replays the t-adic inertia action as the topological monodromy of a small loop around t=0. The braid word is read from root positions on a loop whose radius is below an exact Cauchy bound. The repository's integral Picard–Lefschetz representation (`marked_curve_topology.braid_monodromy`) then gives an exact symplectic matrix.

All mathematics here is classical: Richelot, Bost–Mestre, Kani and Frey–Kani for gluings, and DDMM, Bouw–Wewers and Liu for stable reduction. The contribution is an exact, replayable implementation with independent cross-checks, not a priority claim.

## 1. Singular Richelot splittings

### Setting

Write a binary quadratic form as G=c₀z²+c₁xz+c₂x², stored as (c₀,c₁,c₂). The source is C: y²=F(x,z)=G₁G₂G₃, a binary sextic, and C has genus two exactly when F is squarefree as a binary form, infinity included. The Richelot determinant is δ=det(cᵢⱼ). For δ≠0 the classical target is v²=H₁H₂H₃/δ with Hᵢ=G′ⱼGₖ−GⱼG′ₖ. This affine bracket is half the Jacobian covariant ∂ₓGⱼ∂_zGₖ−∂_zGⱼ∂ₓGₖ, so it is also valid at infinity.

### Theorem 1 (the pencil)

Assume F is squarefree and δ=0. Then:

1. G₁, G₂, G₃ span a pencil Π of dimension 2.
2. The discriminant q(λ,μ)=disc(λP+μR) restricted to Π is a binary quadratic form with nonzero discriminant.
3. Π contains exactly two squares κ₁l₁² and κ₂l₂², with non-proportional linear forms defined over Q(√disc q) and Galois-conjugate when that field is quadratic.
4. Gᵢ=aᵢl₁²+bᵢl₂² with all aᵢ, bᵢ nonzero and the ratios −bᵢ/aᵢ distinct.

*Proof.* Two proportional forms would share roots, so the rank is 2. Squares form the smooth conic B²=4AC in the projective plane of binary quadratics. A line meets the conic in two points, is tangent to it, or lies in it; the last case is impossible. Tangency at l² means that Π is the polar line of l², which consists of the forms divisible by l. All Gᵢ would then share the root of l, contradicting squarefreeness. Hence q has two simple roots, which give two distinct squares. Conjugation preserves Π and the conic, so it permutes the two squares. Finally, aᵢ=0 or bᵢ=0 would make Gᵢ a square, and equal ratios would make two forms proportional. ∎

### Theorem 2 (explicit splitting and gluing)

Put u=l₁/l₂ and W=l₁′l₂−l₁l₂′, a nonzero constant. Write φ^∗ for pullback and φ,∗ for pushforward of divisor classes. Then:

1. F=∏(aᵢl₁²+bᵢl₂²), so C is y²=∏(aᵢu²+bᵢ) after scaling y by l₂³.
2. The maps
   φ₁:(x,y)↦(X,Y)=(l₁²/l₂², y/l₂³) onto E₁: Y²=∏(aᵢX+bᵢ), and
   φ₂:(x,y)↦(l₂²/l₁², y/l₁³) onto E₂: Y²=∏(aᵢ+bᵢX)
   are the quotients by τ:u↦−u and by τι, where ι is the hyperelliptic involution.
3. φ₁^∗(dX/Y)=2W l₁ dx/y and φ₂^∗(dX/Y)=−2W l₂ dx/y. These pullbacks span H⁰(C,Ω).
4. φ₁^∗+φ₂^∗:E₁×E₂→J(C) is an isogeny of degree 4. Its kernel is the graph of ψ:(−bᵢ/aᵢ,0)↦(−aᵢ/bᵢ,0).
5. Dually, (φ₁,∗, φ₂,∗):J(C)→E₁×E₂ has kernel equal to the Richelot kernel {[roots of Gᵢ]−[roots of Gⱼ]}.

*Proof.* (1) follows from Theorem 1 and (2) is substitution. For (3), d(l₁²/l₂²)=2Wl₁l₂⁻³dx and Y=y/l₂³; the second case is the same with the indices exchanged. Since l₁ and l₂ are independent, the pullbacks span. For (4), φ₂,∗∘φ₁^∗=0: the τ-invariant divisor {R,τR} maps to {φ₂R, φ₂ιR}, a fibre of x on E₂, whose class is constant. Also φₖ,∗∘φₖ^∗=[2], so the composite (φ₁,∗,φ₂,∗)∘(φ₁^∗+φ₂^∗) is [2] on E₁×E₂, of degree 16. The two maps are dual for the principal polarizations, so each has degree 4. For Tᵢ=(−bᵢ/aᵢ,0)−O, the divisor φ₁^∗Tᵢ−φ₂^∗T′ᵢ is the divisor of u, so (Tᵢ,T′ᵢ) lies in the kernel. These three points and 0 form a group of order 4. (5) is the dual statement: φ₁,∗([roots of Gᵢ]−[roots of Gⱼ])=2(Tᵢ−Tⱼ)=0. ∎

When disc q is not a square, the pencil squares are conjugate, κ₂=κ₁^σ and l₂=l₁^σ, so bᵢ=aᵢ^σ and E₂=E₁^σ coefficientwise. The isogeny is Galois-stable, so J(C) is isogenous over Q to Res_{k/Q}E₁ with k=Q(√disc q). This case has no splitting over Q. It is the arithmetic content of a singular Richelot splitting with irrational squares.

### Theorem 3 (replayable isogeny invariant)

Let p be odd, let F mod p be squarefree of full binary degree, and let the E-models have unit leading coefficients and unit discriminants. Then:

- L_C(T)=L_{E₁}(T)L_{E₂}(T) when p splits in k or k=Q, using one embedding √D↦s for both curves;
- L_C(T)=1−a_{p²}(E₁)T²+p²T⁴ when p is inert.

For δ≠0, L_C(T) equals the L-polynomial of the Richelot target.

*Proof.* Isogenous abelian varieties have isomorphic Tate modules, so their characteristic polynomials of Frobenius agree. At an inert prime, Frobenius exchanges the two factors of Res E₁, and its characteristic polynomial is that of Frob_{p²} on E₁ evaluated at T². ∎

The program computes L_C from exact point counts N₁ and N₂ over F_p and F_{p²}. Each count sums 1+χ(F) over P¹, with leading coefficient χ at infinity. L_E is computed directly over F_p or F_{p²}=F_p(√D). The integer polynomials are compared. This check is independent of the construction and does not reuse the decomposition identity.

### Certificates

- The pencil decomposition Gᵢ=aᵢl₁²+bᵢl₂² holds exactly in Q(√D)[x].
- l₂⁶E₁(l₁²/l₂²)=F=l₁⁶E₂(l₂²/l₁²) holds as binary sextics.
- The differential identity d(l₁²)l₂²−l₁²d(l₂²)=2Wl₁l₂ holds, and the pullback matrix is invertible.
- E₂=E₁^σ coefficientwise in the quadratic case.
- L-polynomials agree at every admissible prime below 80.

The negative control replaces E₂ by its quadratic twist by 2. The L-polynomial identity then fails at at least one prime, so the comparison has discriminating power.

## 2. Cluster pictures and the semistable model

### Definitions

Let C: y²=c∏_{r∈R}(x−r), |R|=n≥3 and g=⌊(n−1)/2⌋, over K=Q_p with p odd, or over K=Q((t)). The program uses the following definitions.

- A cluster is a subset s⊆R cut out by a disc, with |s|≥2 or s=R.
- The depth is d_s=min_{r,r′∈s} v(r−r′), and the relative depth is δ_s=d_s−d_{P(s)}, where P(s) is the parent cluster.
- ν_s=v(c)+|s|d_s+Σ_{r∉s}d_{r∧s}, where r∧s is the smallest cluster containing r and s. Put μ_s=ν_s−|s|d_s.
- s is even or odd according to |s|, a twin if |s|=2, and übereven if all its children are even.
- s is a cotwin if it has a child of size 2g and is not übereven.
- s is principal if |s|≥3, s is not a cotwin, and s is not R in either of these cases: |R| is even with exactly two children and no singletons, or |R| is even with a child of size 2g+1.

The last two exceptions are exactly the root clusters whose components are contracted below. The program's DDMM-style semistability test uses this list and asserts agreement with the graph-action test on every input.

### Theorem 4 (geometric semistable graph)

Take a tame extension L/K that makes every depth integral and every relevant ν_s even. The model of P¹_L given by the cluster discs is a tree of P¹'s indexed by the clusters, with annuli of thickness δ_s between them. The normalized double cover over this tree has these parts.

- **Components.** Cluster s carries f_s odd branch flags: its odd children, plus the parent flag if |s| is odd (∞ for s=R). If f_s>0, s has one component of genus (f_s−2)/2. If f_s=0, it has two rational components, called sheets.
- **Annuli.** An odd child s gives one ramified lift of its annulus, of length δ_s/2. An even child gives two unramified lifts, each of length δ_s.

Lengths are measured in v_K units. The graph is connected and g=Σg_v+b₁.

*Proof sketch.* On the component of s, y²=θ_s²∏_{children}(X−red s′)^{|s′|}, where X=(x−z_s)/β_s, v(β_s)=d_s and θ_s²=cβ_s^{|s|}∏_{r∉s}(z_s−r). This is Riemann–Hurwitz on each P¹. An annulus of thickness δ carrying an odd number of branch points is covered by one annulus of thickness δ/2; otherwise it has two unramified lifts. The genus identity is the global Riemann–Hurwitz count. It is checked by the code on every input. ∎

Stable contraction repeatedly removes genus-0 leaves and smooths genus-0 bivalent vertices, adding edge lengths. The potential toric rank is b₁ of the stable graph. The curve has potentially good reduction exactly when this graph is a single genus-g vertex.

### Theorem 5 (tame inertia on the special fibre)

Let σ generate tame inertia. Choose π^q∈K̄ compatibly with σπ^q=e^{2πiq}π^q. Every root lies in K(√D) or K(t^{1/2}), so d_s∈½Z, and σ acts on R with orbits of size at most 2.

1. **Fixed cluster.** If σs=s, then σ acts on Γ_s by X↦αX+b and Y↦εY, with α=e^{−2πid_s} and ε=e^{πi(2d_sE_s−ν_s)}, where E_s=Σ_{children}⌊|s′|/2⌋.
   - The two sheets of a vertex with no odd flags are exchanged iff μ_s is odd.
   - The two lifts of an even edge s′→P(s′) are exchanged iff μ_{s′} is odd.
2. **Moved pair.** If σs≠s, label the σs-subtree by transport from the s-subtree. σ² fixes all roots and acts on the s-subtree by the doubled phases e^{−2πiμ}.
3. **Positive-genus component.** The σ-invariant part of H¹(Γ_s) has dimension:
   - 2g_s or 0 when α=1, according as ε=±1;
   - 0 when α=−1 and the number m_s of odd children is odd;
   - (2g_s+2−F)/2 when α=−1 and m_s is even, where F=2[ε=1]+2[ε(−1)^{m_s/2}=1] counts the fixed points over the two fixed points X₀, ∞ of X↦−X+b;
   - 2g_s or 0 for a moved pair, according as 2ν_s is even or odd.

*Proof.*

- **X-action.** σ fixes x and y, so σ*(X)=(β_s/σβ_s)X+(z_s−σz_s)/σβ_s. Its residue is αX+b. A finite-order tame action excludes a nontrivial translation when α=1.
- **θ and Y.** θ_s²=π^{ν_s}U, where U is a unit of K(R). Inertia acts trivially on residues, so σθ_s/θ_s≡e^{πiν_s}. On generic points of Γ_s, x−σz_{s′}≡x−z_{σs′}, and with Y=yβ^{E_s}/(θ_s∏(x−z_{s′})^{⌊|s′|/2⌋}) this gives σ*Y≡εY.
- **Sheets and lifts.** The lift function of an even edge is y/(θ_e(x−z_{s′})^{|s′|/2}) with θ_e²=c∏_{r∉s′}(z_{s′}−r), of valuation μ_{s′}. The sheet rule for a vertex with no odd flags is the case f_s=0.
- **Invariants.** Average traces over the cyclic group generated by σ. The Lefschetz formula gives tr(h|H¹)=2−#Fix(h) for h≠1. In case α=−1 with m_s odd, σ²=ι and both fixed points over X₀ and ∞ are branch points, so the average is 0.
- **Moved pair.** σ acts on H¹(Γ_s)⊕H¹(Γ_{σs}), and its invariants are identified with those of σ² on H¹(Γ_s). ∎

The code assembles σ as a permutation of vertices and edges. It asserts that σ preserves every incidence and that every phase it uses is integral. Both assertions held on all inputs below.

### Theorem 6 (conductor)

Write H¹=H¹_ab⊕H¹(Γ)⊗Sp(2) as a Weil–Deligne representation. The I_K-invariants have dimension

  dim H¹_ab^σ + dim H₁(Γ,Q)^σ = 2a + t,

where t is the toric rank of the Néron model over K and a its abelian rank.

The supported root extensions are tame because p is odd and they are at most quadratic, so the Swan conductor vanishes. Therefore

  n = n_tame = 2g − (2a + t),  u = g − a − t.

The curve is semistable over K iff 2a+t=2·(potential abelian rank)+(potential toric rank). The program asserts that this agrees with the DDMM criterion: every proper cluster is inertia-invariant, and every principal cluster has d_s∈Z and ν_s∈2Z.

*Proof.* Grothendieck's description of the monodromy filtration gives (H¹)^I=ker N on the semisimple invariants. Its dimension is that of the invariants of the finite tame action on H¹_ab and on H¹(Γ), and Theorem 5 supplies that action. ∎

## 3. Independent replays

### PARI genus2red

For genus two over Q_p, PARI/GP's `genus2red` implements Liu's algorithm, which is independent of clusters. Twelve named examples are recorded with the conductor exponents printed by PARI/GP 2.17.2. They cover rational, unramified, ramified and Galois-swapped root sets. The unit tests compare against these literals and do not need PARI.

The optional `--pari` receipt contains 1000 seeded random curves, 250 each of rational, unramified-quadratic, ramified-quadratic and swapped-cluster type, with p∈{3,5,7,11}. More than 2,000 further curves of the same four types also agreed in development runs; these runs are not recorded. There were no disagreements.

### Topological monodromy (Q((t)), genus ≤ 4)

For roots r_i(t^{1/2}) the monodromy of the loop t=ρe^{iθ} is the inertia action.

1. **Radius.** ρ is below an exact Cauchy lower bound for the nonzero roots of every difference r_i−r_j and of the leading coefficient c(t).
2. **Braid word.** Root positions are projected through a rotation followed by a shear, a plane diffeomorphism that removes rigid collinear alignments. Adjacent crossings are located by bisection and signed by the transverse coordinate. Simultaneous disjoint crossings commute.
3. **Matrix.** braid_monodromy(g, word)·(−1)^{v(c)} is an exact integral symplectic matrix T. The sign records the winding of √c.
4. **Stability.** The matrix must agree under sample refinement. The invariants (dim ker(T−1), the semisimple order and rank(T^m−1) at the unipotent power) must agree under a second projection.
5. **Comparison.** 2g−dim ker(T−1) is compared with the cluster conductor, and rank(T^m−1) with the potential toric rank.

## 4. Results

| item | result |
|---|---|
| singular Richelot named examples | 4 examples. Two split over Q, one of them with a root at infinity. Two are Weil restrictions, from Q(√2) and from Q(√−1); the Q(√2) example also has a linear factor. Complete L-polynomials agree at 19–21 primes below 80 for each example. |
| exhaustive box | All 11,600 unordered triples of distinct forms with coefficients in {−2,…,2}, δ=0 and squarefree sextic split. By pencil field: Q 4,608; Q(√2) 2,096; Q(√−1) 1,824; Q(√−2) 640; Q(√3) 576; Q(√6) 512; Q(√5) 480; Q(√−3) 256; Q(√7) 192; Q(√10) 128; Q(√−5) and Q(√11) 64 each; Q(√−7), Q(√13), Q(√14), Q(√17) and Q(√22) 32 each. All 41,376 L-polynomial comparisons at p≤13 agree. |
| constructed sweep | 32 constructed splittings with D∈{1,2,3,5,−1,−2,−3,−7} and generic coefficients; all 250 prime checks agree. |
| smooth Richelot replay | For δ≠0, the classical example and a variant with a root at infinity have squarefree targets; source and target L-polynomials agree at 17 primes each. |
| negative control | Twisting E₂ by 2 breaks the identity at p=13, 19, 29 and 37. |
| named p-adic clusters vs PARI | All 12 conductor exponents equal PARI 2.17.2 genus2red. |
| named Q((t)) families vs braid | 9 families of genus 2–4, including twists by the leading coefficient t, Puiseux half rates and swapped twins. The conductor and the potential toric rank agree with the braid monodromy for all 9. |
| seeded Q((t)) sweep vs braid | 120 seeded families of genus 2 and 3, with semisimple orders 1, 2 and 4, all agree. |
| p-adic internal sweep (DDMM ⇔ graph action) | 600 seeded curves of genus 2–4 over rational, unramified and ramified domains. The DDMM semistability criterion equals the graph-action test in every case. |
| PARI random cross-check (optional receipt) | 1,000 seeded genus-two curves: 0 disagreements. |

### Named p-adic genus-two curves

The PARI column is the PARI/GP 2.17.2 genus2red conductor exponent. The column σ-inv gives (dim H¹_ab^σ, toric rank t).

| name | p | roots | c | pot. toric | pot. abelian | σ-inv | n | PARI | stable edges |
|---|---|---|---|---|---|---|---|---|---|
| three_twins | 3 | 0,3,1,4,2,5 | 1 | 2 | 0 | (0,2) | 2 | 2 | 2,2,2 (theta graph) |
| three_twins_twisted | 3 | same | 3 | 2 | 0 | (0,0) | 4 | 4 | 2,2,2 |
| nested_triple | 5 | 0,5,25,1,2 | 1 | 1 | 1 | (2,0) | 2 | 2 | 1/2, loop 2 |
| nested_triple_twisted | 5 | same | 5 | 1 | 1 | (0,1) | 3 | 3 | 1/2, loop 2 |
| disjoint_twins_two_rates | 7 | 0,49,1,344,2 | 1 | 2 | 0 | (0,2) | 2 | 2 | loops 4, 6 |
| cotwin_like | 3 | 0,1,2,3,9 | 1 | 1 | 1 | (2,0) | 2 | 2 | 1/2, loop 2 |
| half_depth_cluster | 5 | ±√5, ±2√5, 1, 2 | 1 | 1 | 1 | (0,1) | 3 | 3 | loop 1 |
| half_depth_odd_cluster | 5 | ±√5, ±2√5, 0 | 1 | 0 | 2 | (0,0) | 4 | 4 | none |
| swapped_twins | 3 | ±√3, 9±√3, 1 | 1 | 2 | 0 | (0,1) | 3 | 3 | 1,3,3 |
| swapped_triples | 3 | ±√3, 9±√3, 18±√3 | 1 | 0 | 2 | (0,0) | 4 | 4 | 3/2 |
| unramified_triple | 7 | ±49√3, 0, 1, 2 | 1 | 0 | 2 | (4,0) | 0 | 0 | 1 (two elliptic components) |
| unramified_pair_twin | 5 | 1±25√2, 0, 2, 3, 4 | 5 | 1 | 1 | (0,0) | 4 | 4 | loop 4 |

Several rows illustrate distinct phenomena.

- **unramified_triple.** The Jacobian has good reduction (n=0), but the curve does not: its stable fibre is two elliptic curves meeting at a point.
- **swapped_triples.** Inertia exchanges two genus-one components, so the Jacobian has potentially good reduction and n=4.
- **nested_triple_twisted.** The twist by 5 kills the abelian invariants and leaves one toric invariant.

### Q((t)) families with collisions at several rates

These are checked against braid monodromy. The column ord is the order of the semisimple part of T.

| name | roots | c | g | pot. t | σ-inv (ab,t) | n (clusters) | n (braid) | ord | stable components; edges |
|---|---|---|---|---|---|---|---|---|---|
| nested_rates_1_2 | 0, t, t², 1, 2 | 1 | 2 | 1 | (2,0) | 2 | 2 | 2 | g=1, g=0; 1/2, loop 2 |
| nested_rates_1_2_twisted | same | t | 2 | 1 | (0,1) | 3 | 3 | 2 | same |
| disjoint_twins_rates_1_2_3 | 0, t, 1, 1+t², 2, 2+t³ | 1 | 2 | 2 | (0,2) | 2 | 2 | 1 | two g=0; 2, 4, 6 |
| four_at_rate_1_genus_3 | 0, t, 2t, 3t, 1, 2, 3 | 1 | 3 | 1 | (4,1) | 1 | 1 | 1 | two g=1; 1, 1 |
| half_rate_pairs | ±t^½, ±2t^½, 1, 2 | 1 | 2 | 1 | (0,1) | 3 | 3 | 2 | g=1; loop 1 |
| half_rate_odd_cluster | ±t^½, ±2t^½, 0 | 1 | 2 | 0 | (0,0) | 4 | 4 | 4 | g=2 |
| swapped_twins_puiseux | ±t^½, ±t^½+t², 1 | 1 | 2 | 2 | (0,1) | 3 | 3 | 2 | two g=0; 1, 3, 3 |
| genus_4_three_levels | 0, t, t³, t³+t⁵, 1, 1+t², 2, 3, 4, 5 | 1 | 4 | 3 | (2,3) | 3 | 3 | 1 | g=1, two g=0; 4,1,1,1,4 |
| genus_3_twisted_nest | 0, t², t²+t³, t, 1, 1+t, 2, 3 | t | 3 | 3 | (0,1) | 5 | 5 | 2 | three g=0; 2,1,1,1/2,2 |


## 5. Scope and what is not claimed

**Richelot**

- Inputs are binary forms over Q with a squarefree sextic.
- A singular source is rejected; its target would be a degenerate abelian variety.
- Kani's criterion is neither needed nor implemented. Isogenies are not written on Mumford coordinates, and the polarization types of further gluings are not classified.
- L-polynomial agreement is an isogeny invariant used as an independent replay. The proof of the isogeny is Theorem 2, not the counts.

**Clusters and conductors**

- p must be odd, and the roots must lie in Q, in one quadratic field Q(√D) with √D∉Q_p, or in Q[t^{±1/2}].
- Splitting fields of higher degree, wild ramification and p=2 are not handled.
- For split quadratic fields, the roots must be supplied as rationals.
- Outputs are the semistable and stable dual graphs, inertia action, Néron ranks and conductor exponent.
- Not produced: minimal regular models, component groups, Tamagawa numbers, Frobenius on components, local Euler factors beyond their degree, and root numbers.
- The conductor statement is Theorem 6 together with the cited structure theory (DDMM; Bouw–Wewers; Grothendieck SGA 7). It is checked, not formally proved, by PARI in genus two and by topology in genus at most four.

**Braid replay**

- Root positions and crossings are floating point. The word is accepted only when refinement and a second projection agree.
- The matrix algebra and the loop radius are exact.
- No interval certification of the crossing times is claimed.
- No Lean formalization is added.

## 6. Reproduction

```
cd python
python develop_singular_richelot_and_clusters.py          # receipts/curve_structure/singular_richelot_and_clusters.json
python develop_singular_richelot_and_clusters.py --pari   # optional, needs cypari2: ..._pari.json
python -m unittest tests.test_singular_richelot_and_clusters
```

The main receipt is deterministic: all random sweeps are seeded, and JSON is written with sorted keys.

## 7. Literature

- F. Richelot, *De transformatione integralium Abelianorum primi ordinis commentatio*, J. reine angew. Math. 16 (1837).
- J.-B. Bost, J.-F. Mestre, *Moyenne arithmético-géométrique et périodes des courbes de genre 1 et 2*, Gaz. Math. 38 (1988).
- E. Kani, *The number of curves of genus two with elliptic differentials*, J. reine angew. Math. 485 (1997); G. Frey, E. Kani, *Curves of genus 2 covering elliptic curves and an arithmetical application* (1991).
- N. Bruin, K. Doerksen, *The arithmetic of genus two curves with (4,4)-split Jacobians*, Canad. J. Math. 63 (2011) — Richelot formulas and the δ=0 degeneration.
- B. Smith, *Isogenies and the discrete logarithm problem in Jacobians of genus 3 hyperelliptic curves*, J. Cryptology 22 (2009), §on Richelot isogenies.
- T. Dokchitser, V. Dokchitser, C. Maistret, A. Morgan, *Arithmetic of hyperelliptic curves over local fields*, Math. Ann. 385 (2023); and *Semistable types of hyperelliptic curves*, Contemp. Math. 724 (2019).
- I. Bouw, S. Wewers, *Computing L-functions and semistable reduction of superelliptic curves*, Glasgow Math. J. 59 (2017).
- Q. Liu, *Modèles minimaux des courbes de genre deux*, J. reine angew. Math. 453 (1994); PARI/GP `genus2red`.
- A. Grothendieck, SGA 7 I, Exposé IX (monodromy, semistable reduction, toric/abelian/unipotent ranks).
- A. Ogg, *Elliptic curves and wild ramification*; J.-P. Serre, J. Tate, *Good reduction of abelian varieties* (Néron–Ogg–Shafarevich).
