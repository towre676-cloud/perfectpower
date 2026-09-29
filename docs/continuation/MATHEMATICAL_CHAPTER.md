# Rational structural extraction and the arithmetic of sparse hits

This chapter records the mathematics of the continuation at source base
`ddad6befc1f16219e4860bd90273a99a25e37bd6`. Statements identified below as
formalized refer to the accompanying Lean modules, using Lean and Mathlib
4.20.0. The construction proves existence; it does not formalize the executable
Yun algorithm. Counting conclusions and the geometric finiteness theorem are
separate obligations.

## 1. What the decomposition must mean

Put F=S+k. The relevant equation is F(n)=m^d with n positive and m an integer.
For d≥2 define A(N)=#{1≤n≤N : ∃m∈Z, F(n)=m^d}. Both signs of m represent the
same index; they must never be counted twice. Zero is a hit. Negative values
are hits only for odd d. These elementary conventions become substantive in
structural reductions.

A factorization used to classify this equation should exist for every nonzero
F. Over Q[X] one has

F = c ∏_{j=1}^M P_j^j,

where c≠0, each P_j is monic and squarefree, and distinct layers are coprime.
An absent layer equals 1. Nonzero constants are covered by the empty product.
The zero polynomial is handled separately: every index is a hit for d≥2, and
there is no finite decomposition with nonzero leading scalar and monic layers.

The coefficient field matters. X and X+2 are coprime over Q[X], since
(-1/2)X+(1/2)(X+2)=1. They are not comaximal over Z[X]: evaluation at zero
would make any integral Bezout identity assert that an even integer is one.
Thus an interface demanding `IsCoprime` over Z[X] is not the universal
squarefree-layer interface. This is a distinction between comaximality and
absence of a common nonunit factor, not a numerical edge case. Both sides of
this example are proved in `RationalYun.lean`.

The formal existence construction takes Mathlib's finite multiset of
normalized irreducible factors of F. It collects the distinct factors occurring
exactly j times and multiplies them to form P_j. Monic normalization identifies
associated factors. Each layer is squarefree because its normalized factor
multiset has no repetitions; layers are coprime because a factor cannot have
two different multiplicities. Grouping the original multiset by multiplicity
recovers F, with scalar equal to its leading coefficient. This proves existence
for every nonzero rational polynomial and, by injective coefficient mapping,
for every nonzero integer polynomial.

The independent Python implementation uses Euclidean gcd and differentiation
instead. For monic f, initialize c=gcd(f,f'), w=f/c. At step j put
y=gcd(w,c), P_j=w/y, then replace w by y and c by c/y. Repeat until w=1.
Characteristic zero is essential to this derivative algorithm. Exact Fraction
arithmetic, reconstruction, squarefreeness, pairwise gcds, and degree accounting
are checked. These tests do not establish equivalence to the noncomputable Lean
construction; that is a possible later refinement theorem.

## 2. Extract full powers before testing values

Write j=dq_j+r_j with 0≤r_j<d and set

G_d=∏P_j^{q_j},     R_d=∏P_j^{r_j}.

Then F=cR_dG_d^d. The identity is formalized, together with

deg F=∑_{j=1}^M j·deg P_j. The code uses `natDegree`, justified by the nonzero monic factors.
This accounts for constant layers and prevents degree cancellation.

For an integer X and d>0, being a rational d-th power is equivalent to being
an integer d-th power. Indeed a reduced rational root a/b has b^d=1 when its
power is integral. That existing denominator theorem now feeds the general
pointwise reduction

IsHit_d(F(n)) ↔ F(n)=0 or RatPower_d(c R_d(n)).

The disjunction is essential. If G_d(n)=0, the original value is zero whether
or not cR_d(n) is a power. If G_d(n)≠0, division of the putative root by
G_d(n) gives the equivalence. The new Lean proof makes this case split
explicitly rather than adding a hidden nonvanishing hypothesis.

For nonzero F, the exceptional set F(n)=0 is finite. Turning that observation
into a bounded discrepancy between hit counts is a separate finite-set
counting step. It should be proved once and reused for radical and Pell
reductions; a pointwise equivalence alone is not an asymptotic theorem.

## 3. A single residual root gives the radical model

Define the bad-root degree by

B_d(F)=∑_{d ∤ j} deg P_j.

Since Q has characteristic zero and the layers are squarefree, this counts the
distinct algebraic roots whose multiplicity is not divisible by d. The formal
invariant is the degree sum; its identification with a roots-in-an-algebraic-
closure profile remains an explicit transport obligation.

If B_d(F)=1, precisely one contributing layer has degree one and all the other
nondivisible layers have degree zero. Monicity turns every degree-zero layer
into 1, and the degree-one layer into X−α for α∈Q. Therefore

F=c(X−α)^rG^d,        0<r<d.

This implication is proved in `ProfileReduction.lean`. It does not assume a
rational root at the outset: the rational root follows from the degree-one
squarefree layer. The finite-sum lemma isolating the unique nonzero summand is
also kernel-checked.

Write α=u/v in reduced form, v>0. For integer F the leading scalar is the
integer c=leadingCoeff(F). Put

K(n)=c v^{d−r}(vn−u)^r ∈ Z.

Then, in Q,

F(n)=K(n)(G(n)/v)^d.

The general integer radical reduction is consequently

IsHit_d(F(n)) ↔ F(n)=0 or IsHit_d(K(n)).

`DenominatorReduction.lean` proves this statement for arbitrary integer F
from B_d(F)=1. All casts and the identity for the leading coefficient are
checked. The rational coefficients of G introduce no extra integrality
condition: rational-power status of the integer K(n) already forces an integer
root. The positive denominator is taken from α itself, rather than chosen
informally after the proof.

The next arithmetic stage studies K(n)=Cz^r, z=vn−u. With
t=d/gcd(r,d), prime valuations restrict admissible nonzero z to a fixed residue
class modulo t in every valuation. After selecting a minimal admissible z_0,
the magnitude takes the form |z|=z_0w^t. The affine condition adds
z≡−u (mod v), and parity supplies the sign condition. These are already
represented in the repository's valuation and count modules, but the complete
signed count must be connected to this general reduction.

The leading constant may be zero because there are no admissible residue
classes. A root multiplicity pattern supplies a candidate growth exponent; it
does not prove that an infinite branch is populated. A final theorem should
state either a finite exceptional hit set or
A(N)=C_F,d N^{1/t}+O(1) with C_F,d>0, and specify the arithmetic criterion
selecting the alternative. The real-power asymptotic conversion is still a
separate Lean task.

## 4. The quadratic residual model and its branches

Suppose d=2e with e>0 and every nonzero residual multiplicity equals e. The
product W of the layers with residue e satisfies R_d=W^e. If their degree sum
is two, W is a monic quadratic and

F=cW^eG^{2e}.

The shape, monicity, and degree assertion are formalized. At an integer n with
F(n)≠0, the exact criterion is

∃γ∈Q : γ^e=c and γW(n) is a rational square.

To prove necessity, write cW(n)^e=y^{2e} and take γ=y²/W(n). Conversely, if
γW(n)=z² and γ^e=c, then cW(n)^e=z^{2e}. The case W(n)=0 is retained in the
F(n)=0 branch. The generic integer-polynomial pointwise statement is
`Decomposition.integer_pell_reduction`.

There may be two coefficient branches. If e is even and c has a nonzero
rational e-th root γ, both γ and −γ qualify. For instance
F=4(X²−2)² is a fourth power exactly when 2(n²−2) or −2(n²−2) is a rational
square. Testing just the positive coefficient root discards the latter branch.
The simultaneous conditions that q and −q are rational squares force q=0;
this overlap assertion is proved. When e is odd there is at most one rational
coefficient root, and when c has no such root only the exceptional zeros
remain. These branch-cardinality statements should be formalized before
summing orbit counts.

A rational square branch must next be converted to an integral quadratic
model. Choose a positive integer L clearing the denominators of the
coefficients of γW. Multiplication by L² preserves rational-square status,
and L²γW has integer coefficients. The integrality theorem then converts the
branch into an integer square equation. Completing the square yields a
norm equation together with its congruence condition; retaining that condition
is necessary for the orbit count to refer to the original indices.

Monic degree two alone is not a Pell asymptotic. One must establish the relevant
nondegeneracy, distinguish the sign and square-discriminant cases, and prove
that a congruence-compatible orbit exists. Empty branches and split norm
models cannot be assigned a positive logarithmic constant. Once these checks
are complete, the existing Pell orbit and exact-count machinery is the right
place to attach the general structural reduction.

## 5. What the density misses

The density A(N)/N loses the distinction between bounded, logarithmic, and
fractional-power growth. A stable replacement for exploration is

α=limsup_{N→∞} log(1+A(N))/log N,  N≥2.

The added one makes the empty and finite cases unambiguous. Power growth with
positive leading constant has exponent 1/t; logarithmic growth and finite
counts both have exponent zero. Thus α alone still does not separate the Pell
and finite regimes. A hierarchy recording power exponent, logarithmic exponent,
and then leading coefficient is more informative, provided every limit is
specified rather than inferred from a small sample.

Finite computations should report exact A(N), scales, and explicitly finite
estimators. They cannot certify completeness without a height or descent
argument. Analytic transforms can discriminate established growth laws, but
an Abelian implication should not be advertised as its Tauberian converse.
The useful next result is a chain from a proved arithmetic parametrization to
a proved count and then to a transform asymptotic, with every direction stated.

## 6. The remaining universal theorem

This continuation closes universal rational decomposition existence, structural
power extraction, and substantial pointwise portions of the radical and Pell
reductions. It does not prove Siegel's theorem, normalization of every
superelliptic component, the root-profile-to-genus bridge, or the complete
counting classification. The existing finite-type theorem still rests on its
named finiteness premise. Changing the coefficient field is not permission to
silently promote that premise to a proof.

A publication should present the structural algebra, arithmetic counts,
geometric finiteness input, and executable certificates as distinct layers of
evidence. The strongest contribution of this continuation is that the first
layer now exists for arbitrary nonzero input and its reductions preserve the
actual integer-hit predicate, including exceptional zeros and coefficient
branches. No priority claim is made for squarefree decomposition or the
classical algebra underlying these reductions.
