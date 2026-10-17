# Periodic Dirichlet families and exact character spectra

This extension turns a finite coefficient table into an entire family of
integrals.  It also supplies an exact bridge between periodic observations,
roots of unity, Mellin kernels, Hurwitz zeta functions, and Dirichlet
characters.  Its purpose is to make these objects computable in one common
coefficient system, so a cancellation found in a finite observation model
automatically becomes a statement about a rational integral kernel and its
periods.  The implementation is
`python/perfectpower/dirichlet_periods.py`; the independent checks are in
`python/tests/test_dirichlet_periods.py`.

The code uses `Fraction`, the existing exact cyclotomic polynomial generator,
and `QuotientAlgebra`.  No symbolic algebra package or floating point
calculation is needed for any identity or equality test.  The optional
`approximate()` method explicitly evaluates an algebraic number in binary64.
Nothing in this note is represented as a new Lean theorem or as a proof of
the higher categorical claims in the motivating visualizations.

## One finite table, three analytic descriptions

Let a rational table be indexed from one through its length:

\[
c=(c_1,\ldots,c_N),\qquad c_{n+N}=c_n,
\qquad D_c(s)=\sum_{n\geq1}\frac{c_n}{n^s}.
\]

The convention matters: the last entry is the value at residue zero.  The
constructor is `PeriodicDirichlet((c1, ..., cN))`; `coefficient(n)` follows
the same convention even at zero and negative integer arguments.  Exact
integers, fractions, and rational strings are accepted.  Floats and booleans
are rejected, so an accidental decimal cannot silently enter a certificate.

Summing a geometric series gives a rational kernel:

\[
K_c(x)=\frac{\sum_{a=1}^{N}c_a x^{a-1}}{1-x^N},
\qquad
D_c(s)=\frac1{\Gamma(s)}\int_0^1
(-\log x)^{s-1}K_c(x)\,dx.
\]

The common absolute convergence region is \(\operatorname{Re}s>1\).
If \(\sum c_a=0\), the numerator also vanishes at one and the apparent pole
in the kernel is removable.  Summation by parts then gives convergence of
the ordinary Dirichlet series for \(\operatorname{Re}s>0\), and the Mellin
integral has the same larger domain.  The removable endpoint value is

\[
K_c(1)=-\frac1N\sum_{a=1}^{N}(a-1)c_a.
\]

The coefficient mean \(\mu=N^{-1}\sum c_a\) is the residue at the possible
pole of the analytic continuation at \(s=1\).  A zero-mean table yields an
entire continuation.  These continuation claims do not turn divergent
ordinary series into convergent ones.  The API reports the ordinary,
absolute, and continued domains separately.

Splitting the sum into residue classes gives

\[
D_c(s)=N^{-s}\sum_{a=1}^{N}c_a\zeta(s,a/N).
\]

The corresponding generating family, initially for \(|z|<1\), is

\[
\sum_{n\geq1}\frac{c_nz^n}{n^s}
=N^{-s}\sum_{a=1}^{N}c_a z^a
\Phi(z^N,s,a/N).
\]

`hurwitz_reduction()` and `lerch_reduction()` return these complete symbolic
reductions, including their scale, residue arguments, and domains.  They do
not claim that an arbitrary Hurwitz or Lerch value is elementary.

## Exact Fourier transport

With \(\zeta_N=e^{2\pi i/N}\), put

\[
b_h=\frac1N\sum_{a=1}^{N}c_a\zeta_N^{-ha},
\qquad 0\leq h<N.
\]

Finite Fourier inversion is exact:

\[
c_n=\sum_{h=0}^{N-1}b_h\zeta_N^{hn},
\qquad
D_c(s)=\sum_{h=0}^{N-1}b_h
\operatorname{Li}_s(\zeta_N^h).
\]

The polylog identity is asserted on the safe common region
\(\operatorname{Re}s>1\).  The code keeps the coefficient \(b_h\) as a
reduced element of \(\mathbb Q[z]/(\Phi_N(z))\), with the specified complex
embedding \(z=e^{2\pi i/N}\).  A packet records the ambient root order,
the cyclotomic polynomial, and the reduced rational coefficients.  The
ambient order need not be the smallest possible field of definition.

`CyclotomicNumber` supports exact sums, products, inverses, integer powers,
conjugation, and changes of ambient field.  For fields of orders \(M\)
and \(N\), arithmetic is performed in the common field of order
\(\operatorname{lcm}(M,N)\).  The embedding sends
\(\zeta_N\) to \(\zeta_L^{L/N}\), so it preserves the specified complex
value.  This reuses the repository's polynomial quotient machinery rather
than relying on rounded comparisons of complex numbers.

## Parity gives algebraic multiples of powers of pi

For a positive integer \(k\), suppose
\(c_{-a}=(-1)^k c_a\).  The two halves of the bilateral Dirichlet sum then
agree.  Combining its Bernoulli Fourier expansion with the exact DFT gives

\[
\boxed{
\frac{D_c(k)}{\pi^k}
=-\frac{(2i)^k}{2k!}
\sum_{h=0}^{N-1}b_h B_k(h/N).
}
\]

All quantities on the right belong to a finite cyclotomic field and are
computed exactly.  The implementation uses an ambient order divisible by
four so that \(i\) has an exact representation.  For weight one, matching
odd parity forces zero mean, and therefore the potentially exceptional
zero Fourier mode vanishes.

This is a general algebraic coefficient, not necessarily a rational one.
For the odd residue pair modulo eight,

\[
\sum_{m\geq0}\left(\frac1{(8m+1)^3}-\frac1{(8m+7)^3}\right)
=\frac{4+3\sqrt2}{256}\pi^3.
\]

The exact coefficient is stored as
\(1/64+3(\zeta_8-\zeta_8^3)/256\), using
\(\sqrt2=\zeta_8+\zeta_8^{-1}\).  Squaring that last algebraic number
returns two by exact polynomial reduction.  `residue_pair(8, 1)` creates
the coefficient table directly.

Opposite parity is deliberately retained as a formal period.  For example,
the beta character modulo four has table \((0,1,0,-1)\) when indexed from
zero, or \((1,0,-1,0)\) under the periodic-series convention.  Its odd
values give

\[
\beta(1)=\frac\pi4,\qquad
\beta(3)=\frac{\pi^3}{32},\qquad
\beta(5)=\frac{5\pi^5}{1536}.
\]

Its even value \(\beta(2)\), Catalan's constant, remains formal.  The API
does not report an invented algebraic multiple of \(\pi^2\), nor does a
formal result assert impossibility of every other kind of expression.

## Full characters, primitive reduction, and Gauss sums

`DirichletCharacter(q, order, exponents)` takes a full table indexed from
zero.  `None` records zero at a nonunit; an integer \(e\) records
\(e^{2\pi i e/\mathrm{order}}\) at a unit.  The constructor checks every
unit pair for multiplicativity and requires the correct support and value
at the identity.  It removes redundant common factors from the root order.
The quartic example modulo five is
`DirichletCharacter(5, 4, (None, 0, 1, 3, 2))`, with \(\chi(2)=i\).
Thus complex characters are supported in full, rather than being replaced
by just the real or quadratic cases.

The conductor is found by testing every divisor \(d\mid q\): the values on
units must depend only on the residue modulo \(d\).  Reduction to the
least such divisor produces the primitive character \(\chi^*\).  Induction
to a larger modulus restores the zeros at the new nonunits.  The Euler
relation is

\[
L(s,\chi)=L(s,\chi^*)
\prod_{p\mid q}\left(1-\frac{\chi^*(p)}{p^s}\right).
\]

Factors at primes already dividing the primitive conductor are one and
are omitted from the stored nontrivial list.  For example, inducing the
beta character from four to twelve removes the multiples of three and
multiplies its cubic value by \(1+3^{-3}\).  The result is
\(L(3,\chi_{12})=7\pi^3/216\).

Gauss sums are computed from the actual finite table:

\[
G_a(\chi)=\sum_{r\bmod q}\chi(r)\zeta_q^{ar}.
\]

The identity
\(G_a(\chi)=\overline{\chi(a)}G_1(\chi)\) holds for every multiplier when
the character is primitive, and for unit multipliers even when it is
imprimitive.  Extending that identity to nonunits of an imprimitive
character would be an error.  The principal character modulo four supplies
an exact counterexample: \(G_1=0\), while \(G_2=-2\).  The implementation
reports the nonunit imprimitive case as inapplicable instead of converting
it into a false equality.

For an independent check on the DFT evaluation, the engine also computes
generalized Bernoulli numbers and the primitive Bernoulli–Gauss formula,
then applies the Euler factors.  Matching-parity results obtained by these
two routes must agree exactly.  Generalized Bernoulli numbers also give
the continued values
\(L(-m,\chi)=-B_{m+1,\chi}/(m+1)\); the method name and note explicitly
identify these as analytic continuation rather than ordinary sums.

`all_characters(q)` enumerates the complete finite character group.  It
extends a character on a subgroup \(H\) through one new generator \(g\).
If \(g^t\) first returns to \(H\), its possible exponents satisfy the exact
finite congruence \(tx=\chi(g^t)\).  Repeating these extensions gives all
\(\varphi(q)\) characters, including noncyclic unit groups.  An explicit
modulus budget prevents an accidental unbounded enumeration.

## Error bounds and computational scope

For a zero-mean rational table, let
\(B_M=\max_{1\leq j\leq N}|\sum_{n=M+1}^{M+j}c_n|\).  Discrete summation
by parts gives, for every positive integer \(k\),

\[
\left|D_c(k)-\sum_{n=1}^{M}\frac{c_n}{n^k}\right|
\leq\frac{B_M}{(M+1)^k}.
\]

This includes conditionally convergent weight-one sums.  A separate
absolute-series bound is available for every table at weights above one;
the engine returns the smaller valid bound.  The partial sum and radius
are rational numbers, so `enclosure()` returns an exact rational interval.

For a complex nonprincipal character, a partial sum is a cyclotomic number
and the tail is enclosed in a complex disk of rational radius.  A prefix
is bounded both by the number of unit values already included and by the
number left in the period.  This conservative triangle bound uses neither
rounded complex magnitudes nor an ordering of a complex number field.

Fourteen tests cover exact field embeddings, DFT inversion for every
period through twelve, rational kernel endpoint cancellation, finite
residue-class grouping, known beta values, the radical coefficient above,
weight-one tail enclosures, complex characters, conductor and Euler
reduction, primitive and imprimitive Gauss scope, analytic continuation,
and invalid-input rejection.  All character tables through modulus sixteen
are enumerated, and the DFT and independent primitive Euler evaluations
are compared at matching weights one through four.  These checks establish
the executable exact arithmetic used in the retained experiments; they
are not a claim of formal kernel verification of this module.

The classical analytic formulas can be checked against the primary NIST
references [DLMF 25.15](https://dlmf.nist.gov/25.15),
[DLMF 25.12](https://dlmf.nist.gov/25.12), and
[DLMF 25.14](https://dlmf.nist.gov/25.14).

## Connection to the broader integral program

Raghava's harmonic cancellation families create controlled combinations
of moments and constants.  The present module supplies a second exact
coordinate system for periodic kernels: the finite coefficient table,
its character/Fourier spectrum, and its Mellin integral are transported
together.  The root-filter identities already present in PerfectPower
compress selected cyclotomic spectra; this extension allows the remaining
coefficients to be genuinely algebraic and supports multiplicative
characters as well as additive phases.  The new mechanism is therefore a
working interface between finite observations and analytic periods.  Its
concrete outputs are identities, exact coefficient packets, and remainder
bounds.  A physical interpretation, an E8 adjoint-lift identification, or
an unspecified higher categorical colimit would each require additional
definitions and proof.
