# Signed families, exact residue counts and complete optimizer interpretation

This formalization follows the parallel semilinear-capacity push at `3fec118`.
It adds 25 reusable and concrete library statements across `SignedPowerCharts`,
`SemilinearCapacity` and `SemilinearPowerSearch`, plus four checked examples.
The 29 declarations compile in the pinned Lean 4.20.0 environment and use only
standard axioms. The full Python suites run 822 tests: 818 pass and four optional
checks skip. The focused semilinear suite has 34 passing tests. These are separate
checks: the Lean theorems prove mathematics; Python tests exercise the implementation.

## Every sign and every zero

For positive exponents p and q, let g=gcd(p,q), a=p/g and b=q/g. Taking absolute
values of x^p=y^q and cancelling the positive g-th power gives |x|^a=|y|^b.
The already checked coprime-power theorem gives a common integer power parameter;
taking its absolute value produces a nonnegative natural parameter t. Thus

\[
x=s_x t^b,\qquad y=s_y t^a,\qquad s_x,s_y\in\{1,-1\},
\qquad s_x^p=s_y^q.
\]

`gcd_signed_charts` proves exactly this equivalence for every positive p and q.
At t=0 it requires both signs to be positive, assigning the zero point to one
chart. For nonzero t the sign compatibility follows by cancellation of the
nonzero common magnitude. Even original exponents therefore keep negative
coordinate branches; gcd reduction does not justify discarding them.
`shared_offset_charts` applies this theorem to A(x)^p+k=B(y)^q+k with arbitrary
integer coordinate maps. It cancels only the additive offset.

`affine_image` proves that a*x+b=u has an integer solution exactly when a divides
u-b. `affine_fibre` additionally proves the exact coordinate x=(u-b)/a for every
nonzero a, including negative slopes. Nonlinear coordinate maps require a
complete fibre certificate. `fibre_product` proves the Cartesian-product assembly
of two independently complete finite fibres. None of these statements classifies
the global image of an arbitrary nonlinear map as periodic.

## Floor quotients count enormous intervals

For a positive modulus m and normalized residue 0≤r<m, every point with n mod m=r
has exactly a lattice representation n=r+m*k. Its interval inequalities become

\[
\left\lfloor\frac{\ell-1-r}{m}\right\rfloor+1\le k
\le\left\lfloor\frac{h-r}{m}\right\rfloor.
\]

`residue_interval_image` proves the exact finite-set equality, not just a count.
Injectivity of the lattice map then gives `residue_interval_count`: the number of
points is the natural truncation of the difference of those floor quotients.
Integer Euclidean division implements floor division for positive divisors, so
negative endpoints are included. Natural truncation handles empty intervals.
`residue_set_count` adds counts for a finite set of distinct normalized residues,
proving disjointness rather than treating multiplicities as points.

The proof-producing tactic `native_residue_count` handles literal single-residue
counts directly in Lean. It applies the generic theorem and proves its numeric
side conditions and resulting quotient arithmetic. It does not enumerate the
interval or invoke Python. The checked example counts residue 7 modulo 13 across
[-10^30,10^30], obtaining 153846153846153846153846153846 points. A second example
counts residues 0,1,12 in the same interval, obtaining
461538461538461538461538461541 points.

`accepted_rank` proves that an accepted coordinate increases the finite prefix
count by exactly one. This supports a rank specification, but does not certify
the Python binary-search implementation used for rank selection.

## Polynomial residues and Boolean transport

`horner` represents integer polynomials in ascending coefficient order, matching
the software representation. `horner_residue` proves that congruent inputs yield
congruent polynomial values. `horner_period` proves that any multiple of the
modulus is a valid period. Together with the preceding Boolean-cell theorem,
these laws justify reusing modular truth tables inside a cell whose ordinary
sign atoms have already been certified constant. The producer must still justify
those sign cells; general Sturm variation is not proved by these algebraic laws.

## Period steps and infinite-domain minima

For a residue domain the relevant forward difference is f(x+M)-f(x), not always
f(x+1)-f(x). `step_residue` and `period_descent` formalize this move. To certify
candidate completeness on an infinite domain, `global_candidate_bound` requires
an independently proved integer lower bound L and a strict feasible descent
witness for every point outside the candidate predicate. Strong induction on
(f(x)-L).toNat shows that checked candidate values bound every feasible value.
The lower bound can be loose; it is not assumed to be the final optimum.

`global_optimizer_iff` adds an attainment witness and identifies every optimizer
as precisely a feasible candidate at the certified value. `period_optimizer_iff`
assembles the same theorem from left/right period-step witnesses. Strict descent
preserves all ties. Neither theorem assumes the original domain finite.
The remaining obligation is to derive these sign, feasibility and lower-bound
hypotheses from a checked polynomial transcript, including its infinite tails.

The concrete large-translation example minimizes
(x-7*10^30)^2 over x mod 7 in {2,5}. Lean proves that its minimum is 4 and that the
only minimizers are 7*10^30-2 and 7*10^30+2. This is a complete unconditional
example on an infinite disconnected domain, rather than a bounded sample scan.

## Finite sign domains close even-power equations

`SemilinearPowerSearch.complete` proves an additional compiler endpoint. If a
finite set X is proved to be exactly the inputs where F(x)≥0, then every positive
even-exponent solution y^d=F(x) is found by searching X and using the already
proved signed integer-power fibres. Membership in the resulting finite set is
equivalent to the original equation. The theorem needs no additional height bound.
It makes no assertion that every polynomial has a finite nonnegative domain.

For F(x)=3-2x^4, `negative_quartic_domain` proves X={-1,0,1}.
`negative_quartic_packet` kernel-checks the computed square-root packet.
`negative_quartic_complete` proves exactly the four solutions
(-1,-1), (-1,1), (1,-1), (1,1). The generic theorem covers any certified finite
sign domain and any positive even exponent; this one packet is its direct example.

## Reproduction and remaining work

Run `scripts/check_semilinear_capacity.sh` in the pinned Lake environment.
It builds the required small dependency chain sequentially, checks both audit
files, rejects nonstandard axioms and runs the 34 focused Python tests.
`make test` runs the complete four Python suites. The focused script is also
connected to GitHub Actions; successful hosted execution is a separate event.
The full historical heavy Lean build has not been rerun in this push.

The Python outputs retain `execution_verified: false`. General Sturm variation,
normalization/decomposition uniqueness, a generic proof-producing transcript
compiler, the floor-sum and rank-selection algorithms, coefficient-bearing
primitive power charts and global nonlinear parameter-image classification
remain open. The stored 262 transformed curve presentations, 3,080 optimizers
and 676 Bober modular domains retain their Python evidence; this push does not
claim an individual Lean theorem for every stored corpus row.
