# Coefficient charts, reusable integer images and recurrence solution domains

This push extends PerfectPower's queryable solution-space machinery in three
connected directions. Coefficient-bearing power relations now produce primitive
signed charts. Compiled curve objects retain those charts across repeated counts,
restrictions and optimizer queries. Modular polynomial-coefficient recurrences
produce finite-state orbits whose hit sets support large-range counting, rank
selection and global polynomial index optimization. Integer fibres can be reused
across chart signs, nested generators and repeated parameter evaluations.

The Python core still requires only the standard library. The accompanying Lean
layer checks 19 declarations, including a general coprime coefficient-power
completeness theorem with explicit primitive hypotheses, the whole family
2x²=3y³, and actual modular recurrence examples. These results do not promote
whole Python execution into a Lean proof-producing compiler.

## Primitive coefficient-bearing families

Consider cX^p=dY^q with nonzero integer c,d and positive p,q. Let g=gcd(p,q),
a=p/g and b=q/g. At each prime l, a nonzero solution has valuations u,v satisfying

\[
p u-q v=v_l(|d|)-v_l(|c|)=\delta_l.
\]

If g does not divide delta at even one prime, there are no nonzero solutions.
The zero pair remains a solution; an obstruction must not erase it. When the
condition holds, a and b are coprime. The program solves a*u-b*v=delta/g using a
modular inverse, then shifts both exponents to a nonnegative primitive pair
(u0,v0). Primitivity means u0<b or v0<a. Every other nonnegative solution is

\[
u=u_0+b k,\qquad v=v_0+a k,\qquad k\ge0.
\]

The prime exponent k contributes to a common natural parameter t. For primes
outside the coefficient support, both primitive exponents are zero. Multiplying
the coefficient-supported primitive powers gives positive scales alpha,beta and
all nonzero magnitudes

\[
|X|=\alpha t^b,\qquad |Y|=\beta t^a,\qquad t\ge1.
\]

The finite sign table retains exactly the signs satisfying
sign(c)*sx^p=sign(d)*sy^q. A separate chart at t=0 contains the zero magnitudes.
This convention makes counting charts disjoint for explicit affine coordinates.
The absence of compatible nonzero signs can also leave only the zero fibre.

`primitive_power_charts` returns coefficient factorizations, primitive valuation
rows, scales, signs and any obstruction. The coefficient factorization uses
bounded trial division. A budget failure raises `WorkLimit`; it does not issue
an incomplete chart as complete. Default budgets allow 100,000 trial candidates
per coefficient, coefficients up to 4,096 bits, primitive scales up to 16,384
bits and exponents from 1 through 64. Evaluation also bounds output bit size.
This is exact bounded coefficient arithmetic, not a new fast general factoring
algorithm.

## Polynomial entry points and original integer images

`coefficient_presentations` recognizes expanded identities F(x)=c*A(x)^p+k.
It extracts the p-th-power-free part of the leading coefficient and recovers the
candidate integral coordinate through exact triangular coefficient equations.
Substitution checks every proposed identity. The constructor does not claim to
find every conceivable rational coordinate presentation.

When the existing unscaled shared-offset recognizer has no presentation,
`parameterize_relation` now tries the coefficient route. Therefore `curve-query`,
`polynomial-charts`, generator evaluation and the arithmetic engine can use the
new charts without a separate query language. Existing complete unscaled routes
remain first in the dispatcher. The resulting evidence identifies the coefficient
schema and retains `execution_verified: false`.

Affine A(x)=a*x+b gives x=(sx*alpha*t^b-b)/a, with the indispensable divisibility
condition. Negative affine slopes are handled by positive denominator normalization.
A nonlinear coordinate gives complete integer fibres at each parameter, and its
global parameter image can remain unresolved. The zero chart gets its own fibre
search. This distinction was important in integration: treating its constant
zero target as an ordinary two-nonconstant-polynomial relation was invalid.

For example, 2x²=3y³ has scales alpha=18, beta=6 and reduced steps 3 and 2.
Its points are x=±18t³, y=6t², t≥1, together with (0,0). Restricting y≤6T² gives
exactly 2T+1 points. The saved T=10^40 query returns
20000000000000000000000000000000000000001 without scanning the box. On the
nonzero domain y>0, minimizing x²+y² gives value 360 at exactly (-18,6) and (18,6).

The existing SMT simplifier also consumes the new charts. With 2x²=3y³,
x<0 and 0<y≤600, it emits the linear integer domain 1≤t≤10. Its model recovery
returns (-144,24) at t=2 and rejects parameters outside that domain. This is an
automatic existing-adapter integration, not an additional caller-managed route.

## Compile once and reuse fibres

`CurveSpace(left,right)` stores a compiled generator in an isolated serialized
representation. Its `query` method applies new side predicates, objectives and
budgets to that representation. Returned evidence is independently mutable and
does not change the stored generator. Counts and optimizer results retain the
same original-coordinate semantics as `query_curve`.

`IntegerImageIndex` stores complete replayable root certificates keyed by the
normalized polynomial and target. `points(T,u)` returns every integer solution
of T(x)=u. Cache outputs are copied, so altering a returned root list cannot
corrupt later queries. `evaluate_parameterization` and `family_points` accept
an optional image index, and `CurveSpace.evaluate` owns one automatically.
The cache is bounded and evicts old entries at capacity. A cached transcript
that exceeds a new caller's node budget still fails that budget.

Reuse avoids root discovery and replay construction, while certificate node
accounting keeps its previous logical meaning. The saved experiment asks for
32 quadratic fibres three times. It constructs 32 certificates with 590 total
nodes and records 64 cache hits. Every root list agrees with a separate literal
integer scan. This establishes reuse and exact agreement; it is not a claim of
industrial speed superiority.

```python
from perfectpower.query_space import CurveSpace

space = CurveSpace([0, 0, 2], [0, 0, 0, 3])
count = space.query({"expr": "y-600", "relation": "<="}, point_limit=0)
optimum = space.query({"expr": "y", "relation": ">"}, objective="x*x+y*y")
assert count["solution_count"] == 21
assert optimum["optimization"]["optimizer_points"] == [(-18, 6), (18, 6)]
```

## Recurrence dynamics as finite exact state spaces

For Q(n)*A(n+1)=P(n)*A(n) modulo m, polynomial coefficient values repeat modulo m.
The correct state is (n mod m,A(n) mod m). Retaining the index phase prevents a
repeated sequence value from being mistaken for a complete repeated state.
When gcd(Q(n),m)=1, the next value is unique. A repeated full state proves an
exact eventual period, including any transient prefix.

`recurrence_orbit` computes this deterministic finite state sequence. The state
budget defaults to 100,000 and the modulus is bounded by 65,536. If the budget
ends before a repeated state or singular coefficient, it raises `WorkLimit`.
The method does not silently classify a truncated exploration as periodic.

At a singular denominator q, solve q*z=rhs modulo m directly. If h=gcd(q,m)
does not divide rhs, there are no successors. Otherwise the exact successor set
is the compact arithmetic progression base+j*(m/h), 0≤j<h. The deterministic
orbit stops there, returning this congruence and its known prefix. It does not
choose one branch or replace a nonunit by an invalid modular inverse. Global
rank selection and optimization require a closed orbit; counts beyond a singular
prefix are rejected.

`orbit_domain` selects a residue set or the d-th-power residues of the sequence
value. It returns disjoint finite prefix cells and a periodic tail in the same
interval/residue representation used by the arithmetic query machinery.
`orbit_count` and `orbit_select` reuse floor-counting and rank selection.
`orbit_optimize` uses period-step polynomial differences and retains all tied
index minimizers. Constant, empty and unbounded objectives keep their explicit
meanings.

These are exact statements about a modular recurrence. Passing a power-residue
filter is a necessary local condition for an integer perfect power, not a proof
that the integer sequence value is a perfect power. Applying the modular sequence
to a particular integer sequence also requires that sequence's recurrence and
initial value to agree. No integrality of arbitrary rational hypergeometric terms
is inferred from a modular orbit.

The saved variable-coefficient example has P(n)=n²+3, Q(n)=n²+n+1, modulus 8 and
initial value 1. Q is always odd, so the orbit closes after a four-state prefix
with period eight. Its square-residue hit set contains all nonnegative indices
except index 1. The count through 10^100 is exactly 10^100 and the zero-based
selected hit of rank 10^100 is index 10^100+1.

## Lean theorem map and its scope

`CoefficientPowerCharts.valuation_balance` proves the exact prime-exponent equation
for nonzero natural coefficients and coordinates. `valuation_gcd` proves the
necessary gcd divisibility. `exponent_line` uses Bézout to obtain the complete
integer line; `primitive_row` proves its free exponent is nonnegative under the
primitive row condition. `chart_sound` verifies the original equation for every
parameter whenever its scale identity holds.

`coprime_complete` goes further. For coprime positive exponents and nonzero scales
with c*alpha^p=d*beta^q, it assumes the explicit primitive denominator condition:
if n^q divides alpha and n^p divides beta, then n=1. Normalizing a solution by
alpha,beta gives a coprime power relation over the rationals. Rational denominator
powers divide the integer scales, and the primitive condition forces denominator
one. This proves the full integer parameter equivalence. The theorem
`two_square_three_cube` discharges these hypotheses for (c,d,alpha,beta,p,q)=
(2,3,18,6,2,3), proving the complete infinite family directly.

`RecurrenceDomains.unit_step` proves unique next-value transport over any
commutative ring with a supplied unit denominator. `repeat_future` proves that a
checked repeated deterministic state repeats at every future offset. Numeric
readouts and hit predicates inherit that period. The remaining library statements
retain the index phase, characterize a zero denominator and compose complete
image fibres with readouts.

Five example theorems prove two singular transitions modulo 6 and the actual
phase/value doubling recurrence modulo 7. One singular equation has exactly two
successors; another has none. A closed iterate formula proves the whole state
returns after 21 steps, and every hit predicate inherits that cycle.
All 19 declarations pass the standard-axiom audit. The Python chart producer,
coefficient factoring, general noncoprime completeness assembly, arbitrary stored
orbit transcripts and cache implementation are not all certified in Lean.
General Sturm variation and whole-compiler proof emission remain separate work.

## Evidence and reproduction

The constructed coefficient corpus uses signed coefficients from ±1 through ±8
and exponents 2 through 5, for 4,096 cases. An independent bounded integer scan
checks 2,560,000 original-coordinate pairs and agrees with every generated family.
The recurrence corpus has 720 coefficient/modulus/seed cases: 344 close with a
period and 376 meet a singular denominator. Literal polynomial evaluation and
exhaustive next-value enumeration check 105,248 transitions; every bounded hit
count agrees. These defined mathematical workloads do not establish recognition
coverage or speedup on external industrial problems.

The focused suite has 18 passing tests; the earlier 34 semilinear tests also pass.
After preserving the parallel flavor-completion push, the four full Python suites run 891 tests: 887 pass and four optional checks skip.
Run `scripts/check_query_space.sh` for the Lean audit and focused tests,
`PYTHONPATH=python python python/develop_query_space.py` for the saved corpus,
and `make test` for the full Python suite. The focused Lean audit is connected
to GitHub Actions. The full historical heavy Lean build was not rerun here.

```sh
python -m perfectpower coefficient-charts --c 2 --p 2 --d 3 --q 3 --verify
python -m perfectpower curve-query --left '[0,0,2]' --right '[0,0,0,3]' --predicate '{"expr":"y","relation":">"}' --objective 'x*x+y*y' --verify
python -m perfectpower recurrence-orbit --p '[3,0,1]' --q '[1,1,1]' --modulus 8 --seed 1 --through 1000000000000 --rank 1000000000000 --verify
```
