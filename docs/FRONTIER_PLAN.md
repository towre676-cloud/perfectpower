# Frontier push: Hall, Pillai, and uniform integral-point bounds

## What this push cannot do

**Nothing here proves Hall's conjecture, Pillai's conjecture, or any uniform bound on integral points.** Each of these is a statement about *all* solutions of a Diophantine inequality. The available tools either give bounds far too weak to close the gap, or are themselves unproved:

- **Baker** gives explicit bounds for each fixed equation, but they are astronomical and non-uniform.
- **Siegel** gives finiteness for each fixed equation, but is ineffective.
- **Modular methods** settle specific exponent families only.
- **abc** is open.

Any claim in this repository to have proved Hall, Pillai or a uniform bound should be read as a bug in the reasoning, not as a result.

## What the push does instead

It turns each conjecture into a sharply stated, certified, machine-readable frontier. It also formalises the conditional and function-field statements that *are* provable. There are five deliverables, in order of value per unit effort:

1. **Mordell census for Hall's conjecture.** For every $0<|k|\le K$, list all integral points of $y^2=x^3+k$, from Sage `integral_points` (mwrank generators, saturated, plus elliptic-logarithm sieving). Record the Hall ratio $r=\sqrt{|x|}/|k|$ and the rank. Each row carries a label:
   - *certified by independent computation*, naming the tool, version, and whether the rank was proved;
   - *conditional* on an unproved rank;
   - *scan evidence only*, if the engine failed.

   Lean can check that a listed point satisfies its equation, but **never that a list is complete**. The census validates the pipeline; it is not expected to beat published Hall records, which come from lattice-reduction searches (Elkies, Jiménez Calvo–Herranz–Sáez, Aanderaa–Kristensen–Ruud).
2. **Pillai gap census.** Tabulate all pairs of perfect powers up to a bound $B$ that differ by at most $K$. Pillai's conjecture says this set is finite for each fixed $k$; the census is the empirical set, not a proof. Mihăilescu's theorem settles $k=1$ (Catalan) and is cited, not rescanned; $3^2-2^3=1$ serves as a regression check.
3. **Mason–Stothers and Davenport, formalised unconditionally.** Mathlib provides Mason–Stothers as `Polynomial.abc`. From it we derive Davenport's bound $2\deg(f^3-g^2)\ge\deg f+2$ for coprime $f,g$ over a field of characteristic $0$ with $f$ nonconstant and $f^3\ne g^2$. This is a proven theorem in the shape of Hall.
4. **The abc-conditional layer, formalised.**
   - abc is stated as an explicit *hypothesis* `ABC ε C`, never as an axiom, so the axiom audit stays clean.
   - Proved consequences:
     - Hall's inequality for coprime $(x,y)$;
     - a height bound for $x^a-y^b=k$ that is uniform in the exponents.
   - These are theorems of the form "abc ⇒ …". A future proof or disproof of abc lands on machine-checked consequences.
5. **Uniformity data.** From the census, plot the maximal number of integral points against the rank and against $\log|k|$, in the direction of Lang's conjecture and the Hindry–Silverman theorem. This is labelled **numerical evidence** and proves nothing.

## Out of scope

- **Runge's method for $y^2=x^3+k$.** It does not apply: the curve has a single place at infinity, since $\gcd(2,3)=1$.
- **Our own Baker-bound-to-sieve pipelines.** PARI and Sage already do this, and the explicit bounds are astronomical.
- **Claims of new records.**
