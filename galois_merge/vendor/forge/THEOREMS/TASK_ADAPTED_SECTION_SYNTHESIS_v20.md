# Task-adapted section synthesis in the Wilson fiber product — v0.20

## 1. The compiler problem after v0.19

V0.19 identified the synchronized degree-eight word space with a 511-dimensional fiber product inside the 486-dimensional native transport algebra `A` and the 152-dimensional Wilson Hecke algebra `H`.  The coupling code has dimension 127: there are surjective linear maps

`σ_A : A -> F_p^127`, `σ_H : H -> F_p^127`

such that the degree-eight synchronized image is exactly

`B_8 = {(a,h) : σ_A(a)=σ_H(h)}`.

The Hecke kernel has dimension 25.  Degree nine removes the coupling completely: the synchronized language is the full direct product `A x H`.

The next problem is therefore a section problem.  Given a Hecke task subspace `T <= H` and a candidate native radical subspace `S <= A`, determine whether there is a linear section `s:T->S` whose graph lies in `B_8`, and whether the native marginal `s` can be injective.

## 2. Exact degree-eight section criterion

Let `f=σ_H|_T` and `g=σ_A|_S`.  A degree-eight section exists exactly when

`im f <= im g`.

If this holds, a faithful native section exists exactly when

`dim ker g >= dim ker f`.

The necessity is immediate.  A lift must solve `g s=f`, so `im f` must lie inside `im g`; on `ker f`, every lift lands in `ker g`, so an injective lift needs enough kernel dimension.  Conversely choose a complement of `ker f`, lift its image through a right inverse of `g`, and inject `ker f` into `ker g`.  The two pieces have disjoint images modulo `ker g`, giving an injective section.

This criterion is stronger than dimension counting.  The actual position of `σ_H(T)` inside the 127-dimensional coupling code matters.  In particular every one-minus radical has a 75-dimensional signature image and a 100-dimensional Hecke reachability space, yet none of the three one-minus images contains even the distinguished Paley line or the `C3` line.  Rank is only a dimension shadow.

## 3. Pure-radical cost model

A plus arrow contributes five native coordinates and a minus arrow contributes seventy-five.  Thus a radical mask with ranks `(r_+,r_-)` has native coordinate dimension

`5 r_+ + 75 r_-`.

For comparison with the inherited v0.17 dense native product model, its arrow contribution is

`30 r_+ + 1500 r_-`.

These are algebraic coordinate and operation proxies, not measured wall-clock hardware timings.  All v0.20 section optima below are pure-radical, so the 3501-operation semisimple vertex term is absent from the comparison.

## 4. The full 152-dimensional teacher: the old three-minus answer was not optimal

The pure-minus v0.19 calculation proved that two minus arrows expose all 152 Hecke dimensions jointly but leave only a 150-dimensional native marginal, forcing two dimensions of information loss.  It therefore promoted all three minus arrows as the minimum pure-minus faithful encoding.

V0.20 removes the unnecessary `pure-minus` restriction.  Take one plus arrow and two minus arrows.  The radical code has dimension

`5 + 75 + 75 = 155`.

Its coupling signature has full rank 127, hence every Hecke target is reachable.  Its signature kernel has dimension

`155 - 127 = 28`,

while `ker σ_H` has dimension 25.  The section criterion therefore gives

`28 >= 25`,

so a faithful 152-dimensional native section exists already in the mixed stratum

`(r_+,r_-)=(1,2)`.

This stratum is optimal simultaneously for native coordinate dimension and for the inherited arrow-operation proxy among faithful pure-radical encodings of the full teacher.  It uses 155 coordinates instead of 225 for `(0,3)`, a reduction of 70 coordinates or about 31.1 percent.  Its arrow-operation proxy is 3030 rather than 4500, a reduction of 1470 or about 32.7 percent, with the same total number of native channels, three.

The release freezes an explicit good-prime 152-dimensional section in this `(1,2)` code.  This is a linear section, not an algebra embedding; the v0.19 unit-separating quartic still rules out the stronger generator-preserving identification.

## 5. What the current EQ-LAB actually needs

WILSON-EQ-LAB v0.4 has a much smaller deployed linear task family than the full Hecke algebra.  Its trainable one-hop `Q192EquivariantLinear` family is the 8-dimensional spatial span of the identity and seven primitive Q192 routes.  The RS route-consistency and joint-overlap heads use the same seven-route bank after their pointwise feature construction.  The Paley path head uses the signed Paley line, which already lies in the seven-route span.  Adding the frozen depth-five denoising target from the application benchmark gives a 9-dimensional application span.

All of these task spaces have injective coupling signature: their task dimension equals their signature rank.  Therefore once a degree-eight native mask contains their signatures, every lift is automatically faithful.

The exact degree-eight result is unexpectedly rigid.  No one-minus mask and no plus-only mask contains any of the named nonzero task spaces.  Every pair of minus arrows does.  Thus the minimum faithful degree-eight radical schedule for the Paley line, the `C3` line, the seven-route bank, the 8-dimensional learned one-hop family, and the 9-dimensional current application span is uniformly

`(r_+,r_-)=(0,2)`.

It has 150 native coordinates and inherited arrow proxy 3000.  This is not a dimension necessity for the small tasks; it is caused by the 127-dimensional cooperative lock and the relative position of the task signatures inside it.

## 6. One extra word degree changes the optimal ISA completely

At degree nine the synchronized language is `A x H`, so the coupling condition disappears.  A Hecke task of dimension `t` can be paired with any native radical subspace of dimension at least `t`.  Section synthesis becomes pure dimension allocation.

For the one-dimensional Paley and `C3` lines, one plus arrow already supplies five native coordinates.  The minimum section is therefore `(1,0)`, with native dimension 5 and arrow proxy 30.

For the seven-route bank, the 8-dimensional learned one-hop family, and the 9-dimensional application span, one plus arrow is too small but both plus arrows provide ten coordinates.  Thus their minimum coordinate and arithmetic section is `(2,0)`, with native dimension 10 and arrow proxy 60.  The minimum *channel-count* solution is instead one minus arrow, dimension 75 and proxy 1500.  V0.20 therefore exposes an explicit Pareto choice: one expensive wide channel versus two cheap narrow channels.

The full 152-dimensional teacher cannot fit in two minus arrows (150 coordinates), nor in any radical mask with fewer than 152 coordinates.  The mixed `(1,2)` code has 155 and remains optimal even after degree-nine separation.

## 7. Word depth versus runtime section cost

The Hecke target spaces themselves enter the synchronized `X,Y` word filtration at different depths.  The Paley and `C3` lines occur at degree one.  The seven-route bank, identity-plus-seven-route learned family, 9-dimensional application span, and full Hecke algebra all first lie in the `X,Y` word span at degree seven.

Those values are not the same as the depth required to force a target into a chosen native radical stratum.  Pure one-sided radical access begins only at degree eight, and full direct-product independence begins only at degree nine.  The compiler therefore has three distinct depth notions: Hecke expressivity depth, native-stratum access depth, and cross-category decoupling depth.

For the current EQ application, the resulting Pareto front is concrete.  Degree eight gives a coupled but exact two-minus implementation.  Degree nine buys independent addressing and collapses the faithful native application code from 150 coordinates to ten plus coordinates.  The one-degree increase is therefore a potentially enormous runtime-state reduction rather than a small algebraic refinement.

## 8. The hard-negative boundary remains external

The v0.20 section theorem covers Hecke/Q192 observables, including the route-resolved RS hard-negative fixtures in EQ-LAB v0.4.  It does not pull the older Forge projective determinant semi-invariants for `Q2/Q35` and `Q159/Q160` into the native species-3 component.  V0.16 proved that those are object-admission data outside the five-arrow category.  The correct architecture remains

`external canonical-factor / semi-invariant admission gate -> task-adapted fiber-product section -> native execution`.

Thus task synthesis preserves the negative information by keeping it at the boundary where it belongs, not by inventing native coordinates for it.

## 9. Formation v31 and the role of actual subspaces

Formation Polarization v31 is imported byte-for-byte.  Its projective-atom theorem again warns that dimension alone is not the state: one-dimensional full-support lines and their relative projective positions carry the formation-critical information.  Wilson v0.20 exhibits an independent version of the same general principle.  A one-minus native slice has a large 100-dimensional Hecke image, yet it misses the named Paley and `C3` lines at degree eight.  The analogy is lattice-theoretic only; no functor between the formation and Wilson categories is asserted.

## 10. What remains open

Structural section synthesis is now solved for the current tasks under the frozen degree/channel/native-coordinate/arrow-cost objectives.  Arithmetic coefficient height is not yet honestly optimized.  The coupling signatures and explicit sections are frozen over the certified good prime.  Their centered modular coefficients are coordinate-dependent and are not characteristic-zero height invariants.  The next arithmetic compiler problem is to lift the degree-eight fiber product and its task sections to a controlled rational or integral model, then minimize numerator/denominator height and shared word support without changing the already-proved depth and native-stratum optima.

Machine certificates are in `DATA/RELATION/TASK_ADAPTED_SECTIONS_V20/`; the reproducer is `scripts/analyze_task_adapted_sections_v20.py`.
