# Crossing the 3-isogeny to find missing Mordell witnesses

## Result

This continuation closes 85 of the 90 constructive Mordell witness gaps left by the binary-invariant release. There are now 452 curves with retained point witnesses matching their rank upper bounds, out of 457 frontier curves. All 457 already had equal external PARI lower and upper rank endpoints. The remaining missing witnesses are on the five rank-one curves k=5935,7482,7823,8210,9454. No integral-point list is promoted, and no complete Mordell-Weil basis or new Lean theorem is claimed.

The longer original-cover search closes three gaps, k=-2558,-4565,-8041. A new alternate route crosses the rational 3-isogeny to E' : v^2=u^3-27k, finds points on its retained quartic covers and sends them back through the dual map. It returns 83 point images on 82 original curves and closes all 82 constructive gaps. This includes k=-9257, where an explicit second point is independent of the existing point (21,2). The original curve now has a witnessed rank-two lower bound matching the retained upper bound two.

The productive partner-cover coordinates are remarkably small: their primitive abscissa heights range from 41 to 26,673, with median 128 across the 83 returned images. These are heights on the retained source quartics, rather than reduced-search charts or original elliptic coordinates. Large coordinates on the original curve do not require large coordinates on every isogenous covering model.

## Why another curve can help

The goal is to retain enough rational points on E_k : y^2=x^3+k to witness its known rank. A rank statement can be available before a practical search finds an explicit point. Changing a covering chart helps, but remains within one particular covering model. An isogeny provides another curve of the same rational rank and additional covering models. Its rational points can be searched first and transported to E_k afterwards.

The rational map has degree three. Its finite kernel means a non-torsion partner point cannot map to torsion: if its image had finite order, a suitable multiple of the source point would lie in the finite kernel, making the source point torsion too. The delivered lower bounds do not rely on this argument alone. Exact rational arithmetic checks the returned original point and constructs its existing good-reduction character certificate on E_k.

Because three is odd, the isogeny is especially compatible with the mod-two witness characters already used by the repository. Composition with the dual is multiplication by three, which is invertible modulo two. The image therefore retains useful mod-two independence information. This explains why the partner route can supply original-curve rank witnesses without requiring a new rank computation or a different independence engine.

## The exact maps

The forward map from E_k to E_{-27k} is u=(x^3+4k)/x^2 and v=y(x^3-8k)/x^3. The normalized dual map is x=(u^3-108k)/(9u^2) and y=v(u^3+216k)/(27u^3). Both maps extend across their finite kernels to the point at infinity. In the rational-point implementation, a point with abscissa zero and the point at infinity return the point at infinity. Nonzero integer k is required so the curve is nonsingular.

The polynomial identity for the forward map is (x^3+k)(x^3-8k)^2-(x^3+4k)^3=-27k*x^6. The dual identity follows with the normalized factors nine and twenty-seven. Exact polynomial arithmetic checks the first identity; independent symbolic tests check both equations and their differential factors. The forward pullback has factor one for dx/y, while the dual pullback has factor three. Tests also compare dual-after-forward with exact multiplication by three, and check additivity on rational examples.

These are morphisms between elliptic curves, not coordinate isomorphisms. A transported point can generate a subgroup of positive index in the original Mordell-Weil group. A matched rank lower bound establishes enough independent directions; it does not identify primitive generators or settle saturation. The output retains this distinction explicitly.

## Composing a covering directly to the original equation

Let a partner cover be z^2=R(t), with partner coordinates u=A(t)/z^2 and v=B(t)/z^3. Its polynomial identity is B^2=A^3-27kR^3. Substituting the dual map gives original-coordinate rational functions X=(A^3-108kR^3)/(9A^2R) and Y=B(A^3+216kR^3)/(27A^3Rz). This produces a direct original-Mordell map from a quartic cover of the partner curve.

The compiler retains the numerator and denominator polynomials separately and checks the denominator-cleared identity in the quotient ring defined by z^2=R. The necessary nonzero factors R and A remain explicit. If a denominator vanishes, this chart cannot be divided through; such a point is handled by the projective isogeny rather than fabricated as an affine point. Original-coordinate integrality is determined after rational reduction, not inferred from integral cover coordinates.

An atlas of 88 such composed maps accompanies the 87-curve partner search. The stored quartics and their maps to the partner are externally discovered, but every map to the stated original curve is checked with exact polynomial arithmetic. Cover completeness is not asserted by this alternate discovery route. Positive points suffice for the constructive rank task.

## Searches and retained evidence

The original-cover continuation uses numerator and denominator height one hundred million, thirty seconds per cover and eight workers. It searches the 91 covers belonging to the 90 then-missing curves and returns three additional witnesses. It appends a fourth round to receipts/quartic_invariants/frontier.json and retains exact original-cover lifts in the corresponding descent packets.

After those original-cover discoveries, the partner search processes 87 curves and 88 covers. Its numerator bound is ten million, denominator bound one million and timeout eight seconds per cover, with four workers. It returns 83 points. Three cover attempts time out and two complete without returning a point. All five unsuccessful cases are the remaining positive-k curves. The partner route has zero processing errors.

A second partner pass on those five curves increases both bounds to one hundred million and the timeout to thirty seconds. All five time out. A bounded Heegner discovery pilot on their rank-one partner curves is also retained. Its initial stack budget is 128 million bytes and twenty seconds; a follow-up uses 512 million bytes and thirty seconds. No checked point is returned by either pilot. Backend failures and timeouts are recorded separately and imply no absence theorem.

Discovery and application are separate phases. The search writes partner-cover points and exact dual images without changing the original descent packets. The application reloads those packets, checks every source covering equation and dual image, then computes original-curve independence. This avoids conflicting updates while the original-cover search is running. Retained image records are deduplicated, so restarting application does not accumulate duplicate source evidence.

## The rank-two curve k=-9257

The existing point is P=(21,2). One newly found dual image is Q with X=662593936756474827892565183374669/28177851863736129061463684312025 and Y=9153824936433195933497442220904296041907428273178/149575968113754601433617765138229764433189140125. Exact substitution checks Y^2=X^3-9257. The retained good-reduction character matrix for P and Q has rank two, while the curve has no rational two-torsion. This gives a free-rank lower bound two, matching the retained upper bound.

The explicit independent pair has its own receipt, rank_two_basis.json. Its complete_basis field is false. A further partner-cover image is retained in the full point list, so that list contains three points spanning two certified directions. Certifying the full list does not require making all three points independent. The application stops halving discovery once its lower bound matches the existing upper bound, avoiding unnecessary very-large-coordinate computations for redundant points.

The historical census assigned rank one to this curve. The newly retained rank-two witnesses bring the point-supported census-rank correction count to twelve, matching the already determined external backend corrections. The original census and the correction evidence remain distinguishable.

## What the five remaining cases mean

The five coefficients are 5935,7482,7823,8210,9454. Each has equal external lower and upper rank endpoints one and no retained non-torsion point sufficient for the constructive ledger. A search timeout leaves discovery unfinished. An empty bounded return excludes only the searched candidates under that operation's stated bounds. Neither result establishes that a cover lacks rational points.

All 457 frontier integral-list obligations remain. Even a complete rank determination does not show that a retained point list is a complete Mordell-Weil basis, and a complete basis alone does not enumerate all integral points. Further saturation and effective height bounds are still needed. This continuation substantially closes constructive rank data while preserving those mathematical tasks.

## Reproduction

Run make check-mordell-three-isogeny for exact map, composition, source-lift, independence and receipt checks. Run the test_mordell*.py suite together with make check-quartic-invariants for the affected arithmetic interfaces. The arithmetic core uses the standard library; independent symbolic tests require SymPy. Large discovery runs require PARI/GP, version 2.15.4 in this release.

Run python/develop_mordell_isogeny_search.py with PYTHONPATH=python and PERFECTPOWER_GP set, or pass --gp explicitly. Its default numerator bound is ten million and timeout eight seconds; use --denominator-max 1000000 to reproduce the successful rectangular pass. After discovery completes, run the same script with --apply-only. The --keys option restricts a continuation to comma-separated original coefficients. Do not apply concurrently with another writer of the same descent packets.

Run python/reconcile_mordell_frontier.py and python/develop_mordell_two_descent.py --effort 3 to refresh the summaries from the retained packets. Existing results are reused. The Heegner pilot is reproducible through python/develop_mordell_heegner.py. It is analytic discovery followed by exact point checking, and does not assert analytic rank.

The reusable interfaces are three_isogeny, isogeny_point, compose_isogeny_cover, partner_covers and augment_isogeny_witnesses in perfectpower.mordell_three_isogeny. Receipts are in receipts/mordell_isogeny_search, with positive original-coordinate evidence in receipts/mordell_two_descent. The previous binary-invariant monograph documents the quartic reduction and primitive chart machinery reused here.

## Primary mathematical context

The degree-three identities and differential factors above are derived directly and tested symbolically in this release. For the surrounding elliptic arithmetic, see the PARI/GP official manual, especially ell2cover, ellrank, ellheegner and isogeny operations: https://pari.math.u-bordeaux.fr/dochtml/html-stable/Elliptic_curves.html. Rational-cover search is documented under hyperellratpoints: https://pari.math.u-bordeaux.fr/dochtml/html-stable/Hyperelliptic_curves.html.

John Cremona, Tom Fisher and Michael Stoll, Minimisation and reduction of 2-, 3- and 4-coverings of elliptic curves, supplies the broader covering-model context: https://arxiv.org/abs/0908.1741. The present combination uses exact invariant contractions, bounded quartic reduction and explicit odd-degree isogeny transport; it does not claim their complete minimisation algorithm.
