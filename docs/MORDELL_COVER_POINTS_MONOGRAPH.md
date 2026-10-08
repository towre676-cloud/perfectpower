# Smaller-height covers and exact Mordell rank witnesses

Searching the retained two-descent covers closes 76 of the 168 previously unresolved rank intervals. The committed frontier now has 365 exact ranks: 352 of rank one and thirteen of rank two. Ninety-one curves still have upper rank one without a retained non-torsion witness, and k=-9257 retains the interval one to two. The universal rank upper bounds from the preceding release are unchanged.

The first pass uses cover abscissa height at most one million and closes 56 rank gaps. A second pass at ten million closes another twenty. Every positive result retains quartic coordinates, rational Mordell coordinates, homogeneous integer coordinates, and an exact independence certificate. All 76 new points are nonintegral. No integral-point list becomes complete merely because its rank is now known.

## Why the covering chart changes the search

Write the original curve as E: Y²=X³+k. A retained cover has z²=R(t), with degree R at most four, and polynomials Nx and Ny of degrees at most four and six. Its map is X=Nx(t)/z² and Y=Ny(t)/z³. Exact polynomial arithmetic checks Ny²=Nx³+k R³. The chart excludes z=0 explicitly.

A rational point can have enormous original-coordinate numerators while having a modest abscissa on this quartic. Searching E and searching a covering curve impose different effective height budgets. This release uses models already produced by descent, avoiding a fresh Selmer calculation for each attempt. Their smaller coordinates make the covers constructive tools for finding points.

For k=-1345 the cover is R(t)=5t⁴+60t³-8t-24. A point has t=48629/58441 and z=8578610447/3415350481. Its original coordinates are X=9881537680280463146909/73592557201377539809 and Y=-982010472581562242316088638859882/631321880029182445796645784623. Searching original-coordinate numerators with the same budget would miss this point by many orders of magnitude.

This does not solve the local-to-global problem for every Selmer class. An everywhere locally soluble cover may lack a rational point. An unsuccessful finite search cannot prove this absence. Only an exactly checked positive point contributes to a rank improvement. Attempts distinguish a returned point, no point returned, a timeout, and an exceptional zero ordinate.

## The homogeneous integer lift

Let t=u/v in lowest terms, with v positive. For an integral quartic define R_h(u,v)=v⁴R(u/v). The rational ordinate satisfies (zv²)²=R_h(u,v), an integer. A rational number whose square is an integer is itself an integer: a reduced denominator would have to divide a coprime numerator. Thus w=zv² is an integer and w²=R_h(u,v).

These are weighted homogeneous coordinates: u and v have weight one, while w has weight two. Replacing (u,v,w) by (cu,cv,c²w) preserves the rational point. The implementation fixes the primitive abscissa and positive v, retains both signs of w, and requires w nonzero on the affine Mordell map.

Choose a positive integer D such that D²Nx and D³Ny have integer coefficients. Every committed cover needs only D=1 or D=2: the possible denominators in Nx are 1,2,4, and in Ny are 1,2,4,8. The general routine also handles larger rational denominators using their least common multiple when necessary.

Define A=D²v⁴Nx(u/v) and B=D³v⁶Ny(u/v). Both are integers. Homogenizing the polynomial identity gives B²=A³+D⁶k w⁶. The original coordinates are X=A/(D²w²) and Y=B/(D³w³). This is an exact integer equation with an explicit rational reverse map.

The target is integral precisely when D²w² divides A and D³w³ divides B. For integer k, the first condition implies the second: integral X makes Y²=X³+k integral, and a rational square root of an integer has denominator one. Retaining both conditions makes the signed-coordinate reconstruction explicit.

For the k=-1345 example the integer coordinates are (48629,58441,8578610447), with D=1. The values of A and B are its displayed original-coordinate numerators. The identity B²=A³-1345w⁶ holds exactly. The divisibility conditions fail, so this is a rank witness rather than an integral point. The distinction is part of the chart itself.

## Height distortion

Suppose max(|u|,v) is at most H. Let C_R, C_x and C_y be the sums of absolute coefficient values of R, Nx and Ny respectively. Termwise bounds give |w|² at most C_R H⁴, |A| at most D²C_x H⁴, and |B| at most D³C_y H⁶. These algebraic bounds require no numerical periods.

After reducing the original fractions, their naive heights are at most D²max(C_x,C_R)H⁴ for X and D³max(C_y,C_R^(3/2))H⁶ for Y. Cancellation can reduce these heights but cannot invalidate the envelope. A moderately larger covering-chart search can therefore reach points far beyond a direct search on E.

A cover-height bound controls a finite candidate set; it does not establish that all integral points lie within it. Complete Mordell-Weil basis construction, saturation and an effective global bound remain separate. The homogeneous chart exposes the correct finite arithmetic domain once a sufficient bound is available.

## From a point to an exact rank

All 457 frontier curves have rational two-torsion dimension zero. The previous cubic-field descent and Cassels pairing supply an upper bound of one or two. New positive points supply a lower bound through exact good-reduction characters and rational halving.

The character matrix detects classes modulo twice the rational point group. With no rational two-torsion, a nonzero class cannot arise from torsion: odd-order torsion is itself twice another torsion point. A nonzero witnessed class therefore gives positive free rank. Rational halving handles a point initially lying in twice the group while retaining exact coordinates.

Each of the 76 new results has lower bound one matching upper bound one, hence rank exactly one. No analytic-rank estimate or finiteness assumption for the Tate-Shafarevich group enters these closures. A bounded Heegner pilot supplied no witnesses; the productive construction was rational search on stored quartics.

## Reproduction and remaining work

Install PARI/GP or set PERFECTPOWER_GP to its executable. Run develop_mordell_cover_search.py with --height 1000000, then again with --height 10000000. The second pass here used eight workers and twelve seconds per cover. It has 93 timed-out cover attempts; a timeout is an unfinished search, not an insolubility theorem. Results can vary with the time budget.

The runner retains cumulative rounds, updates only exactly lifted positive witnesses and preserves every descent upper bound. Run develop_mordell_two_descent.py with --effort 3 to reassemble the summary from stored packets, then reconcile_mordell_frontier.py to update the census view. The historical census rank and all integral-list obligations remain explicit. Run make check-mordell-cover-points for the lift and rank checks.

The remaining 92 intervals are a narrower frontier. Cover reduction or higher-height search may supply more witnesses. The k=-9257 case needs a second independent point or a sharper upper bound. Complete bases, saturation termination, integral-list completeness and Lean descent refinement remain further work.

## Sources

PARI's official hyperelliptic documentation defines rational-point search and its height parameter: https://pari.math.u-bordeaux.fr/dochtml/html-stable/Hyperelliptic_curves.html. Its elliptic documentation describes covering maps and descent: https://pari.math.u-bordeaux.fr/dochtml/html-stable/Elliptic_curves.html. The preceding construction is in docs/MORDELL_TWO_DESCENT_MONOGRAPH.md.
