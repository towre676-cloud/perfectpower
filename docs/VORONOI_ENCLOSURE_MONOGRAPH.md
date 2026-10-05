# From numerical Voronoi proposals to reusable exact surface queries

PerfectPower's surface work had two distinct achievements: numerical geometry of
branched algebraic curves, and rational distance bounds on a specified finite
polyhedral surface. This push makes the latter easier to consume and audit. A
producer emits explicit witnesses. A separate checker accepts those witnesses
without running the producer, a heat equation, or shortest-path optimization.
A reusable `SurfaceSpace` then answers distance and nearest-site questions at
arbitrary rational face points. Lean proves the reusable coverage, chain,
convexity and metric-transfer statements behind this design.

The distinction between the represented surface and the original curve remains
essential. Decimal edge lengths are interpreted as exact rationals. They define
a genuine piecewise Euclidean metric after nondegeneracy and gluing checks.
They are not certified measurements of the smooth curve's conformal metric.
The new transfer theorem describes precisely the additional comparison needed;
this release does not manufacture that comparison from numerical quadrature.

## What the independent checker accepts

The input mesh contains vertex indices, triangle indices, positive rational edge
lengths, and optionally explicit face orientation signs. The checker rejects
duplicate edges, duplicate triangles, missing or unused edges, nonpositive
lengths, and triangles whose exact Gram determinant is not positive. Every edge
must occur twice with opposite oriented directions. Every vertex link must be
one connected cycle, and the entire edge graph must be connected. Existing
analytic meshes retain their triangle coordinate order: their separately stored
orientation signs are used for incidence checks, without changing barycentric
coordinates. A face with the opposite numerical orientation is not silently
reordered and mistaken for the old face.

The packet contains rational vertex fields, one explicit edge path from each
site to each vertex, and addressed patch leaves. Fields may originate in a heat
solver or any other proposal mechanism. Their origin is irrelevant to acceptance.
For each triangle with squared edge Gram matrix

\[
G=\begin{pmatrix}A&C\\ C&B\end{pmatrix},\qquad D=AB-C^2>0,
\]

the checker verifies

\[
B u^2-2Cuv+A v^2\le D,
\qquad u=f(b)-f(a),\quad v=f(c)-f(a).
\]

This is the affine gradient condition for a local Lipschitz constant at most
one. The common vertex values make the affine readouts agree on shared edges.
Piecewise affine continuity and segmentwise Lipschitz control give a global
lower-distance witness on the polyhedral length metric. The Lean chain theorem
makes the distance-approximation hypothesis explicit; the actual quotient
surface construction and its correspondence with this JSON mesh are not yet
formalized.

The path witnesses need not be shortest paths. Every recorded vertex sequence
must start at its designated site and end at the designated target, and every
step must be a real mesh edge. Summing its exact lengths gives an upper bound.
The producer happens to choose paths with Dijkstra; the checker never invokes
Dijkstra. A different producer can use any admissible paths with at most the
number of mesh vertices recorded in a witness. This budget admits the simple
paths selected by the present producer without introducing a completeness claim
for arbitrary encodings of longer paths.

## Pointwise distance brackets

For a point p inside a triangle, each path to a corner can be followed by the
straight in-face segment to p. The best supplied such path gives an upper bound.
Every accepted field gives a lower bound. The bracket is

\[
\max_f |f(p)-f(s)|\le d(p,s)
\le\min_{v\text{ a corner}}\bigl(\operatorname{length}(\gamma_{s,v})
+\|p-v\|_G\bigr).
\]

Square roots are rounded outward with integer arithmetic. The packet stores
upper bounds rounded upward and lower bounds rounded downward to a 32-bit binary
grid. This shortens the packets substantially; the checker compares these
compact bounds against its own exact witness calculations. If outward rounding
would destroy a strict patch separation, the producer retains the patch as
unresolved. Compression never justifies a stronger classification.

`SurfaceSpace` checks a packet once and retains immutable rational field, path
cost and triangle data. Its `point(face, barycentric)` method accepts exactly
three nonnegative rational coordinates summing to one. It returns all site
brackets, a strict winner when one is proved, and all sites still compatible
with nearest-site status. A site remains possible when its lower bound is no
greater than the smallest upper bound. An absent strict winner expresses
insufficient information, and does not assert an actual equal-distance tie.
Returned lists are fresh values and cannot alter the stored witnesses.

## Why area totals are insufficient

A sum of area fractions equal to one can hide a missing patch balanced by a
repeated patch. The new checker uses a prefix tree. Each face starts with the
whole barycentric triangle. Each refinement replaces a patch by its four
midpoint children, indexed zero through three. A packet leaf carries its exact
address and barycentric vertices. The checker reconstructs those vertices,
checks its area fraction is exactly \(4^{-k}\), and recursively establishes that
every unassigned internal node has all four covered children. Duplicate leaves,
missing children and parent/descendant overlap are rejected.

Lean's `midpoint_cover` proves actual geometric coverage: every nonnegative
barycentric triple summing to one is in some midpoint child. If a parent
coordinate is at least one half, the corresponding corner child contains the
point. Otherwise the three central-child weights are nonnegative. Their sum
and reconstructed coordinates are proved exactly. This proof concerns points,
rather than only a conservation-of-area identity.

A patch center has a rational upper radius covering its three corners. The
norm's convexity covers all points of that patch. For a proposed winner s,

\[
U_s(p)+2r<L_t(p)\qquad\text{for every }t\ne s
\]

implies strict preference for s throughout the patch. Distance ties therefore
cannot occur in a classified leaf. Lean's `boundary_coverage` assembles this
argument for a covering family: any point having two distinct equally nearest
site indices lies in an unresolved patch. It does not incorrectly treat equality
between two non-nearest sites as a Voronoi boundary. Strict winners are unique,
even in the more general setting of a pseudometric space.

## The smooth-metric bridge

Suppose a map \(\phi\) from the mesh surface to a smooth surface has globally
proved distance comparison factors \(0<l\le u\):

\[
l\,d_M(x,y)\le d_S(\phi(x),\phi(y))\le u\,d_M(x,y).
\]

Then lower site bounds transfer by l, and upper site bounds and patch radii
transfer by u. The correct sufficient separation becomes

\[
uU_s(p)+2ur<lL_t(p).
\]

`transferred_winner` proves this statement for two pseudometric spaces and an
explicit map. `transfer_piece` computes the associated conditional classification
in Python. It always reports `comparison_proved: false`: factors supplied by a
caller are assumptions, and are not evidence that any curve satisfies them.
Coverage of the intended smooth surface would additionally require that the map
covers that surface. No surjectivity or topology identification is inferred from
the distance comparison theorem alone.

The saved comparisons at exact equality, one percent distortion and ten percent
distortion measure how many existing patch margins would survive these
hypotheses. They are sensitivity calculations, not analytic certifications.
To establish actual comparison factors, the next geometry push needs validated
roots and sheets, enclosed metric tensors, compatible finite/branch/infinity
charts and a proved global geometric correspondence. For a canonical Bergman
metric it also needs enclosed period normalization. None follows merely from
observed agreement of numerical period matrices.

## Lean coverage and its limits

The module `PerfectPower/VoronoiEnclosure.lean` adds fourteen reusable theorems.
Checked local field differences bound a whole chain, and chains whose costs
approximate metric distance yield a global field bound. Shared-edge readouts,
field lower bounds, nearest-tie coverage, radius transfer, strict-winner transfer,
midpoint interpolation, area preservation, winner uniqueness, actual midpoint
coverage and convex radius control are included. An adaptive-tree theorem propagates geometric coverage through every refinement level. Three examples exercise the
chain interpretation, the central subdivision point and the transferred winner
on the real line. The dedicated audit checks all seventeen declarations and
permits only `propext`, `Classical.choice` and `Quot.sound`.

These are reusable mathematical proofs, not a kernel proof of the Python
checker. The current packets are independently replayed in exact Python
arithmetic. Kernel-checked packet ingestion, construction of the polyhedral
quotient length metric, a formal shortest-path producer and identification with
an analytic curve remain separate obligations. The earlier triangle-gradient
and local patch theorems are preserved; this module connects more of the
reasoning while keeping the remaining semantic bridge visible.

## Reproduction and evidence

Run `PYTHONPATH=python python python/develop_voronoi_witness.py` to construct and
independently replay the three saved genus-two/genus-three surface packets.
The inputs are the already committed curve meshes and heat proposals. Packet
hashes, compressed sizes, face-fraction totals, conditional sensitivity and
reusable query statistics are stored in `receipts/voronoi_witness/summary.json`.
Face-fraction sums are sums relative to individual faces, not physical areas:
unequal triangle areas must not be silently treated as equal surface area.

The focused suite tests producer independence, exact coverage, overlaps,
modified path endpoints, false gradient bounds, invalid topology, altered site
bounds, false smooth certification flags, conservative witness freedom and
repeated queries. An independent regular-tetrahedron calculation checks point
brackets against Euclidean chords. The full existing Python suite is run as a
regression check. `scripts/check_voronoi_enclosure.sh` compiles the new Lean
module, checks the seventeen axiom reports and runs the focused tests. It is wired
into the existing Lean workflow; that change does not assert that the account's
runner availability problem has been resolved. The historical heavy Lean
library is not rebuilt as part of this focused push.

The CLI accepts local JSON files directly. `voronoi-witness --mesh mesh.json
--fields fields.json --sites '[0,1]' --depth 2 --verify` constructs a packet.
`voronoi-check --mesh mesh.json --certificate packet.json` checks it and exits
with a nonzero status on rejection. These commands require no numerical heat
solver dependencies when the mesh and proposals are supplied.

This release gives the geometry branch a concrete reusable contract: provide a
closed rational polyhedral surface and site witnesses, obtain conservative
boundary enclosures and point queries, and retain the precise additional
hypotheses needed to move to a smooth curve. General Sturm verification remains
a separate arithmetic front; this push does not claim to have completed it.

The recorded run accepts 11,520 enclosure leaves and checks 12,864 point queries
across 3,216 faces. The three stored surfaces have 172, 395 and 525/2 assigned
face-fraction units, respectively, leaving 884, 661 and 1683/2 unresolved.
At assumed one-percent distance distortion the retained assigned sums are 156,
711/2 and 248. These figures describe conservative classification margins.
The full regression run has 924 tests: 920 pass and four optional tests skip.
All thirteen focused tests pass, and all seventeen Lean audit entries contain
only standard axioms. The packets together occupy about 1.14 MB compressed.
