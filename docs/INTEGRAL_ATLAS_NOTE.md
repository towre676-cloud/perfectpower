# Spectral Atlas: what the pictures actually mean

The geometric atlas at `/integrals/atlas.html` offers four linked mathematical views. The previous
exact calculators remain at `/integrals/calculator.html`. The mathematical
account remains the [deep monograph](PERIOD_BRIDGE_DEEP_MONOGRAPH.md), with
the [PDF](PERIOD_BRIDGE_DEEP_MONOGRAPH.pdf) and all prior receipts retained.

The E8 scene is a geometric projection of the actual root vectors exported
by `e8_periods.roots()`. A root is stored in doubled Euclidean coordinates;
dividing its eight integers by two gives a vector of squared length two.
Edges incident to the selected root have inner product one, giving exactly
56 neighbors. Each of the eight Coxeter orbits contains 30 distinct roots.
The projection uses Fourier exponent one along the exact Coxeter action.
Its optional depth coordinate is the real exponent-seven component.
Normalization and rotation are display operations, not new exact claims.

The phase scene computes the actual integer exponents `1 + 1680*j`, for
`0 <= j < 264`. Coprimality with 443520 marks the 240 primitive inputs and
the 24 inputs of conductor 40320. Integer power maps use the residue of
`power*exponent` modulo 443520 and retain multiplicities of coincident
images. Filtering is applied to the original inputs. At power 264 all
branches return to q. These branches are not identified with E8 roots.

The Raghava scene draws positive summands of the arcsine moment family on
a logarithmic scale relative to its exact sum. The selected coefficient of
pi is computed with the existing BigInt rational engine. In particular,
changing the denominator from 840 to 221760 multiplies the exact value by
264 to the power minus twice the moment order. Plotting uses floating point.

The Mellin scene follows the root-cycle and Cartan contributions. Its
balance coordinate is `log2(root_term / abs(cartan_term))`, so height zero
means equal magnitudes, with no visual subtraction of differently scaled
bars. The normalized integral coefficient is computed exactly at integer
weights. For B and C the rank tuner chooses `n = 2^(k-1)-1`. The density
view substitutes `t = -log(x)` in the raw integral and includes the
Jacobian `exp(-t)`; the displayed sample interval starts at positive t.

The user can inspect roots by direct selection or by native orbit and step
controls, rotate the projection by dragging, pause the orbit animation, and
export the current diagram as SVG with state and source identity. The archived geometric atlas has
no animation on first load. Changing chapters pauses playback. Reduced-motion
preferences never trigger automatic motion. Narrow layouts stack controls
and reflow the chapter navigation; diagrams use their measured container size.

`python/export_integral_atlas.py` regenerates the source-bound geometry.
`node python/tests/test_integral_atlas.cjs` checks the shipped display model,
its exact comparisons, and source identities. The existing 330 browser
arithmetic comparisons remain applicable to the unchanged exact engine.
Production build and live HTTP checks complement these computations. A
real browser layout/interaction review must be reported separately.

The visualization publishes through the dedicated mathematical assets in
`data/integral_atlas_web.json` and the Site's `/api/integral-atlas` receipt.
The broader shared research and web feeds retain their previous published
versions; their refresh was blocked by automatic approval review.


## Autonomous React + Three.js experience

The `/integrals/` entry point now opens a React 19.2.6 / Three.js 0.186.1
scene based on the two user-supplied Claude artifacts. Their midnight-blue
field, blue cyclotomic lobe, coral E8 lobe, upper violet bridge, lower gold
convergence, central lavender fiber, and four-part automatic sequence guide
the composition. The published Code tabs were examined directly. The new
scene adds spatial curves, additive particle shaders, postprocessed bloom,
camera orbit, and smooth 2.2-second transitions. Time uses elapsed seconds;
each mode lasts 18 simulation seconds. Animation and scene cycling start
automatically, except when the browser requests reduced motion. The user can
pause, hold a scene, adjust speed/glow, orbit, and save the rendered frame.
Hidden tabs suspend progression. No data or telemetry is transmitted.

The scene includes 384 decorative positions around the cyclotomic node,
the 240 source-derived E8 projections, and 264 decorative positions around
the fiber node. Only the E8 node uses root coordinates; the other point
arrangements are illustrations of counts, not embeddings or equivalences.
The root display scales the normalized Coxeter-plane x/y coordinates by
0.93 and the optional exponent-seven depth by 0.62. Cloud rotation and
pulsation are visual operations. The violet cloud, gold cloud, toroidal
knots, braids, curved connections, and simplices are conceptual motifs.
The component's selected-node explanations distinguish these from exact
phase maps and integral identities. In particular, there is no asserted
higher categorical equivalence, categorical trace of 264, or physical E8
model. Raghava's moment scaling and the Mellin cancellation remain available
in the retained exact calculators and monograph.

`web/integral-families/resonance.jsx` owns the React interface;
`resonance-scene.js` owns Three.js. Install the pinned packages in that
directory, then run `npm run build`. The release carries a self-contained
`resonance.bundle.js` and its linked dependency licenses, so the hosted
scene requires no CDN. `python/export_integral_atlas.py` binds the new
source/assets into the dedicated mathematical receipt and feed.

`node python/tests/test_resonance_scene.mjs` executes the actual Three
geometry/curve constructors, checks all root positions, source geometry,
determinism, and phase counts. It does not run a WebGL context or establish
browser appearance. The original atlas's fixture test now loads `atlas.html`.
The production build and live asset/receipt checks are reported separately
from browser QA.


## Refined motion and close study

Transitions now save the visible node positions, scales and four scene
weights before changing direction. Repeated selections during a transition
continue from that mixture. A separate presentation clock permits manual
view changes while the mathematical animation is paused; reduced motion
makes transitions immediate. The automatic camera stays within a bounded
front-facing arc rather than orbiting indefinitely behind the arrangement.
Direct manipulation takes priority for eight seconds. Resize retains the
user's zoom relative to the scene framing.

Clicking a structure enters a close study and holds automatic scene changes.
Returning restores the whole field and resumes the tour from a fresh scene
interval. E8 now highlights a root and its actual 56 adjacent roots. The
selected root follows the exported Coxeter successor every 1.6 simulation
seconds, traversing all eight 30-root orbits. The inspector reports its
source-derived eight coordinates, orbit and step. The displayed adjacency
segments are projected exact root relations; the comet trails on the larger
connecting paths remain conceptual motion graphics.

A shader draws a restrained 37-by-29 warped luminous grid, echoing the
original reference background. Six-point particle tails add directional
flow. Adaptive detail reduces pixel ratio, bloom resolution and particle
count on slower devices; explicit full and efficient modes remain available.
This adaptation does not alter root data or mathematical calculations.

Measured label boxes are clamped to the clear scene area and separated when
they collide. Close-study labels are replaced by the selected inspector.
Hidden interface elements are inert, and Escape closes panels even while a
control has keyboard focus. A graphics interruption offers a restart.
`python/build_resonance_downloads.py` produces the standalone and inline
copies from the same shipped bundle, preserving licenses and checking their
asset independence. New pure transition, camera, adjacency and label-layout
checks complement the existing React markup and geometry tests. These are
still distinct from browser visual and WebGL execution QA.
