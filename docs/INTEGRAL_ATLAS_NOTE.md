# Spectral Atlas: what the pictures actually mean

The live `/integrals/` entry point now offers four linked views. The previous
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
export the current diagram as SVG with state and source identity. There is
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
