# Closing the final five Mordell witness gaps

October 8, 2026. This continuation starts from commit 5735bab8f88c42080390e2ba04d6cf5c5c47392a. All 457 frontier curves now have retained exact rational points whose independently checked rank lower bounds match the existing external PARI rank upper bounds. The constructive witness gap count is zero. N26 and N27 are closed; complete bases, saturation and integral-point completeness remain separate.

## From 92 missing witnesses to zero

The starting frontier had 365 matching witness ranks and 92 constructive gaps, despite equal external rank bounds on every curve. Binary quartic contractions and cover reduction supplied two additional witnesses. A longer original-cover search and exact degree-three isogeny transport then closed another 85, including the second independent direction at k=-9257. This release closes the final five rank-one cases: k=5935,7482,7823,8210,9454. The resulting count is 365 + 2 + 85 + 5 = 457.

These are closures of missing constructive witnesses, not new discoveries of the curves' ranks. Each final curve already had backend lower and upper bounds equal to one. The new coordinates provide exact, independently replayable evidence that the rational witness span has rank at least one. Combining that certificate with the retained external upper bound determines the rank. No new formal Lean rank theorem is claimed.

## Published discovery with exact local verification

Rafael von Känel and Benjamin Matschke publish Mordell data at https://www.math.u-bordeaux.fr/~bmatschke/data/. Their mwMordell10000.sobj file contains candidate Mordell-Weil coordinates for coefficients of absolute value at most 10000. The page specifically records a correction for the previously missing basis at k=7823. This release uses the five rows as discovery inputs and independently checks their coordinates and independence; it does not adopt the published assertion that the points form complete bases.

The fetched source has 565585 compressed bytes and SHA-256 23692c1f7d63fd94cab3a1231fadbba83a08755a0c370e20e191a4d8b8686c2d. It contains 19662 distinct curve records and 17645 finite points. Every decoded point was checked against y^2 = x^3 + k. The retained five-row numerical excerpt is attributed to von Känel and Matschke under the source's CC BY-NC 3.0 license. The full external dataset is not bundled.

The reader pins the exact source digest, bounds compressed and decompressed sizes, and allows only Sage's two numeric constructors: make_integer and make_rational. Their base-32 numeric strings become Python integers and exact fractions. It imports no Sage code and rejects other serialized constructors and persistent references. Candidate intake checks original models, canonical coordinates, exact curve equations, monotone rank lower bounds and consistency with existing rank upper bounds. The independence verifier replays the resulting local character evidence without trusting the discovery source.

The runner prepares all five updates before writing any descent packet. It then independently replays every one of the 457 frontier independence certificates, checking each certificate's curve, original points and lower bound against the retained packet. All 457 audits pass. Repeated intake deduplicates evidence and preserves integral-point-completeness flags. The JSON receipt includes provenance, the original-coordinate points, the five new certificates and the full-frontier audit count.

## Compact witnesses on the original quartic covers

The published points also have exact rational preimages on the original retained two-descent covers. Rational-root discovery solves Nx(t) - X R(t) = 0. Each recovered primitive weighted coordinate triple (u,v,w) is then checked with integer arithmetic: w^2 = F(u,v), where F(u,v) = sum(f_i u^i v^(4-i)) and the coefficients f_i are stored constant first. The retained polynomial cover map is evaluated exactly and its image must equal the published point. Rational-root discovery is not used to assert absence or completeness.

For k=5935, the original coefficients are (-51,-180,96,-8,8). A primitive point is (u,v,w) = (7741645,3925433,80151645787027), of projective height 7741645. Its original Mordell x-coordinate is 1573926535825566419486491757301 / 6424286322369043038241498729. Its exact y-coordinate and independence certificate are retained in the JSON receipt.

For k=7482, the coefficients are (-107,-52,108,24,12). A primitive point is (-4352547,2862277,-116320140782911), of projective height 4352547. Its original Mordell x-coordinate is 242469028088310505201151037943 / 13530375151756234868029633921.

For k=7823, the coefficients are (41,-16,-6,112,-11). A primitive point is (-10677130,42786483,11981673410095561), of projective height 42786483. Its original Mordell x-coordinate is 2263582143321421502100209233517777 / 143560497706190989485475151904721.

For k=8210, the coefficients are (60,-40,60,-108,13). A primitive point is (3856363,402909,-22713799574323), of projective height 3856363. Its original Mordell x-coordinate is 124297604919859563283830783599 / 515916691102515696000908329.

For k=9454, the coefficients are (-2,-56,24,-3,3). A primitive point is (-7810603,829966,116658072587271), of projective height 7810603. Its original Mordell x-coordinate is -1142659799409656583366878444423 / 54436423599107958191644909764.

All five original-coordinate points are nonintegral. Cover heights range from 3856363 to 42786483, explaining why small searches did not supply these particular points. Earlier larger searches were time-limited, so their unsuccessful statuses were never exhaustion or insolubility certificates. The compact triples now permit exact replay without searching those height ranges.

## Validation and reproduction

Run make check-mordell-published-witnesses for the five equations, cover transports, independent certificates, mutation rejection, digest rejection, constructor restrictions, idempotence and frontier-count consistency. Run the test_mordell*.py suite with PERFECTPOWER_GP set to a working PARI executable for its optional live-discovery checks. The suite has 36 passing tests. The quartic invariant checks add 11 passing tests, for 47 total. The separate full-frontier audit replays all 457 independence packets successfully.

To reproduce intake, obtain the cited mwMordell10000.sobj and run PYTHONPATH=python python python/develop_mordell_published_witnesses.py --source /path/to/mwMordell10000.sobj. A changed digest is rejected. SymPy supplies rational-root discovery for cover preimages. Then run python/reconcile_mordell_frontier.py and python/develop_mordell_two_descent.py --effort 3 with PYTHONPATH=python. Existing effort-three packets are reused. Routine receipt verification requires neither the external dataset nor Sage, network access or a new point search.

The complete archive includes code, tests, five updated descent packets, refreshed frontier and descent summaries, the source-attributed closure receipt, this monograph and all preceding work. Historical isogeny and invariant receipts retain their release-time counts; the current frontier and this closure receipt are authoritative for the zero-gap state.

## What remains mathematically open

All 457 integral-point-list obligations remain open in this frontier. A certified independent rational point does not establish that it generates the full free Mordell-Weil group. This release imports no source basis or global saturation assertion. Complete bases, saturation termination, global height bounds and complete integral-point enumeration require their own evidence. The earlier 79 Thue-class and 88 unit-equation obligations are separate and are not changed by these rank-witness closures.

The original Birdtracks reference motivates reusable invariant contractions and coefficient control; its representation-theory machinery is not a proof of Diophantine completeness. The successful final step combines published numerical discovery with exact original-cover lifts and independent arithmetic certificates. The concrete achievement is complete constructive rank-witness coverage for this 457-curve frontier, with every remaining completeness task still explicitly tracked.
