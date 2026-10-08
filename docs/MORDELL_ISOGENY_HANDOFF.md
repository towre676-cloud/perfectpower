# Mordell witness handoff: all five residual curves closed

The five constructive gaps described below have now been closed by checksum-pinned published-coordinate discovery and exact independent certificates. Read MORDELL_WITNESS_CLOSURE_MONOGRAPH.md and receipts/mordell_published_witnesses.json for the current state: all 457 matching witness ranks, zero witness gaps. Next work concerns complete bases, saturation and integral-point completeness. The following is the historical isogeny-release handoff.

# Continue from five missing Mordell witnesses

Read MORDELL_ISOGENY_WITNESSES_MONOGRAPH.md and receipts/mordell_isogeny_search/continuation_summary.json. The constructive frontier is now five rank-one curves: k=5935,7482,7823,8210,9454. The preceding 90-gap release is commit 658ac46; this continuation closes another 85 gaps. All 457 external backend ranks were already determined; 452 now have matching retained point witnesses.

The new reusable route searches E_{-27k}, then applies its normalized degree-three dual to E_k. Exact equations, differential factors, group-law examples, source cover coordinates, composed polynomial maps and original-curve independence evidence accompany the code. The successful pass searches partner-cover numerator height ten million and denominator height one million with eight seconds per cover. It returns 83 images on 82 curves. The longer original-cover pass closes k=-2558,-4565,-8041.

The missing rank-two direction at k=-9257 is closed. Its explicit independent pair consists of the existing (21,2) and the large rational point in rank_two_basis.json. The full packet retains one more image, so its three points span two independent directions. Do not force a redundant point list to become independent; stop optional halving once the certified lower bound matches the upper bound.

The five remaining positive-k cases have unsuccessful retained partner-cover attempts at numerator and denominator height one hundred million and thirty seconds per cover. The Heegner pilot returned no checked points: it retained timeouts and stack failures at 128-million and 512-million-byte budgets. Those statuses are unfinished discovery, never insolubility. A future continuation can pursue better coverings or a more capable analytic point-discovery budget, preserving exact original-coordinate images and the existing upper bounds.

Run make check-mordell-three-isogeny and make check-quartic-invariants, then the test_mordell*.py suite. SymPy supplies independent symbolic tests; PARI/GP is needed for discovery only. Use develop_mordell_isogeny_search.py --keys 5935,7482,7823,8210,9454 to target the residual cases. Discovery and --apply-only are deliberately separate, so application should run after other descent-packet writers stop. The application is restartable and deduplicates retained image records.

Complete bases, global saturation termination and all 457 integral-point-list obligations remain separate. No new Lean theorem is supplied here. All 83 new isogeny images are nonintegral; point discovery must not silently promote integral-point completeness.
