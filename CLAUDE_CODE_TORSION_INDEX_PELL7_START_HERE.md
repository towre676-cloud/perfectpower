# Torsion-aware index and Pell-7 handoff

The new arithmetic components are `python/perfectpower/elliptic_torsion_index.py` and `python/perfectpower/pell7_complete.py`. Read `docs/TORSION_INDEX_PELL7_MONOGRAPH.md` for the hypotheses, all-solutions proof and trust boundary. Run `make check-torsion-index-pell7` from the repository root. The independent development oracle uses SymPy; production certificates and replay use standard-library exact arithmetic.

The elliptic operation consumes an existing complete prime-preimage presentation, an independently certified free witness basis, an injective finite torsion product, and coordinates for both the original source list and the entire preimage generator list. Use `generators`, not only `replacement_points`, because prime-kernel generators matter. The packet supplies complete integer relation bases, reduced group invariant factors and the actual nested subgroup index. Both coordinate groups must span the free witness space. The finite product is not advertised as the full rational torsion subgroup.

Historical free-only index packets and all earlier preimage schemas remain unchanged. The query service adds two torsion-aware index operations and three Pell operations. Tests cover pure 5/7 torsion, two independent 2-torsion generators, a free-plus-torsion subgroup with repeated generators, closure and actual enlargement. Regenerated worked files live in `receipts/torsion_index_pell7/`.

Pell-7 positive seeds are `(1,2)` and `(5,4)`, iterated by `(x,y) -> (3x+4y,2x+3y)`. Every integer solution has independent signs on one positive orbit point. The inverse strictly reduces positive x until its next x is nonpositive. Then y is at most five, and the complete finite terminal table gives exactly those seeds. No global completeness claim depends on the 100,000-coordinate scan.

The bounded executable certificate operation is exact Python replay plus paper proof, not a new Lean proof. No Mordell rank case is closed. Next: attach witnessed torsion-aware stage indices to saturation, or develop genuinely independent 2-descent rank upper bounds; do not infer global termination from a finite saturation run. Keep concurrent flavor, wall and arithmetic-chart work intact.

The distributed ZIP parts together contain every tracked source file at the published commit. Extract all parts into the same directory; the included source-package note records the commit. The accompanying PDF is the rendered monograph.
