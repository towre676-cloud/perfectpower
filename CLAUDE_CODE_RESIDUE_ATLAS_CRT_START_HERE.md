# Complete multi-prime atlas products

Start with `docs/RESIDUE_ATLAS_CRT_MONOGRAPH.md` and `docs/RESIDUE_ATLAS_CRT_VALIDATION.md`. The twelve general declarations in `PerfectPower/ResidueAtlasCRT.lean` establish normalized coordinate CRT, complete root-table composition, exact cardinality products and nested rectangle counts. `PerfectPower.lean` imports the new module.

The runtime lives in `python/perfectpower/residue_atlas_product.py`. The public operations in `query_service.py` compose, independently replay, count, rank, select, scan and emit native certificates. Large products retain all local tables with roots=null; they are complete factored covers. Successful counts and scans exhaust all contributing branches. Budget exhaustion raises an error. Rank/select ordering is local-root tuples followed by x and y within each cell.

Run `make check-residue-atlas-product` with the pinned Lean toolchain. The producer emits six worked packets and native programs; the census independently enumerates 120 sources. Native programs instantiate the general proof and use kernel reduction. Keep execution_verified=false until generic compiler refinement is proved.

The bounded next push is formal factored traversal and rank/select refinement. Prove the prefix congruence invariant, zero-cell pruning, complete leaf coverage and exact population sum before connecting offsets to inverse rank/select. Preserve the stable schema and the concurrent fixed-divisor, flavor and elliptic work. Do not replace larger research premises with finite examples.
