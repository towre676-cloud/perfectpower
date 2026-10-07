# CRT atlas validation

The focused command is `source ../lean-env.sh` followed by `bash scripts/check_residue_atlas_product.sh` in the checkout. The environment shim is local runtime support; ordinary Lean 4.20.0 installations can run the script directly with the pinned Mathlib dependencies.

All 25 product tests passed. They check complete explicit and factored products, independent local replay, malformed and omitted roots, shared-prime and source mismatch rejection, huge counts and indices, signed rank/select, work and candidate budget rejection, eight-factor pruning, empty-last-factor short circuit and public query integration.

The independent nested-Horner census passed all 120 sparse-source cases (seed 20261008), including 15 empty products. Direct enumeration of each product-modulus square agrees with complete root cardinalities and explicit tables. Direct signed-rectangle enumeration agrees with factored populations and complete source scans. Sampled rank/select roundtrips agree. The persisted record is `receipts/residue_atlas_product/crosscheck.json`.

The twelve general CRT declarations and all six generated native programs compiled. The script audited 362 printed declaration records and rejected dependencies outside propext, Classical.choice and Quot.sound. Axiom-free declarations are counted separately. No sorryAx or Lean.ofReduceBool was admitted.

Adjacent regression checks passed the 23 existing residue-atlas tests, 24 fixed-divisor tests and 18 query-space tests: 90 focused and adjacent Python tests in total. This is targeted validation, not a rebuild of every historical repository certificate.
