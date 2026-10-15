# Concurrent-session movement engine handoff

This session adds python/perfectpower/movement_language.py and movement_features.py in PerfectPower main. Your front_transfer.py, ordered_motion.py, receiver studies and notebooks remain untouched. Import ensemble_features(time,xy,speed) after adding PerfectPower/python to your Python path. Times are contiguous 10Hz seconds, coordinates yards, speed yards/second. The result is (feature_dict,audit), generated without outcome labels. Aggregate per player/drill in your training pipeline; fit any scales, PCA or regression only in training folds.

The generic segment_channel API accepts per-frame phase costs, duration bounds, additive rewards, temperature and boundary windows. It returns exact counts/ranks, weighted samples, stable additive moments, all-path bounds and boundary/frame posteriors. Treat operational phase posteriors as model weights until calibrated. Compare order-only, uncertainty-only and conventional features separately. Baseline fallback is available in the transfer runner. Real-data results and failures are in receipts/movement_language; the 2025 class is exploratory reuse, not an untouched test.

No raw or athlete-level data is committed. The private adapter output paths are chosen explicitly by the caller. Public examples are synthetic and compatible with the standard-library CLI.

## Residual-correction follow-up (October 15)

The new `perfectpower.movement_residual` module and `scripts/run_movement_residual.py` run alongside the original experiment. See `MOVEMENT_RESIDUAL_MONOGRAPH.md`, the outcome-independent candidate bank in `MOVEMENT_RESIDUAL_PROTOCOL.json`, and `receipts/movement_language/residual.json`. `scripts/prepare_movement_residual.py` reuses the existing authorized cohort and original Combine tracking; it adds source Combine position, leaving the donor cohort unchanged. Private output must be outside the checkout. Zero correction retains the fitted conventional prediction exactly, but tuning this option does not ensure lower unseen error.

PerfectJet main was checked at `01fe017c41d7bdc7352be84fa6d4654a9d0c29c7`, including the merged repeat-decision work. Its open sextic partner PR #2 and its NFL experiment modules were left intact. Both engines still use the same observed players; their outcomes cannot be counted as independent replications. This follow-up does not use early rookie NFL tracking as a predictor.
