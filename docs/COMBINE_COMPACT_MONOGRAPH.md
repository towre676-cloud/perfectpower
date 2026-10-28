# Compact Combine-to-NFL continuation

28October2026. Retrospective development on the existing Big Data Bowl2027 cohort. No independent scouting advantage or Kaggle submission is claimed.

## Result

Four declared source movement coordinates do not improve the tuned conventional prediction: selected repeated nested MSE0.000959201526362 versus0.000953205570471, a0.629% deterioration. The unselected fixed correction worsens0.206%.2023→2024 selects exact no correction; exploratory2025 selects the correction and worsens8.353%. Global and source-position means worsen19.104% in development; all74 source positions are DL, so these two controls coincide. Keep the conventional model as the operating recommendation.

This is a follow-up to the broader residual study, not a replacement for its−2.878% result. The favorable earlier legacy comparisons remain in their historical receipts; `audit_movement_residual.py` replays their exact hash-pinned pre-fix source under `research/movement_language/run_movement_transfer_legacy.py`, exclusively for historical reproduction; the corrected source-position baseline and feature bank must not be described as exact replays of those older NFL-position specifications.

## Source and isolation

The recovered `Movement_Residual_Private_Continuation.zip` supplied74 player aggregates and361 source attempt features, including14665 previously inspected eligible rookie rushes. New code verifies every compact player feature against its source-attempt median and asserts the exact class sizes23/22/29,74 players,361 attempts and14665 rushes. Unmatched/duplicate attempts fail. It does not inspect the sealed two-season2025 pressure-confirmation data. The competition target is a different, previously explored charted rookie pressure-event fraction.

The legacy extractor now audits source Combine metadata constancy instead of silently taking the first observed value, joins tracking by player AND draft class and removes eventual NFL position from predictors. This release's numerical experiment consumes the saved extracted features; the new raw metadata-constancy audit has synthetic tests but was not re-executed against the absent original nine CSVs. The notebook preserves the exact historical cohort reconstruction code as public source only, with file and upstream-notebook hashes; it calls its preparation routine, not the older modeling routines. The cohort itself uses observed NFL position and participation/get-off filters, so predictor correction does not turn the roster into a pre-draft census.

## Fixed bounded estimator

The four coordinates are pass-rush speed gain, pass-rush operational phase recovery acceleration, hoop redirection and four-bag operational braking. No additional feature screen or penalty search is applied. The conventional model is the existing inner-tuned Baseline. Its full15/core8/motor4 subsets include source position and source availability; full15 includes NGS scores.

For every correction-training player, a separately tuned conventional fit excluding that player supplies the response residual. Four source coordinates are standardized and residualized against the full conventional design in training only, then clipped to[-3,3]. Ridge10 without intercept predicts the cross-fitted residual. Add half its correction, capped at±0.02, and clip the final pressure fraction to[0,1]. Inner class-stratified whole-player validation compares only this fixed estimator with exact baseline fallback, accepting correction only if its paired mean gain exceeds one estimated player standard error. This is a heuristic, not a dominance theorem. The cap limits extrapolation magnitude; it cannot create alignment with true errors.

For an unclipped correction d added to baseline b, the squared-error gain is2mean((Y−b)d)−mean(d²). The correction must align with held-out baseline errors enough to pay for its own variance. Fewer dimensions and a smaller cap reduce opportunities for large mistakes, but do not manufacture that covariance. The observed failures are compatible with weak signal, outcome noise or context mismatch; this study does not identify which explanation is correct.

## Evaluation and uncertainty

Three four-fold whole-player development repeats retain their original seeds714,914,1114. Players rather than repeated fold appearances are the bootstrap units. Temporal training is2023→2024 and2023/2024→exploratory2025. Every fit and inner choice uses training responses only. The primary compact model and every control are retained regardless of score.

Temporal fixed-prediction uncertainty has4000 paired player resamples and Bonferroni intervals for the eight declared temporal/control comparisons. They condition on retained fitted predictions and do not account for refitting, adaptive prior research, team/game dependence or class shift. Twenty full training-player refits per temporal comparison add a coarse sensitivity check; their percentile ranges are explicitly not calibrated simultaneous intervals. Duplicate resampled identities remain in the same fold.18/20 earlier temporal refits and17/20 exploratory2025 refits choose exact fallback. A mass at zero can reflect fallback and is not positive predictive evidence.

Sixteen class/source-position-constrained mislinking runs on2023→2024 each selected fallback, despite about96.9% reassignment. They are a descriptive feature-pairing control, not a p-value or proof that correct identities add information. All source-position labels in this cohort are DL.

## Repeatability

A separate outcome-free audit uses2023/2024 attempts only, deterministic alternating event-ID halves and player bootstrap. Pass-rush speed gain has39 repeated players and Spearman0.5190 (descriptive interval0.1583–0.8007); phase recovery has39 and0.2587 (−0.0804–0.5590). Hoop has four repeat players and rank correlation1, without a supported interval. Four-bag has no repeated players. Attempt conditions can vary; neither these correlations nor the phase engine's posterior weights establish physiological reliability. Outcomes do not enter this audit.

## Reproduce

Install `requirements-movement.txt`; then run the focused tests with `PYTHONPATH=python python3 -m pytest -q python/tests/test_movement_language.py python/tests/test_movement_features.py python/tests/test_movement_transfer.py python/tests/test_movement_transfer_source.py python/tests/test_movement_residual.py python/tests/test_combine_compact.py python/tests/test_scouting_confirmation.py` (44passed).

From the trusted private continuation, run:

```bash
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python3 scripts/run_combine_compact.py --players /path/residual_input/players.pkl --events /path/residual_input/events.pkl --private-out /path/private_compact --aggregate receipts/kaggle_combine/compact.json --refits 20 --permutations 16
python3 scripts/audit_combine_repeatability.py --events /path/residual_input/events.pkl --out receipts/kaggle_combine/repeatability.json
```

All32 historical legacy scalar metrics were also reproduced exactly (maximum absolute difference0), recorded separately in `receipts/kaggle_combine/legacy_replay.json`. The compact source/protocol/input hashes and dependency versions are stored in the receipt. `python3 scripts/build_kaggle_combine_notebook.py` regenerates the output-free self-contained notebook and verifies public source hashes. It supports trusted private inputs or nine official hash-pinned CSVs. All-cell execution on the trusted-input path was tested; the original raw-source branch has not been run here. No Kaggle publication or submission was performed. Restricted raw data and per-player predictions remain outside the checkout.

The working writeup contains fewer than2000words and the notebook produces three figures plus an aggregate class table, within the currently published challenge limits. Check those official requirements again before submission. Feed regeneration is distinct from live deployment and native executable changes; no such upgrade is claimed.
