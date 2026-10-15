# Movement residual corrections: a baseline-preserving experiment

October 15, 2026. Reproducible development study on previously inspected classes. The algorithm and its tests are released; a predictive scouting improvement is not validated.

## Result and decision

The predeclared inner-selected residual strategy has repeated nested MSE 0.000980640620843, versus 0.000953205570471 for the separately tuned conventional model: a relative gain of -2.878%. Positive gain means lower error. This does not establish a dependable improvement. Retain the conventional prediction for scouting use and keep the movement engine as measurement/research infrastructure. Neither the favorable historical 2025 comparison nor a favorable family chosen after looking at these results is a confirmed edge.

| Model | Repeated nested MSE | Relative gain |
| --- | ---: | ---: |
| Conventional | 0.000953205570471 | — |
| kinematic | 0.000954033780124 | -0.087% |
| ordered | 0.000953205570471 | +0.000% |
| uncertain | 0.000979812411191 | -2.791% |
| combined | 0.000958467634559 | -0.552% |
| reliability_combined | 0.000972549290826 | -2.029% |
| selected | 0.000980640620843 | -2.878% |

## Inputs and recovery

The authorized saved research checkpoint supplied the exact existing eligible rookie-rush table. The already saved restricted source archive supplied Combine tracking; no new Kaggle login or download was requested. The unchanged observation extractor regenerated 361 attempts, 74 players (23/22/29 in 2023/2024/2025), 1,083 onset scenarios and 14,665 eligible rush records. Replaying the original transfer experiment reproduces all 32 audited scalar metrics exactly, with maximum absolute difference zero. Source/cohort hashes are retained in `residual_historical_replay.json`. The new player input adds source Combine position, leaving the donor cohort untouched.

Each target is the observed pressure fraction among that player’s eligible charted rookie rushes. It is conditional on being observed and on playing opportunities. It is not unconditional career success, a causal athletic effect, betting profitability, or an admission-free sample of all prospects. Exposure ranges from 32 to 625 rushes, with median 162. Equal-player MSE prevents high-exposure players from automatically dominating; unequal outcome noise and role/usage differences remain. No NFL motion or early-rookie performance enters the predictors.

The latest PerfectJet main was checked at `01fe017c41d7bdc7352be84fa6d4654a9d0c29c7`, after its repeat-decision merge. The open sextic partner PR #2 and the separate scouting modules were not changed. A saved later early-rookie validation uses NFL observations to predict subsequent rookie games; it answers a different question. Both movement pipelines reuse this player population, so their outcomes are not independent replications.

## Estimator and mathematical scope

Write the fitted conventional prediction as b(x), the source movement vector as z(x), and the correction as g(z). Predict clip(b(x) + lambda g(z(x)), 0, 1). Lambda is selected from zero, one quarter, one half and one. Zero returns the fitted baseline array exactly; it is never approximated by an enormous regularization penalty. Correction ridge penalties are 1, 10, 100 and 1,000, separate from the baseline penalty.

For fixed predictions and before clipping, let r_i = y_i − b_i. The reduction in squared loss is 2 lambda mean(r_i g_i) − lambda² mean(g_i²). A correction needs held-out covariance with baseline error sufficient to pay for its own variance. Training correlation alone is insufficient. A zero candidate makes nonnegative optimal empirical gain possible on the selection sample, but it supplies no dominance theorem on new players. The selected model can still lose on an outer fold or another class. Clipping makes the loss piecewise quadratic; all selections here use the actual clipped predictions, not the unclipped identity.

Residual responses are cross-fitted: for every correction-training player, the conventional prediction comes from a baseline fitted and tuned without that player. Each baseline tuning has its own player-separated folds. This prevents the response residuals from being merely the training errors of a heavily fitted conventional model. Feature imputation and scaling are fitted within training partitions. The movement vector is again residualized against the full conventional design within training; this preserves the existing nuisance adjustment rather than presenting it as a new solution. Ridge uses all predeclared columns without outcome-based screening or PCA.

The conventional bank tunes three fixed sets: all fifteen original conventional fields, eight body/timed measurements, or four sprint/agility measurements. The full set includes three NGS scores, so it is not described as purely physical. All models include the same four drill-availability indicators and source Combine position. Ridge penalties range from 0.1 through 10,000; an intercept-only mean candidate is also available. These choices are made inside training folds. Selection frequencies describe this estimator’s behavior, not causal evidence that the selected measurements matter.

## Selection, separation and uncertainty

The committed protocol fixes the model families, grids, folds and scoring before evaluation. Development uses 45 players from 2023/2024 and three class-stratified four-fold repetitions with seeds 714, 914 and 1114. Three inner folds select each correction family and the overall selected strategy. Selection uses pooled player squared loss. The zero option is preferred unless the minimum-loss correction’s paired improvement over zero exceeds one estimated standard error. This is a conservative heuristic, not a confidence guarantee: inner errors share training observations, and the minimum comes from multiple candidates.

There are five families: kinematic, order-sensitive signature, phase/uncertainty, combined, and source-repeat-weighted combined. The selected strategy chooses across this full fixed bank within inner validation. Family-specific outer outcomes are retained as diagnostics; they cannot be used to choose the reported primary result. Previously inspected 2025 responses never tune a model. All classes have nevertheless been examined in earlier research, and a new protocol does not erase that adaptive history.

Temporal checks fit 2023 and predict 2024, then fit 2023/2024 and predict exploratory 2025. Every penalty, conventional subset, correction and shrinkage is tuned only on the relevant training players. The 2024 temporal comparison is also development evidence because 2024 was used in other nested runs; it is not an untouched secondary test.

For repeated nested uncertainty, squared errors are averaged over appearances of each player before class-stratified paired bootstrap. The three split repetitions are not treated as independent samples, and averaging squared losses is not reported as an ensemble predictor’s error. Fixed-prediction intervals omit refitting and researcher selection. Each temporal comparison additionally has 100 complete training-player bootstrap refits, including preprocessing, baseline tuning, cross-fitting and correction selection, followed by paired test-player resampling. Duplicate bootstrap identities stay together in every fold. These percentile intervals are coarse sensitivity summaries, conditional on the existing classes; they do not cover new-class shift or prior adaptive research.

## Cohort stability and failures

| Evaluation | Baseline MSE | Selected MSE | Relative gain | Full-refit absolute-gain 95% interval |
| --- | ---: | ---: | ---: | --- |
| 2023_to_2024 | 0.00152583430924 | 0.00152583430924 | +0.000% | [-0.00419919877, 0.00048312888] |
| exploratory_2025 | 0.000714146325495 | 0.000714146325495 | +0.000% | [-0.000365606749, 0.000272541645] |

The repeated-development fixed-prediction 95% interval for selected absolute gain is [-5.948314324989682e-05, -3.434231804924119e-07]. This interval must not be presented as full-refit or prospective uncertainty.

Seed 714: baseline MSE 0.00105912941282, selected MSE 0.00105912941282, relative gain +0.000%; zero selected in 4/4 outer fits.
Seed 914: baseline MSE 0.000910346111994, selected MSE 0.00099265126311, relative gain -9.041%; zero selected in 2/4 outer fits.
Seed 1114: baseline MSE 0.000890141186597, selected MSE 0.000890141186597, relative gain +0.000%; zero selected in 4/4 outer fits.

2023_to_2024: zero selected in 43/100 full refits; positive resampled absolute gain fraction 0.100. A mass at zero reflects fallback, not evidence that movement is useful.

exploratory_2025: zero selected in 56/100 full refits; positive resampled absolute gain fraction 0.190. A mass at zero reflects fallback, not evidence that movement is useful.

The full-refit fixed-test diagnostics show 40 of 100 refits losing more than 10% in 2023→2024, versus only three improving more than 10%. For exploratory 2025 the corresponding counts are 17 losses and 11 gains. The largest absolute pressure-rate correction is 0.377 in the earlier temporal refits and 0.0561 in the 2025 refits, exposing extrapolation risk despite shrinkage and clipping. These failure counts are diagnostics on the same reused samples, not independent tests.

Every family, class-specific loss, outer selection, conventional configuration and missingness summary remains in `receipts/movement_language/residual.json`. The historical baseline is reproduced separately; the new estimator uses a wider conventional tuning grid and source position. Its new baseline error should not be silently substituted into the historical percentage comparison.

## What calibration can and cannot mean here

The original phase posteriors use operational templates, not annotated physiological phase truth. No source phase annotations were recovered. Consequently this study does not claim calibrated phase coverage or calibrated physiological probabilities. It tests a narrower repeatability correction: for each drill/feature, estimate pooled within-player attempt variance W and total attempt variance T from training players only, then set reliability R = max(0, min(1, 1 − W/T)). Multiply standardized, nuisance-residualized coordinates by sqrt(R). This is equivalent to a stronger diagonal ridge penalty on unreliable coordinates when R is positive; zero R drops a coordinate. It is a source-repeat noise heuristic, not an exact latent-variable estimator or a reliability estimate for median-aggregated attempts. Genuine attempt variation, limited repetitions and pooling assumptions can all distort it.

Insufficient repeated attempts produce zero weight instead of fabricated calibration. In development, four-bag agility and front-wave/reaction each have 42 players but no repeats: all 40 features per drill are zero-weighted in this family. Pass rush has 45 players, 39 with repeats, and median estimated reliability about 0.148 across features. Hoop has only four repeated development players; its apparently higher reliability is poorly supported. The unweighted combined family remains available, so unsupported repeat calibration is not forced on every model. Full source support is retained in `residual_source_diagnostics.json`. There is no basis here to conclude that order alone or calibrated phase uncertainty identifies hidden talent.

## Reproduce and retain

Install `requirements-movement.txt`, then run `make movement-residual-test`. The 25 focused tests include the existing 18 checks plus duplicate-player bootstrap separation, exact fallback, the paired selection rule, source-only reliability, held-player/peer invariance, overlap rejection and recovery of a known synthetic incremental signal. Synthetic recovery demonstrates implementation capacity under its model assumptions, not football success. The original observation and transfer modules remain unchanged; the new numerical regression is not Lean-verified.

With the already authorized private cohort and original Combine tracking, prepare an output directory outside the repository:

```bash
python scripts/prepare_movement_residual.py --data /path/to/official --cohort /path/to/private_front/private_rows.pkl --private-out /path/to/private/residual_input
OPENBLAS_NUM_THREADS=1 python scripts/run_movement_residual.py --players /path/to/private/residual_input/players.pkl --events /path/to/private/residual_input/events.pkl --private-out /path/to/private/residual_results --aggregate /path/to/public/residual.json --refits 100
OPENBLAS_NUM_THREADS=1 python scripts/audit_movement_residual.py --players /path/to/private/residual_input/players.pkl --events /path/to/private/residual_input/events.pkl --private-out /path/to/private/residual_results --aggregate-dir /path/to/public
```

The separate private continuation package retains extracted player/event inputs, per-player predictions, bootstrap prediction arrays and execution logs. These are excluded from GitHub and the public complete-source package. Their hashes and aggregate receipts identify the retained computation. Restricted inputs are needed to rerun the empirical study; public users can run all synthetic/reproducibility tests without them. The complete public package contains an explicit PerfectPower Git snapshot and a verified generic mobile repository bundle. It is not a rebuilt or newly signed APK, and data updates do not upgrade native executable code.

The active research feed carries the aggregate conclusion under the existing movement-language contract. Direct live endpoint checks in this environment returned HTTP 403, so live consumption cannot be claimed as verified. Existing historical deployment receipts are preserved as historical records.

## Bounded next step

Keep the fitted conventional baseline as the operating model. Before another outcome-driven feature search, obtain source annotations or deliberately repeated drill conditions sufficient to calibrate phase uncertainty, freeze a target and roster rule, and evaluate later uninspected players with matched role/usage definitions. Better measurement may make a future test worthwhile; no amount of exact phase counting by itself establishes NFL predictive value. This completed experiment supplies a falsifiable estimator and retains a negative result rather than converting model complexity into a scouting claim.
