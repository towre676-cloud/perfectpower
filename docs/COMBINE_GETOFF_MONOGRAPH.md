# Official reconstruction and launch-to-get-off test

28 October 2026. The two remaining tasks from the compact Combine release are completed: the official raw-data rebuild and a fixed launch-to-NFL-get-off/context comparison. The evaluation remains retrospective development; no Kaggle entry or scouting model is promoted.

## Official reconstruction

The original authorized restricted archives supplied all nine official CSVs, totaling approximately2.31GB uncompressed. Every file matched its existing SHA256 pin before reconstruction. No new Kaggle login, credential reuse or download was required. Only aggregate receipts and public code are committed.

The pressure-study notebook was first executed from a fresh working directory with trusted extracted-input bypass disabled. It rebuilt the same74 rookies,361 attempts and14665 rush records, produced three figures, and exactly reproduced all12 checked MSE values from the saved-input run. It included40 full temporal refits and16 feature-mislinking runs. This first-stage receipt is `receipts/kaggle_combine/official_rebuild.json`, pinning the earlier notebook version. The extended notebook adds the get-off study and a fourth figure; its complete raw execution is bound separately in `official_rebuild_full.json` to the new notebook hash and both empirical result files. The earlier receipt is historical evidence, not certification of a later notebook version.

## Mechanism-matched source measurement

The new source block uses only PASS_RUSH_DRILL tracking. Its two player-median coordinates are recorded-speed gain and Euclidean displacement over exactly0.5seconds after an operational movement onset. Three consecutive speeds above1yard/second define that onset. Near10Hz contiguous timestamps, finite coordinates/speeds and sufficient endpoint support are required; actual-time interpolation gives the half-second endpoint rather than assuming that five imperfect intervals equal0.5seconds. No official start cue or physiological reaction time is inferred.

There are143 accepted pass-rush attempts covering all74 players; no player is excluded for lacking a launch measurement. Rigid-coordinate transformation and irregular-timestamp tests verify the measurement contract. The exact original rookie rush roster is retained, including its observed participation/get-off filters. This is not a pre-draft census of all prospects.

The target is the supplied charted `player_get_off` in seconds. It is not renamed physiological reaction time, and it is not the separate sealed two-season pressure endpoint. Its earlier exploration is acknowledged.

## Context and separation

Context uses recorded down, distance, yardline, pre-snap scores, quarter, snap depth, width and speed, plus lineup position, formation and blitzing. The response fit is fixedRidge10 with equal total weight per training player. Numeric preprocessing uses the training plays; it is not itself uniformly weighted across players. NFL team identifiers, eventual NFL position, post-play results and pressure outcomes are excluded from this experiment's retained inputs. These context controls answer a conditional football question, not a causal question about intrinsic athletic ability or an unconditional pre-draft forecast.

The conventional source grid is the existing three feature subsets and fixed ridge penalties, selected by whole-player cross-validation on raw player-mean get-off. That selected configuration is reused for contextual-residual source fitting. It is not retuned against residual targets whose nuisance fits could contain an inner held player's response.

Every correction response comes from a complete context/source pipeline fitted without that player. This includes the context fits used to construct peer nuisance responses; a test changes one player's responses by100seconds and confirms that the baseline predictions used for that player's correction response remain unchanged. The two launch coordinates are standardized and residualized against conventional source traits inside training, then clipped[-3,3]. FixedRidge10 without intercept predicts the cross-fitted player-mean errors. Half its correction is added, capped at half the standard deviation of training-player mean raw get-off. The temporal caps are approximately0.0538 and0.0517seconds. No probability clipping is applied to a real-valued time target.

Inner player-separated selection compares only this fixed correction with exact fallback, requiring paired mean gain greater than one estimated player standard error. The rule remains a heuristic; outer performance is the test.

## Result

The primary metric is the squared mean forecast error of each player, then averaged equally across players. It measures systematic player-mean calibration. It is different from averaging squared play errors, which is retained as a separate auxiliary outcome. Repeated split losses are averaged within each player before inference.

| Evaluation | Conventional/context primary MSE(s²) | Fixed launch MSE(s²) | Fixed relative gain | Selected relative gain |
| --- | ---: | ---: | ---: | ---: |
| Repeated2023/2024 development | 0.004430011 | 0.004420627 | +0.212% | 0.000% |
|2023→2024 | 0.002550500 | 0.002776473 | −8.860% | 0.000% |
| Exploratory2025 | 0.002263031 | 0.002272324 | −0.411% | 0.000% |

Every one of the12 development outer fits and both temporal fits chooses no launch correction. This is a functioning conservative decision rule, not evidence of extra movement signal. The forced correction's conditional player95% absolute-gain intervals are about[-0.0000781,0.0001040] in development,[-0.0019070,0.0014167] in2024 and[-0.0001362,0.0001343] in exploratory2025; every interval spans gains and losses.

Auxiliary equal-player average play-MSE gives the same decision. The forced launch changes are+0.0167% in development,−0.4042% for2024 and−0.0162% for2025. The selected model again has exact zero incremental change. This avoids presenting cancellation of within-player errors as improved individual-play timing prediction.

Context materially changes the comparison with raw source-only forecasts. For example, the contextual conventional model substantially reduces error relative to the source-only conventional control in the forward runs. That reduction uses observed NFL circumstances. It is not extra information from Combine launch and cannot be advertised as a pre-draft scouting edge. Context alone is better than context+conventional source traits in pooled development but worse in both temporal runs; all six control outcomes remain visible rather than selecting a flattering contrast.

## Uncertainty and conclusion

The4000 paired player resamples are class-stratified and conditional on fixed predictions. They do not account for nuisance/model refitting, researcher adaptation, shared NFL games/teams or future class shift. There are no duplicate-raw-row refits in this get-off release. All classes were previously examined;2025 remains exploratory. Official reconstruction establishes reproducibility, not independence.

Retain the conventional/context baseline. The half-second launch block has not established incremental NFL get-off value. The earlier compact pressure correction and broader residual failures remain intact. Better matching the movement window to the endpoint was a necessary test, and it still returned a negative deployment decision. The current results do not imply that every possible tracking feature is useless, or that small effects are ruled out.

## Reproduction and validation

`notebooks/Combine_Movement_Continuation.ipynb` embeds public code only, supports the nine official hash-pinned inputs, rebuilds both studies, and produces four aggregate figures. A trusted extracted-input path exists but cannot silently skip missing get-off context and still claim complete execution.

```bash
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python3 scripts/replay_kaggle_official.py --data /path/official --work /path/fresh-private-work --receipt receipts/kaggle_combine/official_rebuild_full.json --refits 20 --permutations 16
```

The work directory must be fresh and outside the checkout. All raw data, player forecasts, logs and rendered figures remain private. Source/protocol/input hashes are preserved in the receipts.55 focused tests cover previous movement/prediction logic, exact fallback, source constancy, player identity, held-label/peer invariance, transitive nuisance separation, real-valued responses, timing interpolation, coordinate invariance and corrupted-input rejection. The sealed linebacker confirmation remains untouched. No Site deployment, native executable upgrade or Kaggle submission is claimed.
