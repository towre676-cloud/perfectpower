# Repeatable movement is not yet transferable scouting signal

*Big Data Bowl2027 working writeup — reproducible development, not a submitted entry.*

Can a defensive lineman's Combine movement tell us something about rookie pressure production that ordinary measurements miss? We tested a narrower version of that question: whether four source-only movement coordinates improve player-held-out prediction of recorded rookie pressure frequency. The answer in this dataset is **not yet**. This matters because interpretable movement measurements can look promising while their apparent NFL advantage fails under stronger testing.

## One cohort, two distinct requirements

The retained sample contains74 rookies:23 from2023,22 from2024 and29 from2025. It supplies361 accepted Combine attempts and14665 eligible charted rookie rush records. The outcome is each player's observed pressure-event fraction in that cohort. This is conditional on NFL participation, charting, playing opportunity and the historical cohort's get-off requirements. It is not an all-prospect career-success measure or a causal measure of physical ability.

Our analysis separates two questions: does a movement measurement recur across a player's Combine attempts, and does it improve predictions for an athlete whose NFL responses were not used to fit that prediction? Repetition alone cannot establish the second claim.

## Four quantities, fixed before this follow-up run

We used pass-rush speed gain, pass-rush recovery acceleration, hoop redirection and four-bag braking. The phase quantities come from an explicit-duration movement engine that retains multiple possible segmentations rather than treating one phase boundary as certain. These are operational templates; they have not been calibrated against annotated physiological phases.

The conventional baseline selects among three fixed subsets of fifteen recorded body/timed/NGS fields and a fixed ridge grid, including a mean fallback. Every candidate shares the same source Combine position and drill-availability indicators. NGS scores mean this is a stronger baseline than stopwatch timings alone. All74 source Combine positions are simply DL, so our training-only position-mean control is numerically identical to the global mean; it is not a genuinely differentiated role baseline.

The movement model predicts a correction to a separately tuned conventional forecast. Conventional training predictions are cross-fitted before constructing residual responses. All imputation, scaling and nuisance adjustment occur inside training. The four-coordinate ridge correction is halved and capped at two absolute percentage points. Inner validation chooses only between that fixed correction and exact no correction. A conservative selection rule is useful engineering, not a guarantee of improvement for new players.

## Results that survive the reporting process

Entire athletes stay together in every split. Earlier-class development uses three class-stratified four-fold repetitions. We average each player's losses over repetitions before summarizing, rather than counting the same athlete three times. Temporal models fit earlier players and predict a later class. The2025 class was already inspected in earlier work and remains exploratory.

| Comparison | Conventional MSE | Selected compact MSE | Relative error reduction |
| --- | ---: | ---: | ---: |
| Repeated development2023/2024 | 0.000953206 | 0.000959202 | −0.63% |
| Fit2023, predict2024 | 0.001525834 | 0.001525834 | 0.00% |
| Exploratory2025 | 0.000714146 | 0.000773802 | −8.35% |

The compact strategy chose no correction in two development repetitions; in the third, error worsened2.02%. Its pooled conditional player-bootstrap interval includes both gains and losses. The2024 temporal result is exact fallback, not evidence of extra predictive information. Even the bounded correction deteriorated on exploratory2025.

A broader previous baseline-preserving residual study also failed: the selected strategy worsened repeated-development error2.878%, and both temporal comparisons chose no correction. Earlier favorable percentages came from different specifications on these same reused players; they are preserved as exploratory findings, not independent replications. Reducing the feature block and capping extrapolation did not produce a validated advantage.

For uncertainty,4000 fixed-prediction player bootstrap resamples preserve class counts. Temporal comparisons additionally have20 complete training-player bootstrap refits, with duplicate identities kept together, followed by paired test-player resampling. Twenty refits give coarse descriptive sensitivity; they cannot establish finely calibrated tail probabilities or new-class transport. A16-run class-and-source-position mislinking control reassigned about96.9% of development players' movement profiles and always selected fallback. This cannot distinguish our real fallback from useful movement learning, and is not a formal significance test.

## Which measurements are stable enough to investigate?

We split each development player's repeated attempts into alternating event-ID groups and compared their feature medians. This uses only Combine observations, not NFL outcomes.

| Coordinate | Players with repeated attempts | Split-attempt rank correlation |
| --- | ---: | ---: |
| Pass-rush speed gain | 39 | 0.52 |
| Pass-rush phase recovery acceleration | 39 | 0.26 |
| Hoop redirection | 4 | 1.00 — too few to support a strong conclusion |
| Four-bag braking | 0 | Unavailable |

Descriptive player-bootstrap intervals are approximately0.16–0.80 for speed gain and−0.08–0.56 for phase recovery. Different attempts can involve different instructions or conditions, and an event-ID split is not a controlled test-retest design. Nevertheless, the comparison exposes a practical measurement bottleneck: the more complicated recovery coordinate is less reproducible here, while other drills lack sufficient repeats. The hoop correlation of1.00 on four players should not be advertised as perfect reliability.

## Football use and the next falsifiable test

Retain the conventional forecast for scouting decisions. Use the movement engine to describe drills and identify measurements needing better repeat conditions; do not use these results to prescribe training or rank hidden talent as if an NFL edge were established.

We subsequently recovered the original nine official CSVs and completed that mechanism-matched test. Two fixed pass-rush coordinates measured recorded-speed gain and displacement over the first0.5seconds after operational motion onset. The target was the supplied charted NFL get-off time, with training-only alignment, formation, down/distance, score and snap-geometry controls. The forced correction improved systematic player-mean development error only0.21%, then worsened2024 error8.86% and exploratory2025 error0.41%. Every inner-selected model retained exact fallback. The auxiliary play-timing loss supported the same decision. Context makes this a conditional NFL comparison, not a pre-draft forecast. A genuinely uninspected cohort is still required for confirmation.

The attached notebook rebuilds the historical cohort from nine hash-pinned official files, uses audited source Combine metadata rather than eventual NFL position, verifies the four player feature medians against their attempt records, and produces four aggregate figures. It also supports the authorized trusted extracted continuation. The full nine-CSV reconstruction was executed locally: all source hashes matched, and the pressure-study model errors exactly matched the trusted-input run. The expanded notebook also executes the get-off/context comparison; versioned receipts identify the tested notebook and code. No raw competition data or player predictions are bundled in the public code, and this working writeup has not been submitted to Kaggle.

Notebook: [Combine Movement Continuation](https://github.com/towre676-cloud/perfectpower/blob/main/notebooks/Combine_Movement_Continuation.ipynb). Specification and receipts: `docs/COMBINE_COMPACT_PROTOCOL.json` and `receipts/kaggle_combine/`. Mathematical implementation and limitations: [monograph](https://github.com/towre676-cloud/perfectpower/blob/main/docs/COMBINE_COMPACT_MONOGRAPH.md).
