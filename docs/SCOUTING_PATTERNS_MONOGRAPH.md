# Scouting pattern audit: correction direction, role, exposure and influence

October 15, 2026. Retrospective development on previously inspected predictions. No new scouting model is selected or deployed. All earlier identity limitations, chronological protocols and negative results remain in force.

## The strongest supported research hypothesis

The clearest pattern is that the existing ensemble can correct overprediction of pressures per 100 defensive snaps for some linebackers. Among the 24 evaluated Combine linebackers whose forecast decreases, squared error falls 55.189% relative to the conventional baseline: MSE 0.579973 to 0.259893. Twenty of 24 players improve, and the paired mean gain is positive in both observed cohorts: 0.278480 in 2023 (eight players) and 0.340879 in 2024 (sixteen). Mean overprediction falls from 0.636028 to 0.257439 pressures per 100 defensive snaps. This is a prediction-calibration finding about the recorded outcome, not a finding that the players possess superior or inferior intrinsic football ability.

The baseline's simple matured-role-mean control worsens this same group's MSE to 0.884026. Thus this particular correction is not reproduced by replacing each player with the historical mean of his coarse position. That comparison does not identify which college feature causes the difference: the models differ in their fitted functions, regularization and inputs. The receiving and pressure targets must not be conflated.

The subgroup was discovered through exploration. Initial position and top-five influence summaries were inspected, then the full first stratification, then all pressure position/direction and direction/disagreement interactions were added. The protocol records this sequence. The final subgroup's conditional simultaneous bootstrap interval for absolute gain is [0.003695,0.636464] across the final pressure family, but that correction does not cover the adaptive choice of the research family, model refitting, linkage uncertainty, shared NFL team effects or future cohort shift. With two cohorts it is not independent confirmation. The 2025 class still lacks a complete two-season outcome; no partial 2026 season is used to manufacture confirmation.

The useful next hypothesis is a reliability-aware pressure correction for off-ball linebackers, trained and selected inside earlier matured folds. We have not installed a rule that chooses the lower forecast merely because the inspected test cases benefited. A rule derived from these outcomes needs a fresh comparison, and archived-as-of feature evidence remains a separate requirement. Calling this 55% a general scouting advantage would overstate the evidence.

## Position, correction direction and exposure

The full pressure blend improves pooled MSE 7.111% across the same 90 players. EDGE improves 8.122% in both classes, although its direction-specific subgroups reverse signs across classes. Linebackers pooled across both correction directions improve 25.498%, but lose slightly in 2023. Defensive tackles worsen 5.641%. A single broad defensive-position claim would obscure these differences.

Across all pressure positions, lowered forecasts improve 15.809% on 56 players, while raised forecasts worsen 22.009% on 34. Among linebackers, the six raised forecasts worsen 192.263% and lose in both cohorts; this tiny cell's percentage is unstable. Among defensive tackles, lowering the forecast also worsens error in both cohorts. Consequently a universal rule to lower every defensive forecast is not supported by this diagnostic. All small cells are retained rather than discarded because they disagree with the attractive pattern.

Prediction disagreement is the standard deviation of the four forecasts divided by 1+the absolute conventional prediction. Fixed bands are below 0.1, 0.1 to 0.25, and at least 0.25. Moderate disagreement improves 15.95% over 44 players; the five high-disagreement cases worsen about 201.65%, and all five involve raised forecasts. High disagreement is therefore a reason to investigate model support, not an automatic opportunity to trust a more elaborate estimate. These bands were not chosen by maximizing an outer gain.

| Pressure diagnostic | Players | Relative MSE gain | Positive classes | Players improved |
| --- | ---: | ---: | ---: | ---: |
| pos=DE | 8 | +0.03% | 1/2 | 50.0% |
| pos=DT | 23 | -5.64% | 1/2 | 47.8% |
| pos=EDGE | 29 | +8.12% | 2/2 | 55.2% |
| pos=LB | 30 | +25.50% | 1/2 | 70.0% |
| disagreement_band=0.1-0.25 | 44 | +15.95% | 2/2 | 59.1% |
| disagreement_band=<0.1 | 41 | +3.52% | 1/2 | 61.0% |
| disagreement_band=>=0.25 | 5 | -201.65% | 0/2 | 20.0% |
| correction_direction=higher_or_equal | 34 | -22.01% | 1/2 | 38.2% |
| correction_direction=lower | 56 | +15.81% | 2/2 | 69.6% |
| interaction=pos:correction_direction=LB:higher_or_equal | 6 | -192.26% | 0/2 | 16.7% |
| interaction=pos:correction_direction=LB:lower | 24 | +55.19% | 2/2 | 83.3% |
| exposure_band=[0.0, 250.0) | 23 | +18.28% | 2/2 | 56.5% |
| exposure_band=[1000.0, inf) | 23 | -6.39% | 1/2 | 60.9% |
| exposure_band=[250.0, 1000.0) | 44 | +0.97% | 2/2 | 56.8% |

The source audit independently hashes the public snap-count tables and sums regular-season defensive snaps in draft and draft+1 seasons. All 90 pressure cases have positive observed defensive exposure. Multiplying the saved rate by these snaps and dividing by 100 reconstructs integer pressure counts within numerical tolerance, which checks that the explanatory denominator matches the inherited target. No estimate of routes, coverage snaps or pass-rush opportunities is inserted.

The lowest-exposure group, under 250 defensive snaps, improves 18.285% on 23 players. The 250–999 group improves 0.968% on 44; the group at least 1,000 worsens 6.387% on 23. Weighting the full pressure MSE by defensive snaps leaves a 5.171% improvement rather than 7.111%. The 24-linebacker/lowered subgroup improves 66.649% under exposure weighting and includes both small and substantial exposures. This helps distinguish that narrower pattern from a finding driven solely by low-exposure rate noise. It does not turn all defensive snaps into genuine pass-rush opportunities: linebacker usage in coverage and run defense still changes the interpretation of pressure rate.

Exposure is observed after the draft. Selecting a pre-draft prediction rule by a player's future defensive snaps would leak information. These exposure strata and weighted scores are descriptive changes of estimand, marked outcome-conditioned in the machine-readable results. Receiving efficiency has the same issue: its sample is already restricted to players with at least 30 observed NFL targets. Under target weighting its blend improves 3.316%, but that scores production among observed targets rather than all drafted receivers.

## Influence and robustness

The full pressure sample's total squared-loss reduction is 6.469332; its five largest positive contributions sum to 7.762986. Removing those five changes the pressure improvement to a 1.735% deterioration. The full opportunity gain similarly changes from +0.652% to −0.285% after removing its five largest positive contributors. Receiving remains only +0.181% after the analogous removal. This is an adversarial sensitivity calculation, not an alternative unbiased estimate: removal depends on realized errors and cannot be used to improve a headline score.

The 24-linebacker/lowered subgroup contributes 7.681905 in total loss reduction, exceeding the entire 90-player net gain. The remaining 66 players collectively lose. Removing the subgroup's five largest positive contributions leaves 19 players with a 33.108% reduction, a 78.947% individual win fraction and positive class mean gains in both cohorts. This narrower pattern survives the same influence check that removes the pooled advantage, while remaining exploratory and small. Player-level influence rows, including public names and exposures, are preserved outside public GitHub in the complete package; aggregate calculations and all subgroup outcomes are committed.

The script also reports every leave-one-class-out gain and enumerates sign flips of cohort mean gains. With two pressure cohorts, there are only four possible sign patterns. That enumeration is labelled a sensitivity under hypothetical independent symmetric class signs, not an assumption-free p-value. Fixed-prediction player bootstraps can look much more precise than the amount of independent cohort evidence warrants.

## Identity coverage and selection

The original predictions are reused exactly. Classifying their cases by the new strict identity ledger does not refit those predictions with the guarded data table and does not erase the original feature-link limitations. Among 1,454 opportunity cases, the 1,304 birth/name-verified players improve 3.097%, while the 148 unsupported identities worsen 14.003%; two ambiguous cases remain separate. The unsupported group has a negative final-family simultaneous player interval, but the overall association remains observational and spans differing classes, roles and source histories.

The audit standardizes gain contrasts over common class-by-coarse-role cells, requiring at least five examples on each side. Only 394 of 1,454 opportunity players lie in common support for the identity comparison. The standardized verified-minus-unsupported absolute gain is approximately 1.081858 on that subset. It cannot describe the excluded majority, establish a causal benefit from identity verification or license a post-hoc production gate. The pressure identity and recruiting-context contrasts have no class-role cells meeting this two-sided sample requirement; the report explicitly returns no standardized estimate rather than filling sparse cells with invented precision.

The recruitment-context indicator is still only corroborated context. It does not mean a 247-to-CFBD identity has been authoritatively verified, and no recruiting rating enters any predictor. Context-associated gains can reflect who has usable school history, position composition, exposure and name/birth coverage. Historical publication times are still missing. Current roster standing, age, status and draft metadata remain excluded. The stronger new identity infrastructure improves what can be audited; it has not retroactively made historical feature vintages provable.

## Simple controls and preserved failures

After the linebacker interaction was inspected, one additional baseline was evaluated on every target. It predicts a coarse-role mean shrunk toward the overall mean with fixed strength 20. At outer year Y it uses only labels from classes at most Y−2, and its training audit retains the latest class, player counts and prior mean. No shrinkage strength or role subgroup is selected by outer errors.

For role g, m_g = (sum of prior matured labels in g +20 times prior matured global mean)/(number of prior matured players in g +20). An unseen role uses the global mean. The receipt includes tests that changing unmatured labels cannot alter the corresponding prediction. This is a new retrospective control, not an untouched confirmation of its own performance.

| Target | Players | Conventional MSE | Blend MSE | Matured role-mean MSE | Role mean vs conventional gain |
| --- | ---: | ---: | ---: | ---: | ---: |
| target | 1454 | 3.848146467 | 3.823040336 | 3.978262400 | -3.381% |
| receiving_efficiency | 185 | 2.294024866 | 2.234386934 | 2.184476396 | +4.775% |
| pressure_target | 90 | 1.010819021 | 0.938937551 | 1.333895151 | -31.962% |

The simple role mean scores 2.184476 on receiving efficiency, compared with 2.234387 for the blend and 2.294025 for conventional inputs. Its 4.775% point improvement also beats the prior historical-college MSE 2.215969 and raw-college MSE 2.229361. Thus the receiving improvement against Combine is insufficient to establish value from richer custom metrics. The same simple control worsens opportunity 3.381% and pressure 31.962%, so it is not a universal replacement. Every result is retained; no endpoint is promoted merely because one comparison is favorable.

## Exact mathematical explanation

Let b be the conventional prediction, a the aggregate and d=b−a. The individual squared-error gain is

    (Y−b)²−(Y−a)² = 2(b−Y)d−d².

The correction helps when its alignment with baseline error exceeds its squared magnitude. In a prospect-observable context X, its conditional expected benefit is 2 E[(b−Y)d | X]−E[d² | X]. Positive mean downward correction alone is insufficient: its relationship with actual error and its size matter. The pressure sample's baseline signed error is +0.254876 and the blend's +0.173389. The selected linebacker subgroup makes the reduction in systematic overprediction particularly visible.

For K equally weighted expert forecasts p_j and their mean m,

    (1/K) sum_j (Y−p_j)² − (Y−m)² = (1/K) sum_j (p_j−m)².

This identity explains how individually worse source models can form a better average. Pressure's mean individual expert MSE is 1.076048, worse than the conventional 1.010819, while disagreement diversity subtracts 0.137110 to give ensemble MSE 0.938938. The improvement is an error-diversification effect, not proof a new biological variable was discovered. The earlier delayed forecaster is exactly an equal average for pressure because neither parity stream has an earlier eligible evaluated cohort. Opportunity and receiving adaptive changes are tiny; those earlier facts are preserved.

Every leave-one-expert-out equal average is reported as an ablation, not selected as a replacement. Pressure's best ablation in this inspected set omits the historical-only expert and improves 8.415% versus conventional; omitting conventional leaves only a 1.326% gain. Opportunity loses 1.611% when conventional is omitted. The conventional endpoint is an essential control and sometimes a useful ensemble member, even where its individual calibration is imperfect.

For uncertainty, draw 4,000 paired within-class player bootstraps with fixed seed 42871. The same resampling counts apply to all overlapping groups. For group g, bootstrap its mean gain, estimate its bootstrap standard error s_g, and take the 95th percentile c of the maximum absolute standardized centered bootstrap deviation across eligible groups. Report mean_gain_g ±c s_g. Eligibility requires at least ten players and two classes; smaller cells retain point estimates and explicitly unavailable simultaneous intervals. The final families contain 47 eligible opportunity groups, 26 receiving groups and 36 pressure groups. Correction is within each task, not across the whole adaptive research program.

This procedure measures conditional fixed-forecast player uncertainty. It assumes its resampling scheme is meaningful, does not model team dependence or historical source revisions, and is not a guarantee for future draft classes. The sole positive simultaneous opportunity stratum is defined by the realized outcome, making it unusable for pre-draft routing. Receiving has no positive simultaneous subgroup; pressure's selected linebacker/lowered interaction is the exploratory positive described above. The full machine-readable receipt retains every interval and every negative group.

## Reproduction and release

The complete source/data package preserves the previous 240 public archives, the exact frozen prospect and prediction inputs, the identity ledgers and guarded table, all new player-level stratification and influence outputs, and this source snapshot. Restricted movement tracking rows remain excluded. The generic mobile source builder verifies original source bytes; no APK or native executable upgrade is claimed. The research feed receives aggregate evidence under the existing movement result contract. API status and actual consumption are recorded separately from source commits.

```bash
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONPATH=python python scripts/stratify_scouting_patterns.py --players ../identity-replay/prospects.pkl --identity ../identity-derived --predictions ../identity-aggregate --cache ../scouting-public-inputs --out ../patterns-derived --receipt receipts/scouting_patterns/stratification.json
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONPATH=python python -m unittest discover -s python/tests -p 'test_scouting*.py'
python scripts/report_scouting_patterns.py
python scripts/export_explorer_live.py
```

The implementation tests the paired-loss contribution identity, diversity decomposition, correction decomposition, influence deletion, repeat-player rejection, nonfinite inputs, bootstrap reproducibility, exclusion of unsupported standardization cells, and outcome maturity of the role control. Source hashes and denominator reconstruction are checked during the real-data run. All earlier negative experiments and recruiting-availability blockers remain available. The next independent task is to test a prospect-observable reliability correction inside earlier chronological training folds and then on an untouched matured cohort, with adequate true pass-rush exposure if the intended interpretation is rushing ability.

## Complete descriptive group bank

The following tables include every group, including tiny, negative and outcome-conditioned cells. Extreme percentages in tiny cells may reflect nearly zero baseline loss. None is an instruction to deploy a subgroup selector. The JSON receipt additionally retains individual win fractions, signed error, exposure weighting, role-control comparisons, influence and support diagnostics.

### target — every reported group

| Group | Players | Gain | Positive classes | Outcome-conditioned | Simultaneous absolute-gain interval |
| --- | ---: | ---: | ---: | --- | --- |
| all | 1454 | +0.652% | 4/7 | False | [-0.1493546420042428, 0.19956690283837408] |
| draft_year=2018 | 208 | -3.133% | 0/1 | False | unavailable |
| draft_year=2019 | 213 | -7.241% | 0/1 | False | unavailable |
| draft_year=2020 | 226 | +11.440% | 1/1 | False | unavailable |
| draft_year=2021 | 193 | -3.451% | 0/1 | False | unavailable |
| draft_year=2022 | 218 | +5.939% | 1/1 | False | unavailable |
| draft_year=2023 | 189 | +1.318% | 1/1 | False | unavailable |
| draft_year=2024 | 207 | +1.412% | 1/1 | False | unavailable |
| pos=C | 31 | +5.450% | 3/5 | False | [-1.357840129437239, 1.9698562473611858] |
| pos=CB | 162 | +8.755% | 6/7 | False | [-0.1653953441878207, 0.7749588533246603] |
| pos=DB | 43 | -9.356% | 1/3 | False | [-1.5659249175220389, 0.7331978274994342] |
| pos=DE | 44 | -11.787% | 4/5 | False | [-1.405183293065893, 0.7025779343294559] |
| pos=DL | 85 | +2.267% | 2/3 | False | [-0.33962625657395795, 0.46698645496158486] |
| pos=DT | 68 | +1.376% | 2/5 | False | [-0.711745248366545, 0.833184989736244] |
| pos=EDGE | 80 | -4.965% | 4/5 | False | [-0.8467548308999379, 0.5149530439651749] |
| pos=FB | 1 | -4368.438% | 0/1 | False | unavailable |
| pos=G | 12 | +4.969% | 1/1 | False | unavailable |
| pos=ILB | 11 | -9.197% | 0/1 | False | unavailable |
| pos=LB | 120 | -5.423% | 2/7 | False | [-0.775368716972269, 0.4186728463566161] |
| pos=OG | 34 | +0.088% | 2/3 | False | [-0.6214043914284944, 0.6315939032211153] |
| pos=OL | 82 | +4.745% | 2/4 | False | [-0.4750475939529332, 0.9851568800871149] |
| pos=OLB | 13 | -14.836% | 0/2 | False | [-1.66001182101652, 0.8510853650287502] |
| pos=OT | 93 | -0.974% | 3/6 | False | [-0.6288784703921676, 0.5316288675344775] |
| pos=QB | 75 | -0.831% | 3/7 | False | [-1.256057725537577, 1.1376890627157021] |
| pos=RB | 118 | -3.342% | 4/7 | False | [-0.7297498308266536, 0.5659410297805773] |
| pos=S | 78 | +1.527% | 2/5 | False | [-0.4881459822453522, 0.6022870228349835] |
| pos=SAF | 17 | +3.103% | 1/1 | False | unavailable |
| pos=TE | 90 | +4.423% | 4/7 | False | [-0.5093818349245005, 0.7227810369990475] |
| pos=WR | 197 | +5.000% | 5/7 | False | [-0.3714408443794254, 0.6760818892010364] |
| role=DB | 283 | +3.431% | 5/7 | False | [-0.23125099788554157, 0.4851203433809028] |
| role=DL | 277 | -2.047% | 4/7 | False | [-0.41456987586123323, 0.27603103303417037] |
| role=FB | 1 | -4368.438% | 0/1 | False | unavailable |
| role=LB | 144 | -6.831% | 2/7 | False | [-0.8538276221582732, 0.3366807460428438] |
| role=OL | 252 | +2.180% | 4/7 | False | [-0.2712554754610551, 0.5028688358962479] |
| role=QB | 75 | -0.831% | 3/7 | False | [-1.256057725537577, 1.1376890627157021] |
| role=RB | 118 | -3.342% | 4/7 | False | [-0.7297498308266536, 0.5659410297805773] |
| role=SAF | 17 | +3.103% | 1/1 | False | unavailable |
| role=TE | 90 | +4.423% | 4/7 | False | [-0.5093818349245005, 0.7227810369990475] |
| role=WR | 197 | +5.000% | 5/7 | False | [-0.3714408443794254, 0.6760818892010364] |
| identity_status=ambiguous | 2 | -21.654% | 1/2 | False | unavailable |
| identity_status=unsupported | 148 | -14.003% | 2/7 | False | [-1.4988215169116645, -0.011323279440052292] |
| identity_status=verified_name_birth | 1304 | +3.097% | 5/7 | False | [-0.0583412913303913, 0.28615787116498054] |
| recruit_context=False | 377 | -6.901% | 3/7 | False | [-0.7475173727142848, 0.14004075962335932] |
| recruit_context=True | 1077 | +3.837% | 5/7 | False | [-0.03247470326647928, 0.31290860334828596] |
| college_seasons=0 | 184 | +2.380% | 3/7 | False | [-0.3332084077290257, 0.5893110657547372] |
| college_seasons=1 | 86 | -2.207% | 4/7 | False | [-0.6598111406553061, 0.49118486058448807] |
| college_seasons=2 | 227 | -3.593% | 2/7 | False | [-0.6679928689226046, 0.3697172826713705] |
| college_seasons=3 | 957 | +1.621% | 5/7 | False | [-0.15383150503438686, 0.2667846464567656] |
| combine_missing=0 | 392 | -0.264% | 2/7 | False | [-0.34885641602532547, 0.3295364270843619] |
| combine_missing=1-2 | 459 | -1.094% | 4/7 | False | [-0.33298225726797154, 0.24292169142736847] |
| combine_missing=3+ | 603 | +2.683% | 6/7 | False | [-0.18612532001820692, 0.38831414694776145] |
| disagreement_band=0.1-0.25 | 79 | -4.097% | 3/6 | False | [-2.2550089268455498, 1.7625277587521626] |
| disagreement_band=<0.1 | 1375 | +1.093% | 3/7 | False | [-0.10499756398975696, 0.18639002910408747] |
| correction_direction=higher_or_equal | 988 | +0.955% | 4/7 | False | [-0.19510275948444547, 0.27090195325801014] |
| correction_direction=lower | 466 | -0.056% | 3/7 | False | [-0.24064269690557594, 0.23660626730159523] |
| prediction_band=[-inf, 6.217) | 1275 | +0.625% | 4/7 | False | [-0.16635522269260736, 0.21613143927895848] |
| prediction_band=[6.217, 7.601) | 179 | +0.922% | 4/7 | False | [-0.40048077177395675, 0.45379893437300217] |
| class_position=2018:C | 7 | -18.643% | 0/1 | False | unavailable |
| class_position=2018:CB | 21 | +21.069% | 1/1 | False | unavailable |
| class_position=2018:DB | 1 | +57.007% | 1/1 | False | unavailable |
| class_position=2018:DE | 12 | -42.728% | 0/1 | False | unavailable |
| class_position=2018:DT | 17 | -6.122% | 0/1 | False | unavailable |
| class_position=2018:EDGE | 14 | +10.617% | 1/1 | False | unavailable |
| class_position=2018:FB | 1 | -4368.438% | 0/1 | False | unavailable |
| class_position=2018:ILB | 11 | -9.197% | 0/1 | False | unavailable |
| class_position=2018:LB | 3 | -17.721% | 0/1 | False | unavailable |
| class_position=2018:OG | 9 | -5.214% | 0/1 | False | unavailable |
| class_position=2018:OL | 2 | -24.385% | 0/1 | False | unavailable |
| class_position=2018:OLB | 9 | -9.509% | 0/1 | False | unavailable |
| class_position=2018:OT | 16 | -0.936% | 0/1 | False | unavailable |
| class_position=2018:QB | 12 | -21.759% | 0/1 | False | unavailable |
| class_position=2018:RB | 16 | +19.429% | 1/1 | False | unavailable |
| class_position=2018:S | 16 | -4.876% | 0/1 | False | unavailable |
| class_position=2018:TE | 15 | +48.917% | 1/1 | False | unavailable |
| class_position=2018:WR | 26 | +10.243% | 1/1 | False | unavailable |
| class_position=2019:CB | 24 | +7.954% | 1/1 | False | unavailable |
| class_position=2019:DL | 28 | -4.535% | 0/1 | False | unavailable |
| class_position=2019:EDGE | 18 | -17.407% | 0/1 | False | unavailable |
| class_position=2019:LB | 20 | -7.211% | 0/1 | False | unavailable |
| class_position=2019:OL | 12 | -10.430% | 0/1 | False | unavailable |
| class_position=2019:OT | 22 | -2.034% | 0/1 | False | unavailable |
| class_position=2019:QB | 11 | -16.654% | 0/1 | False | unavailable |
| class_position=2019:RB | 20 | -25.538% | 0/1 | False | unavailable |
| class_position=2019:S | 18 | +38.555% | 1/1 | False | unavailable |
| class_position=2019:TE | 16 | -15.320% | 0/1 | False | unavailable |
| class_position=2019:WR | 24 | -1.388% | 0/1 | False | unavailable |
| class_position=2020:CB | 23 | +22.856% | 1/1 | False | unavailable |
| class_position=2020:DL | 36 | +10.315% | 1/1 | False | unavailable |
| class_position=2020:LB | 31 | +8.170% | 1/1 | False | unavailable |
| class_position=2020:OL | 41 | +11.927% | 1/1 | False | unavailable |
| class_position=2020:QB | 11 | +19.102% | 1/1 | False | unavailable |
| class_position=2020:RB | 15 | +17.803% | 1/1 | False | unavailable |
| class_position=2020:S | 21 | -3.840% | 0/1 | False | unavailable |
| class_position=2020:TE | 11 | -11.846% | 0/1 | False | unavailable |
| class_position=2020:WR | 37 | +11.457% | 1/1 | False | unavailable |
| class_position=2021:C | 2 | -764.327% | 0/1 | False | unavailable |
| class_position=2021:CB | 11 | -26.640% | 0/1 | False | unavailable |
| class_position=2021:DB | 28 | -9.155% | 0/1 | False | unavailable |
| class_position=2021:DE | 12 | +0.114% | 1/1 | False | unavailable |
| class_position=2021:DL | 21 | +7.777% | 1/1 | False | unavailable |
| class_position=2021:DT | 3 | +48.135% | 1/1 | False | unavailable |
| class_position=2021:LB | 15 | -25.009% | 0/1 | False | unavailable |
| class_position=2021:OL | 27 | +5.922% | 1/1 | False | unavailable |
| class_position=2021:OLB | 4 | -34.154% | 0/1 | False | unavailable |
| class_position=2021:OT | 4 | +54.611% | 1/1 | False | unavailable |
| class_position=2021:QB | 9 | +18.286% | 1/1 | False | unavailable |
| class_position=2021:RB | 16 | +10.122% | 1/1 | False | unavailable |
| class_position=2021:S | 9 | -4.440% | 0/1 | False | unavailable |
| class_position=2021:TE | 7 | +30.528% | 1/1 | False | unavailable |
| class_position=2021:WR | 25 | -29.593% | 0/1 | False | unavailable |
| class_position=2022:C | 7 | +13.808% | 1/1 | False | unavailable |
| class_position=2022:CB | 28 | +11.822% | 1/1 | False | unavailable |
| class_position=2022:DE | 11 | +4.410% | 1/1 | False | unavailable |
| class_position=2022:DT | 16 | +20.432% | 1/1 | False | unavailable |
| class_position=2022:EDGE | 15 | +17.128% | 1/1 | False | unavailable |
| class_position=2022:LB | 19 | -8.153% | 0/1 | False | unavailable |
| class_position=2022:OG | 20 | +0.629% | 1/1 | False | unavailable |
| class_position=2022:OT | 19 | +2.224% | 1/1 | False | unavailable |
| class_position=2022:QB | 8 | -0.841% | 0/1 | False | unavailable |
| class_position=2022:RB | 21 | -2.087% | 0/1 | False | unavailable |
| class_position=2022:S | 14 | +1.991% | 1/1 | False | unavailable |
| class_position=2022:TE | 15 | +19.961% | 1/1 | False | unavailable |
| class_position=2022:WR | 25 | +12.156% | 1/1 | False | unavailable |
| class_position=2023:C | 7 | +4.135% | 1/1 | False | unavailable |
| class_position=2023:CB | 26 | +10.863% | 1/1 | False | unavailable |
| class_position=2023:DB | 14 | -11.670% | 0/1 | False | unavailable |
| class_position=2023:DE | 6 | +2.288% | 1/1 | False | unavailable |
| class_position=2023:DT | 14 | -57.683% | 0/1 | False | unavailable |
| class_position=2023:EDGE | 17 | +2.802% | 1/1 | False | unavailable |
| class_position=2023:LB | 14 | +7.657% | 1/1 | False | unavailable |
| class_position=2023:OG | 5 | +2.268% | 1/1 | False | unavailable |
| class_position=2023:OT | 15 | -10.391% | 0/1 | False | unavailable |
| class_position=2023:QB | 13 | -4.873% | 0/1 | False | unavailable |
| class_position=2023:RB | 14 | +20.790% | 1/1 | False | unavailable |
| class_position=2023:TE | 15 | -7.831% | 0/1 | False | unavailable |
| class_position=2023:WR | 29 | +38.759% | 1/1 | False | unavailable |
| class_position=2024:C | 8 | +0.004% | 1/1 | False | unavailable |
| class_position=2024:CB | 29 | +1.722% | 1/1 | False | unavailable |
| class_position=2024:DE | 3 | +24.401% | 1/1 | False | unavailable |
| class_position=2024:DT | 18 | -0.515% | 0/1 | False | unavailable |
| class_position=2024:EDGE | 16 | +5.912% | 1/1 | False | unavailable |
| class_position=2024:G | 12 | +4.969% | 1/1 | False | unavailable |
| class_position=2024:LB | 18 | -7.201% | 0/1 | False | unavailable |
| class_position=2024:OT | 17 | +4.262% | 1/1 | False | unavailable |
| class_position=2024:QB | 11 | +2.979% | 1/1 | False | unavailable |
| class_position=2024:RB | 16 | -7.258% | 0/1 | False | unavailable |
| class_position=2024:SAF | 17 | +3.103% | 1/1 | False | unavailable |
| class_position=2024:TE | 11 | +1.609% | 1/1 | False | unavailable |
| class_position=2024:WR | 31 | +1.688% | 1/1 | False | unavailable |
| outcome_band=[-inf, 6.217) | 683 | -9.392% | 2/7 | True | [-0.8199959575107677, -0.20142261922164184] |
| outcome_band=[6.217, 7.601) | 726 | +22.394% | 7/7 | True | [0.3578639875041383, 0.6776812475736793] |
| outcome_band=[7.601, 8.294) | 45 | +4.643% | 5/7 | True | [-0.6040716708685356, 1.022553326303357] |
| exposure_band=missing | 1454 | +0.652% | 4/7 | True | [-0.1493546420042428, 0.19956690283837408] |

### receiving_efficiency — every reported group

| Group | Players | Gain | Positive classes | Outcome-conditioned | Simultaneous absolute-gain interval |
| --- | ---: | ---: | ---: | --- | --- |
| all | 185 | +2.600% | 5/7 | False | [-0.06358733629877851, 0.1828632008115123] |
| draft_year=2018 | 28 | +5.798% | 1/1 | False | unavailable |
| draft_year=2019 | 25 | +8.725% | 1/1 | False | unavailable |
| draft_year=2020 | 32 | +1.464% | 1/1 | False | unavailable |
| draft_year=2021 | 17 | -4.342% | 0/1 | False | unavailable |
| draft_year=2022 | 28 | -1.106% | 0/1 | False | unavailable |
| draft_year=2023 | 34 | +1.299% | 1/1 | False | unavailable |
| draft_year=2024 | 21 | +3.407% | 1/1 | False | unavailable |
| pos=TE | 50 | -2.033% | 2/7 | False | [-0.12399458586248596, 0.07177723029231592] |
| pos=WR | 135 | +3.426% | 5/7 | False | [-0.07173688095747364, 0.25452875290832] |
| role=TE | 50 | -2.033% | 2/7 | False | [-0.12399458586248596, 0.07177723029231592] |
| role=WR | 135 | +3.426% | 5/7 | False | [-0.07173688095747364, 0.25452875290832] |
| identity_status=unsupported | 11 | -13.450% | 1/5 | False | [-0.6738835312651004, 0.09038849017484746] |
| identity_status=verified_name_birth | 174 | +3.556% | 5/7 | False | [-0.045628753204596806, 0.20933266347384127] |
| recruit_context=False | 42 | -1.155% | 3/7 | False | [-0.2908337785941341, 0.23665473331176118] |
| recruit_context=True | 143 | +3.735% | 5/7 | False | [-0.05592646808779218, 0.2261471312816063] |
| college_seasons=0 | 1 | -421.339% | 0/1 | False | unavailable |
| college_seasons=1 | 2 | -48.224% | 0/2 | False | unavailable |
| college_seasons=2 | 25 | +12.270% | 3/6 | False | [-0.08733921144792567, 0.6727437738901374] |
| college_seasons=3 | 157 | +1.130% | 3/7 | False | [-0.1040074886169268, 0.15642112871300115] |
| combine_missing=0 | 53 | +6.998% | 5/7 | False | [-0.12132655986934954, 0.34208217801185564] |
| combine_missing=1-2 | 60 | +3.212% | 4/7 | False | [-0.16314015767637266, 0.3626176591539674] |
| combine_missing=3+ | 72 | -0.519% | 3/7 | False | [-0.16009650684942986, 0.13783729969175276] |
| disagreement_band=<0.1 | 185 | +2.600% | 5/7 | False | [-0.06358733629877851, 0.1828632008115123] |
| correction_direction=higher_or_equal | 86 | +4.771% | 4/7 | False | [-0.05836488502682159, 0.26065612587964493] |
| correction_direction=lower | 99 | +0.964% | 5/7 | False | [-0.15955710355353658, 0.20671860074053605] |
| prediction_band=[6.0, 8.0) | 169 | +3.475% | 5/7 | False | [-0.024727312281674213, 0.18838442422902177] |
| prediction_band=[8.0, 10.0) | 16 | -10.578% | 1/3 | False | [-1.0683491022492566, 0.7188480407338825] |
| class_position=2018:TE | 10 | -4.226% | 0/1 | False | unavailable |
| class_position=2018:WR | 18 | +11.338% | 1/1 | False | unavailable |
| class_position=2019:TE | 7 | +8.478% | 1/1 | False | unavailable |
| class_position=2019:WR | 18 | +8.765% | 1/1 | False | unavailable |
| class_position=2020:TE | 5 | +13.176% | 1/1 | False | unavailable |
| class_position=2020:WR | 27 | +1.052% | 1/1 | False | unavailable |
| class_position=2021:TE | 5 | -3.150% | 0/1 | False | unavailable |
| class_position=2021:WR | 12 | -4.865% | 0/1 | False | unavailable |
| class_position=2022:TE | 9 | -9.952% | 0/1 | False | unavailable |
| class_position=2022:WR | 19 | -0.320% | 0/1 | False | unavailable |
| class_position=2023:TE | 10 | -5.047% | 0/1 | False | unavailable |
| class_position=2023:WR | 24 | +2.509% | 1/1 | False | unavailable |
| class_position=2024:TE | 4 | -4.523% | 0/1 | False | unavailable |
| class_position=2024:WR | 17 | +4.153% | 1/1 | False | unavailable |
| outcome_band=[-inf, 6.0) | 24 | +5.003% | 5/7 | True | [-0.14709439322226875, 0.8589627562207278] |
| outcome_band=[10.0, inf) | 11 | -5.498% | 0/5 | True | [-1.3091399664423826, 0.2502959511855505] |
| outcome_band=[6.0, 8.0) | 94 | +5.849% | 5/7 | True | [-0.02827284835110222, 0.09734455075557844] |
| outcome_band=[8.0, 10.0) | 56 | +5.495% | 5/7 | True | [-0.173892812371741, 0.35488814031276106] |
| exposure_band=[0.0, 60.0) | 52 | -1.008% | 3/7 | True | [-0.21742777161789742, 0.16010368804838623] |
| exposure_band=[120.0, inf) | 75 | +6.167% | 5/7 | True | [-0.09753584415825961, 0.2948927015775565] |
| exposure_band=[60.0, 120.0) | 58 | +3.272% | 3/7 | True | [-0.1613258127083816, 0.3379658639846415] |

### pressure_target — every reported group

| Group | Players | Gain | Positive classes | Outcome-conditioned | Simultaneous absolute-gain interval |
| --- | ---: | ---: | ---: | --- | --- |
| all | 90 | +7.111% | 2/2 | False | [-0.14964654772617436, 0.2934094877572103] |
| draft_year=2023 | 45 | +0.267% | 1/1 | False | unavailable |
| draft_year=2024 | 45 | +13.371% | 1/1 | False | unavailable |
| pos=DE | 8 | +0.031% | 1/2 | False | unavailable |
| pos=DT | 23 | -5.641% | 1/2 | False | [-0.43898702330975853, 0.339621853811731] |
| pos=EDGE | 29 | +8.122% | 2/2 | False | [-0.3284595956999153, 0.5750546312159824] |
| pos=LB | 30 | +25.498% | 1/2 | False | [-0.2480892604881013, 0.5169604067700388] |
| role=DL | 60 | +3.242% | 2/2 | False | [-0.23901725243782826, 0.3202260893434134] |
| role=LB | 30 | +25.498% | 1/2 | False | [-0.2480892604881013, 0.5169604067700388] |
| identity_status=unsupported | 9 | +19.569% | 2/2 | False | unavailable |
| identity_status=verified_name_birth | 81 | +5.296% | 1/2 | False | [-0.1842804699287776, 0.2881004462315209] |
| recruit_context=False | 19 | -12.910% | 1/2 | False | [-0.7794418586458634, 0.4676970885604703] |
| recruit_context=True | 71 | +13.862% | 2/2 | False | [-0.09306886778974677, 0.3587282372885595] |
| college_seasons=1 | 1 | -8.583% | 0/1 | False | unavailable |
| college_seasons=2 | 13 | +18.379% | 2/2 | False | [-0.3311134791954221, 0.5042810514532919] |
| college_seasons=3 | 76 | +7.305% | 2/2 | False | [-0.17642699412575003, 0.32919948075131] |
| combine_missing=0 | 8 | +8.660% | 2/2 | False | unavailable |
| combine_missing=1-2 | 23 | +7.472% | 2/2 | False | [-0.2970554809188009, 0.4710486622188704] |
| combine_missing=3+ | 59 | +6.254% | 1/2 | False | [-0.21839950459635304, 0.3144981202156557] |
| disagreement_band=0.1-0.25 | 44 | +15.948% | 2/2 | False | [-0.13410836756609873, 0.48604210038931245] |
| disagreement_band=<0.1 | 41 | +3.516% | 1/2 | False | [-0.270644960073509, 0.34109539394059896] |
| disagreement_band=>=0.25 | 5 | -201.655% | 0/2 | False | unavailable |
| correction_direction=higher_or_equal | 34 | -22.007% | 1/2 | False | [-0.43079542980962054, 0.15999216219377393] |
| correction_direction=lower | 56 | +15.806% | 2/2 | False | [-0.1006356265492783, 0.4960994783659216] |
| prediction_band=[-inf, 1.0) | 12 | -81.301% | 1/2 | False | [-0.7822590697858651, 0.4485367299054037] |
| prediction_band=[1.0, 2.0) | 32 | +17.794% | 1/2 | False | [-0.15673383207574565, 0.43698512979210247] |
| prediction_band=[2.0, 3.0) | 39 | +9.622% | 2/2 | False | [-0.23159552577502562, 0.5150273387654712] |
| prediction_band=[3.0, inf) | 7 | -26.230% | 0/2 | False | unavailable |
| class_position=2023:DE | 6 | -16.805% | 0/1 | False | unavailable |
| class_position=2023:DT | 10 | -32.708% | 0/1 | False | unavailable |
| class_position=2023:EDGE | 16 | +11.450% | 1/1 | False | unavailable |
| class_position=2023:LB | 13 | -6.711% | 0/1 | False | unavailable |
| class_position=2024:DE | 2 | +12.187% | 1/1 | False | unavailable |
| class_position=2024:DT | 13 | +3.050% | 1/1 | False | unavailable |
| class_position=2024:EDGE | 13 | +3.193% | 1/1 | False | unavailable |
| class_position=2024:LB | 17 | +56.027% | 1/1 | False | unavailable |
| interaction=correction_direction:disagreement_band=higher_or_equal:0.1-0.25 | 18 | -6.391% | 1/2 | False | [-0.4342851948097506, 0.3457380857213729] |
| interaction=correction_direction:disagreement_band=higher_or_equal:<0.1 | 11 | -15.339% | 1/2 | False | [-0.3479728010871582, 0.14992046423541902] |
| interaction=correction_direction:disagreement_band=higher_or_equal:>=0.25 | 5 | -201.655% | 0/2 | False | unavailable |
| interaction=correction_direction:disagreement_band=lower:0.1-0.25 | 26 | +23.668% | 2/2 | False | [-0.10777296496827937, 0.7646549729610567] |
| interaction=correction_direction:disagreement_band=lower:<0.1 | 30 | +7.457% | 2/2 | False | [-0.32317691109692476, 0.492078360894252] |
| interaction=pos:correction_direction=DE:higher_or_equal | 3 | -241.161% | 0/1 | False | unavailable |
| interaction=pos:correction_direction=DE:lower | 5 | +16.507% | 2/2 | False | unavailable |
| interaction=pos:correction_direction=DT:higher_or_equal | 11 | -3.594% | 1/2 | False | [-0.39220758435846986, 0.3574045102671118] |
| interaction=pos:correction_direction=DT:lower | 12 | -6.372% | 0/2 | False | [-0.7567245676481302, 0.5981774773606556] |
| interaction=pos:correction_direction=EDGE:higher_or_equal | 14 | +7.026% | 1/2 | False | [-0.2780553233088467, 0.4085411670067411] |
| interaction=pos:correction_direction=EDGE:lower | 15 | +8.580% | 1/2 | False | [-0.6476367626014669, 1.0026003771478287] |
| interaction=pos:correction_direction=LB:higher_or_equal | 6 | -192.263% | 0/2 | False | unavailable |
| interaction=pos:correction_direction=LB:lower | 24 | +55.189% | 2/2 | False | [0.003694537078522131, 0.6364641881518034] |
| outcome_band=[-inf, 1.0) | 33 | +22.746% | 2/2 | True | [-0.13435680118962323, 0.6941491651146647] |
| outcome_band=[1.0, 2.0) | 24 | +12.863% | 2/2 | True | [-0.2607512037249732, 0.4011008103212007] |
| outcome_band=[2.0, 3.0) | 16 | -105.612% | 0/2 | True | [-0.510001729930714, 0.19097435268058346] |
| outcome_band=[3.0, inf) | 17 | -5.449% | 0/2 | True | [-0.7254206219190966, 0.5019832143284788] |
| exposure_band=[0.0, 250.0) | 23 | +18.285% | 2/2 | True | [-0.19542042228822798, 0.8265970858010435] |
| exposure_band=[1000.0, inf) | 23 | -6.387% | 1/2 | True | [-0.4992564393117331, 0.4021886556497047] |
| exposure_band=[250.0, 1000.0) | 44 | +0.968% | 2/2 | True | [-0.27621268730095366, 0.2910799683515249] |
