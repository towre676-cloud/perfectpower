# Broader scouting data and custom metrics

October 15, 2026. Retrospective development release. A broader population, source-aware metric compiler and chronological experiment are complete. No custom-metric scouting edge is validated.

## What changed

The previous motion experiment covered 74 defensive-front rookies. This release builds an exactly linked population of **2,533 drafted Combine invitees across 2013–2024**, preserving missing athletic tests. **1,454 players in 2018–2024** receive chronological out-of-class predictions; earlier classes supply matured training labels. The public source pool contains **8,968 Combine-labeled records from 2000–2026**. These are records, not a claim to possess trajectories or valid NFL outcomes for every athlete.

The acquisition contains **66 public archives in nine table families**, including 1,637,447 credited college play rows, 555,417 college box-score rows, and 113,417 distinct college roster IDs. That last number describes a source pool, not labeled scouting examples. The empirical metric bank uses 42 archives; 24 additional roster/recruiting archives were acquired and audited but do not enter its reported models.

The official-data bridge additionally attaches source-defined custom metrics to **510 authorized BDB players**, of whom 482 have exact public PFR links and 399 have name-verified college features. This is feature integration, not a new 510-player predictive validation. Restricted rows remain private. PerfectJet's current main at `01fe017c41d7bdc7352be84fa6d4654a9d0c29c7` and its concurrent experiments were not changed.

## What the experiment says

After the source-range guard, adding raw historical college information reduces pooled log-snap MSE by **2.534%** versus a tuned Combine/age/position ridge. Its paired fixed-prediction absolute-gain interval is [-0.002305444318021386, 0.19522756843506087], which includes zero. The custom bank changes error by **-0.012%** relative to those broader raw inputs: no incremental custom-metric gain. Additional information and nonlinear repackaging of existing information are different contributions.

The narrow positive point result concerns **NFL opportunity**, measured as log(1 + first-two-seasons regular-season offensive plus defensive snaps). It is not pressure-rate prediction, pure athletic ability, causal value, betting profit or a demonstration that an NFL team can draft better. The fixed-prediction interval excludes refitting and new-class uncertainty. The guarded run follows an inspected failed run and is adaptive development, not untouched confirmation. All classes in the earlier movement study were already examined elsewhere.

| Held-out task | Players | Broader raw vs Combine | Custom vs broader raw | Custom vs draft-control baseline |
| --- | ---: | ---: | ---: | ---: |
| Two-season opportunity | 1454 | +2.534% | -0.012% | +0.000% |
| College-linked opportunity control | 517 | -0.301% | -0.033% | -0.219% |
| Defensive pressure / 100 defensive snaps | 90 | -2.982% | +0.046% | -12.627% |

Positive percentages mean lower error. These target scales and populations differ; percentages must not be pooled across tasks. In the college-linked control, the broad raw gain disappears. In the pressure comparison, only 90 players in two held-out classes have sufficient matured training history and unambiguous advanced outcomes; class direction changes. The pressure target divides season pressures by all defensive snaps, not pass-rush opportunities. It is not the original BDB pressure-event target and cannot be called a replicated movement result.

The all-player broad-raw gains by draft class are:

| Class | Players | Relative gain | Baseline MSE | Broad-raw MSE |
| --- | ---: | ---: | ---: | ---: |
| 2018 | 208 | -2.249% | 4.2466 | 4.34211 |
| 2019 | 213 | -0.010% | 4.75957 | 4.76006 |
| 2020 | 226 | +4.651% | 3.28606 | 3.13322 |
| 2021 | 193 | +2.086% | 3.18806 | 3.12155 |
| 2022 | 218 | +11.445% | 4.27629 | 3.78685 |
| 2023 | 189 | +0.228% | 2.78076 | 2.77441 |
| 2024 | 207 | +0.674% | 4.1222 | 4.09439 |

The full receipt also includes a source-availability-only model, every penalty/shrinkage choice and a diagnostic equal-count top quartile within position/class. The ranking diagnostic measures subsequent usage, not decision profit, and did not select models. No family was selected from its outer error. The draft controls add log overall draft pick and answer a separate post-draft question: whether these measurements add to the information reflected in NFL teams' draft decisions. They are not pre-draft predictors. No dependable custom increment beyond these controls is established.

## The metric definitions

The source compiler retains all raw body/timed measurements plus age at a fixed April 25 draft date, source Combine position, and explicit missingness. It excludes the public table's draft team/round/pick from pre-draft inputs; draft pick appears only in named control models. Immutable birth date is used, but latest NFL body measurements, current NFL position, career totals, status, survival, injuries and retrospective text are not inputs.

Physical transformations include body-mass index, mean 40-yard speed, the constant-acceleration timing proxy 2d/t², takeoff-speed proxy sqrt(2gh), mass-times-takeoff-speed, vertical energy proxy mgh, relative broad jump, vertical/broad jump ratio, shuttle/forty and cone/forty ratios, bench repetitions per kilogram and mass/t⁴. These describe recorded tests under assumptions; they are not direct measurements of acceleration, braking force, muscle power or NFL performance. For the restricted bridge, first-ten and later-thirty mean speeds add actual split information. Deterministic transforms alone create no new observations. These elementary identities and established score-like transforms are not presented as novel physical laws.

College game-category means use only recorded categories. Missing defensive categories are unknown, not zero sacks or zero tackles. Production shares divide a player's recorded statistic by captured teammate totals in the same game; the result is explicitly a **captured-data share**, not guaranteed complete college market share. Passing completions in the participant file are conditioned on credited completions, not all dropbacks. Credit-event coverage does not supply on-field opportunity counts for nonparticipants.

For rushing, receptions and credited completions, a source play succeeds when yards gained reach 50% of distance on first down, 70% on second, and 100% on third/fourth. Explosive thresholds are ten rushing yards or fifteen receiving/completion yards. With s successes in n valid credited observations and source-season league rate p, the stabilized rate is (s + 20p)/(n + 20). Its beta-model variance is (s + 20p)(n − s + 20(1−p))/((n+20)²(n+21)). The prior strength is fixed at twenty, not selected using NFL outcomes. This is operational smoothing, not calibrated physiological uncertainty.

Opponent adjustment subtracts the opponent's observed success rate against **other games**, using league rate when fewer than twenty other credited observations exist. Excluding the current game prevents a player's own play from defining its comparison baseline. These adjustments use college outcomes already available before the draft, never future NFL targets. Explicit lag-one, lag-two and lag-three seasons remain separate, and final-minus-prior production changes form trajectory features. Missing endpoints do not become fabricated trends.

## Time, identities and sample construction

A prospect's college season must be strictly earlier than draft year. Two-year NFL outcomes require a two-year class gap: a model predicting class Y trains on classes at most Y−2, whose first two NFL seasons ended by the prospect's draft. The same maturity gap holds in inner chronological tuning. Entire PFR identities are separated; duplicate or ambiguous IDs are rejected. The initial 2015 floor was expanded to 2013/2014 **before outcome evaluation**, because the 2018 outer test otherwise had no matured chronological inner tuning window. Earlier missing college sources remain missing.

College joining requires an exact ESPN crosswalk ID plus a normalized exact Combine or NFL display name. Normalization removes punctuation, accents and generational suffixes; it does not guess nicknames or perform fuzzy matching. Source-name failures and ambiguous ESPN mappings stay unjoined. Only 1,204 of 2,533 prospects have verified college features in the source window. An NFL-maintained historical ID crosswalk is not a prospective all-prospect identity registry, so source availability can encode selection. The availability-only and matched-college controls diagnose this risk rather than making it disappear.

The broader public Combine pool includes undrafted or unmatched people, but this study's outcome population is drafted invitees with exact PFR/year links. Unmatched people are not labeled NFL failures. Valid drafted identities absent from audited complete NFL snap seasons receive zero observed scrimmage snaps under source identifier consistency; 211 such outcomes remain in the population. This does not solve selection bias for all college players.

Regular-season snap outcomes were audited for 32 teams and every expected completed game, 2013–2025: 256 games before the 17-game schedule, 272 thereafter, and 271 in 2022 due to the canceled game. The advertised 2012 file is empty and is excluded. Player/game/team duplicates fail preparation. Advanced pressure data contain 88 ambiguous player-season groups; all ambiguous groups are rejected rather than guessed or summed. A missing advanced row with positive defensive snaps leaves pressure unknown. No invented zero pressure is used.

Older college defensive box coverage is sparse and changes sharply across seasons. Box and participant files also cover different game sets. Roster archives contain fields resembling current age, status and draft metadata even on historical rows; those columns are not fed into the model. Recruiting recruit_id values and roster cfbd_recruit_ids use distinct namespaces. Both archives were acquired, but no fabricated numeric-ID join or fuzzy-name join was made. A verified namespace bridge and timestamp audit remain needed before recruiting trajectories can be evaluated.

## Preserved failure and source-only guard

The initial unguarded bank is retained in `evaluation_initial.json` with exact initial source under `research/scouting_expansion/initial`. Its broad model increased pooled opportunity error by roughly 83%. A 2018 log-snap prediction reached 37.25, far outside observed outcomes. Sparse early feature support and distribution change made unrestricted standardized regression extrapolate. The first run is a failure of that estimator on these sources, not evidence that every college signal is useless.

The guard masks numeric values with fewer than max(20, 10% of training rows) finite observations and clips standardized values to the training first/99th percentiles. Missingness remains visible. Every bound and support decision is fitted only on the current training partition, and the same guard applies to all model families. The declared feature bank, ridge penalties and shrinkage values remain fixed. The guard was added after inspection, so its result is explicitly adaptive. It prevents unsupported source magnitude from masquerading as certainty; it cannot guarantee predictive improvement.

Five ridge penalties, from one to 10,000, are tuned on the latest feasible earlier chronological classes. The custom model is a mixture of separately tuned broad-raw and augmented ridge predictions, using shrinkage zero, one quarter, one half or one. Inner selection prefers zero unless the best paired improvement exceeds one estimated standard error. This is a heuristic with correlated fold errors and multiple candidates, not a risk-dominance theorem. At the earliest inner point without another tuning window, penalty 100 is fixed by the implementation. Zero preserves the relevant baseline exactly; it does not imply that the baseline itself beats the simpler Combine model.

## Reproduction and handoff

Install `requirements-scouting.txt`. Acquire with `python scripts/acquire_scouting_sources.py --cache /path/to/scouting_inputs`, prepare with `python scripts/prepare_scouting_expansion.py --cache /path/to/scouting_inputs --out /path/to/scouting_derived --aggregate receipts/scouting_expansion/population.json`, and run `OPENBLAS_NUM_THREADS=1 python scripts/run_scouting_expansion.py --players /path/to/scouting_derived/prospects.pkl --private-out /path/to/scouting_results --aggregate receipts/scouting_expansion/evaluation.json`. Player data must stay outside the checkout. `scripts/audit_scouting_sources.py` verifies every downloaded byte hash and source table. `scripts/replay_initial_scouting.py` replays the exact pre-guard core with the current CLI; its metadata labels the loaded original core. `make scouting-metrics-test` checks units, missing categories, identity ambiguity, source-name verification, source-only clipping, college cutoffs, opponent exclusion, maturity and held-player invariance. The original movement tests also pass.

Public archives are saved separately from the complete code snapshot, with acquisition URLs, timestamps and hashes. The private continuation preserves the authorized official bridge and all saved predictions. Raw restricted BDB data and athlete-level restricted outputs are excluded from GitHub and the public source ZIP. Historical source tables may have been revised since the games; this is a fixed retrospective snapshot, not an archived-as-of vintage database. The installed native engine and live feed are distinct; no APK rebuild or deployment of a new NFL scouting model is claimed.

## What should happen next

The defensible next unit of work is a **prospect identity and opportunity layer**: verify roster/recruit namespaces, establish timestamped pre-draft coverage, and obtain proper college snap/route/pass-rush denominators and role/context labels. That would make metrics such as disruption per genuine rush opportunity and production above recruitment expectation meaningful. The current credited-event corpus does not supply those denominators, and full historical tracking cannot be invented for the 8,968-record pool. Paid PFF/SIS charting or additional authorized tracking may fill gaps; no such data are claimed here. The CFBD API is another route but requires an API key; public releases allowed this work to proceed without another signup.

Retain the simpler operating baseline. The broader-data gain is a useful retrospective lead; the custom transformations have not yet earned a predictive scouting claim. Freeze the next metric definitions and identity rules before evaluating later uninspected prospects, and keep opportunity prediction distinct from demonstrated football ability.

## Primary source references

https://nflreadr.nflverse.com/reference/load_combine.html
https://nflreadr.nflverse.com/reference/load_draft_picks.html
https://nflreadr.nflverse.com/reference/load_snap_counts.html
https://nflreadr.nflverse.com/reference/load_players.html
https://nflreadr.nflverse.com/reference/load_pfr_advstats.html
https://github.com/sportsdataverse/cfbfastR-data/blob/main/README.md
https://js.sportsdataverse.org/docs/cfb/reference/loaders
https://collegefootballdata.com/key
