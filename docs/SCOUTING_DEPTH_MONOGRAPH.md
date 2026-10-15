# Opportunity-aware scouting metrics and historical identity repair

October 15, 2026. Reproducible retrospective development experiment.

## Population and acquisition

The package contains **3,762 exactly linked drafted Combine prospects from 2007–2024**, 240 unique public archives (198,867,807 original bytes), and **2,357 prospects with verified college production**. The previous package contained 2,533 prospects and 1,204 verified college feature links. Earlier prospects supply training only for receiving efficiency, whose NFL statistics cover 2007–2025; their unknown snap and pressure labels remain missing. This does not create historical trajectories for these prospects or validate the original movement mathematics on thousands of players.

The source audit verifies hashes and sizes for every archive and exact schedule agreement for reciprocal team/opponent/week sets in all 19 NFL statistics seasons. Legacy NFL tables contain unilateral team/opponent anomalies; those context fields never enter features or player-season receiving totals. One older quarterback has separate ordinary/two-point stat rows with the same weekly key; every ambiguous player's receiving outcome is quarantined. The 2007 Combine maps two same-named people to one PFR ID; both ambiguous rows are rejected. Twenty requested historical files return 404, covering pre-2014 tackle usage and legacy credited-event files. Their absence is retained, not replaced by zero.

Acquired families include Combine, drafts, stable player IDs, snap counts, advanced defense, NFL weekly statistics and schedules; college credited events, game box scores, rosters, recruits, usage, tackle usage, passing, rushing, receiving and team summaries. Not all acquired columns enter the model. Recruiting namespaces remain unbridged; recruiting ratings and season summaries are retained as source material rather than silently entering predictors. Acquisition is not an assertion that every public or licensed scouting source has been obtained.

## Results

**No dependable custom-metric improvement is established.** Historical college production lowers receiving-efficiency MSE by 3.403% across 185 evaluated WR/TE, but both player and class uncertainty intervals include zero. The full custom bank increases error by 4.857% relative to the richer raw inputs; its optional gate chooses zero in every receiving class. On the 1,454-player opportunity target, optional custom improves the raw model by 0.375%, while that result remains 2.722% worse than the equally tuned conventional model. Pressure's optional correction also fails. The large 26.178% opportunity improvement from adding draft pick reflects existing NFL selection information, not a novel metric or pre-draft scouting advantage.

Every row below compares whole-player chronological predictions with models and penalties selected only on earlier, matured classes. Positive gain means lower MSE. The raw and custom families get exactly the same nonlinear model bank as the conventional baseline. No metric or position subgroup is selected by these outer errors.

| Target | Evaluated players | Raw vs conventional | Custom vs raw | Optional custom vs raw | Optional custom vs draft raw |
| --- | ---: | ---: | ---: | ---: | ---: |
| Two-season NFL opportunity | 1454 | -3.109% | +0.079% | +0.375% | +0.000% |
| WR/TE receiving yards per target | 185 | +2.819% | -4.857% | +0.000% | +0.000% |
| Pressures per 100 defensive snaps | 90 | -2.587% | +3.163% | -2.800% | +0.000% |

The last column compares the draft-control optional model with its own draft-control baseline. Draft pick is observed NFL selection information and answers a separate post-draft question; it is excluded from pre-draft models.

### Two-season NFL opportunity

Eligible: 2533; evaluated: 1454.

| Comparison | Candidate MSE | Baseline MSE | Relative gain | Player bootstrap 95% absolute gain | Class bootstrap 95% absolute gain |
| --- | ---: | ---: | ---: | --- | --- |
| historical_vs_combine | 3.92199886 | 3.84814647 | -1.919% | [-0.20991357956598286, 0.061691936124320626] | [-0.3387817628422675, 0.1700222386452671] |
| raw_vs_combine | 3.96777817 | 3.84814647 | -3.109% | [-0.26520027840735044, 0.022986853078116137] | [-0.39695792886367404, 0.12641147504730724] |
| raw_vs_historical | 3.96777817 | 3.92199886 | -1.167% | [-0.12453117888655466, 0.03274615895965525] | [-0.1449996486607805, 0.06472584116688307] |
| custom_vs_raw | 3.96463089 | 3.96777817 | +0.079% | [-0.04247487639256149, 0.05248561752521632] | [-0.03553909819807626, 0.049113664172999436] |
| optional_vs_raw | 3.95288709 | 3.96777817 | +0.375% | [-0.001731367785265841, 0.033201026541914765] | [0.0, 0.0435646521429416] |
| optional_vs_combine | 3.95288709 | 3.84814647 | -2.722% | [-0.24891086764212877, 0.03570310602697285] | [-0.3614971385478136, 0.12681986314666052] |
| draft_raw_vs_raw | 2.92910045 | 3.96777817 | +26.178% | [0.8230926606381921, 1.2615106659158306] | [0.7858565271832016, 1.2966755566427888] |
| draft_custom_vs_draft_raw | 2.93091553 | 2.92910045 | -0.062% | [-0.029745483627645723, 0.024945369368553332] | [-0.023830174938583033, 0.019761017851699144] |
| draft_optional_vs_draft_raw | 2.92910045 | 2.92910045 | +0.000% | [0.0, 0.0] | [0.0, 0.0] |

| Class | Players | Raw vs conventional gain | Optional custom vs raw gain |
| --- | ---: | ---: | ---: |
| 2018 | 208 | -7.460% | +0.000% |
| 2019 | 213 | -15.286% | +1.794% |
| 2020 | 226 | +12.446% | +0.000% |
| 2021 | 193 | -10.240% | +0.000% |
| 2022 | 218 | +4.323% | +0.000% |
| 2023 | 189 | -5.617% | +0.000% |
| 2024 | 207 | +1.057% | +0.000% |

### WR/TE receiving yards per target

Eligible: 422; evaluated: 185.

| Comparison | Candidate MSE | Baseline MSE | Relative gain | Player bootstrap 95% absolute gain | Class bootstrap 95% absolute gain |
| --- | ---: | ---: | ---: | --- | --- |
| historical_vs_combine | 2.21596884 | 2.29402487 | +3.403% | [-0.02039245210029791, 0.18031327514614554] | [-0.00962493397719826, 0.17784279151713409] |
| raw_vs_combine | 2.2293614 | 2.29402487 | +2.819% | [-0.03413313785451679, 0.168610183074594] | [-0.051580833020883295, 0.18021119622028955] |
| raw_vs_historical | 2.2293614 | 2.21596884 | -0.604% | [-0.032682420909620646, 0.006280374122051665] | [-0.047643388604269796, 0.0065169871910491645] |
| custom_vs_raw | 2.33763086 | 2.2293614 | -4.857% | [-0.2531363272116253, 0.0344726181568353] | [-0.2878875840396681, 0.03477729204048808] |
| optional_vs_raw | 2.2293614 | 2.2293614 | +0.000% | [0.0, 0.0] | [0.0, 0.0] |
| optional_vs_combine | 2.2293614 | 2.29402487 | +2.819% | [-0.03413313785451679, 0.168610183074594] | [-0.051580833020883295, 0.18021119622028955] |
| draft_raw_vs_raw | 2.24861585 | 2.2293614 | -0.864% | [-0.14498895600456477, 0.109755591789065] | [-0.05860773732430551, 0.004235763223294776] |
| draft_custom_vs_draft_raw | 2.33413354 | 2.24861585 | -3.803% | [-0.2094693529570727, 0.03505517684375067] | [-0.26271377840132115, 0.034500659127196666] |
| draft_optional_vs_draft_raw | 2.24861585 | 2.24861585 | +0.000% | [0.0, 0.0] | [0.0, 0.0] |

| Class | Players | Raw vs conventional gain | Optional custom vs raw gain |
| --- | ---: | ---: | ---: |
| 2018 | 28 | +7.398% | +0.000% |
| 2019 | 25 | +13.484% | +0.000% |
| 2020 | 32 | +0.682% | +0.000% |
| 2021 | 17 | -8.382% | +0.000% |
| 2022 | 28 | -2.396% | +0.000% |
| 2023 | 34 | +0.278% | +0.000% |
| 2024 | 21 | +4.096% | +0.000% |

### Pressures per 100 defensive snaps

Eligible: 339; evaluated: 90.

| Comparison | Candidate MSE | Baseline MSE | Relative gain | Player bootstrap 95% absolute gain | Class bootstrap 95% absolute gain |
| --- | ---: | ---: | ---: | --- | --- |
| historical_vs_combine | 1.25223243 | 1.01081902 | -23.883% | [-0.5567880723646846, 0.023513404478179505] | [-0.24294265735017093, -0.2398841685803135] |
| raw_vs_combine | 1.03697088 | 1.01081902 | -2.587% | [-0.25248057777376387, 0.17758165578771423] | [-0.14438288015143105, 0.09207915847421104] |
| raw_vs_historical | 1.03697088 | 1.25223243 | +17.190% | [-0.0648146075308359, 0.5250622217809295] | [0.09855977719873986, 0.3319633270545245] |
| custom_vs_raw | 1.00416974 | 1.03697088 | +3.163% | [-0.08712074189245946, 0.15143555706280964] | [-0.05806627357351912, 0.1236685613971891] |
| optional_vs_raw | 1.06600402 | 1.03697088 | -2.800% | [-0.12626385510153096, 0.05953189158683399] | [-0.05806627357351912, 0.0] |
| optional_vs_combine | 1.06600402 | 1.01081902 | -5.459% | [-0.29046360931739457, 0.16053418631553174] | [-0.2024491537249503, 0.09207915847421104] |
| draft_raw_vs_raw | 1.11892354 | 1.03697088 | -7.903% | [-0.3375407719716673, 0.13220925563729996] | [-0.2730146224735985, 0.10910929938727583] |
| draft_custom_vs_draft_raw | 1.0470073 | 1.11892354 | +6.427% | [-0.11414666600588204, 0.29612202253816194] | [-0.09244893548735406, 0.23628142281720343] |
| draft_optional_vs_draft_raw | 1.11892354 | 1.11892354 | +0.000% | [0.0, 0.0] | [0.0, 0.0] |

| Class | Players | Raw vs conventional gain | Optional custom vs raw gain |
| --- | ---: | ---: | ---: |
| 2023 | 45 | -14.950% | -5.230% |
| 2024 | 45 | +8.721% | +0.000% |

## What these targets establish

The opportunity target is log(1 + first-two-season regular-season offensive plus defensive snaps), measuring realized NFL use. Receiving efficiency is two-season receiving yards divided by targets, restricted in advance to Combine WR/TE with at least 30 NFL targets. It is a conditional performance estimate for players who reached that threshold; it does not score all receivers, eliminate quarterback/scheme effects, or prove draft decisions improve. There are 422 eligible receiving outcomes. Pressure uses the previous denominator of all defensive snaps, not true pass-rush opportunities; only 90 evaluated defenders remain. Its sample has not expanded merely because more public tables were acquired. Outcome scales and gains across tasks must not be pooled.

The initial 2013-start receiving population evaluated only 100 players. Its full results remain in `evaluation_receiving_efficiency.json`; the expanded 2007-start run is in `evaluation_receiving_extended.json`. The coverage extension was fixed before outer error values were inspected; only the initial sample count and tuning configurations had been reviewed. The outcome, 30-target threshold, feature bank, model bank and outer years stayed fixed. Earlier source-driven identity repair and the stopped unbridged run are recorded in the protocol and `initial_unbridged/`. These runs belong to the same retrospective development program, not independent confirmations.

## Exact identity and chronology

The original NFL ESPN ID crosswalk fails for many older college IDs. The repair matches exact normalized Combine or NFL display name **and exact immutable birth date** against only roster seasons in the three years before the draft. Punctuation, accents and generational suffixes normalize; nicknames and fuzzy spelling do not. A unique college athlete ID is required. There are 1516 additional cross-namespace bridges, 1347 same-namespace birth verifications and 3 ambiguous bridges left unresolved. Every attached feature still requires a source-name check at its explicit one-, two- or three-year lag.

Current NFL body size, current position, status, career totals and roster draft metadata are excluded. Birth date is used for identity and age at a fixed April 25 draft date. This is a current-vintage historical source package; upstream birth and name corrections may postdate a game's original publication. It is not an archived-as-of prospect database. Drafted invitees with exact PFR/year links define the population; unmatched or undrafted prospects are not fabricated NFL failures.

For outer class Y, training classes are at most Y−2, so both training outcome seasons are finished by the next draft. The same gap applies to inner chronological folds. At least 100 training players and 20 validation players are required, using at most the three most recent eligible inner classes. Player IDs cannot overlap. Evaluation labels never fit scaling, clipping, support selection, regressions or hyperparameters. The 2025 draft class is neither used as untouched confirmation nor assigned a complete two-year outcome from a partial 2026 season.

## Custom metric mathematics

Raw usage counts retain rushes, targets including incompletions, receptions, yards, first downs, touchdowns, red-zone and third-down activity, same-game team totals and active games. A usage game means a game with activity in that section, not a guaranteed game played or full route exposure. Transfers are summed only across distinct source team keys. Duplicate team/athlete/season keys fail.

For observed successes s in n opportunities and college source-season pooled rate p, define

    q = (s + 20 p) / (n + 20),
    Var(q) = (s + 20 p)(n − s + 20(1 − p)) / [(n + 20)²(n + 21)].

The fixed strength 20 is not tuned with NFL responses. Catch, first-down-or-touchdown conversion, explosive and third-down conversion metrics use their appropriate observed denominators. Zero opportunities leave the measurement missing. This beta variance describes an operational binomial smoothing model; it is not calibrated movement-phase uncertainty or a physiological confidence bound. Explosive flags come from the upstream EPA-explosive definition; they are not the older fixed-yard credited-event threshold.

Other metrics are receiving yards/targets; total yards/(rushes+targets); targets/same-game team targets; touches/same-game team touches; player/team first downs; opportunities/active games; third-down opportunities/all opportunities; and scrimmage tackle points/team scrimmage tackle points. Tackle share excludes special-teams and post-turnover activity in its denominator. It is not a tackle success rate per defensive snap or pressure rate per rush. No route, pass-rush or on-field denominator is invented. Historical box means, college trajectory differences and the earlier physical proxies are also retained in the declared custom family. Conventional measurements and the earlier movement residual experiment are unchanged.

## Models and baseline preservation

Every feature family receives ridge penalties 10, 100, 1,000 and 10,000; shared-plus-position-interaction ridge at 100 and 1,000; histogram gradient boosting with depth 2 or 3, L2 1 or 10, 150 iterations, learning rate .05 and minimum leaf 30; and 200 extra trees with minimum leaf 10 and max-feature fraction .7. Seeds are fixed at 84593. Boosting has no evaluation-set early stopping. Coarse roles group defensive backs, offensive line, defensive line and linebackers; other positions remain explicit. No role is selected for promotion using outer errors.

Numeric imputation/scaling, the previous max(20,10% of training) finite-support guard and first/99th-percentile clipping fit only training data. Missingness and training position indicators are explicit. The role ridge appends numeric/missing/position design interactions with each observed training role. Squared-error predictions are floored at zero for these nonnegative targets. Each family's minimum pooled inner player MSE selects its model independently.

The optional bank compares selected raw and selected custom inner loss vectors. It accepts the custom endpoint only if their paired mean gain exceeds one player standard error; otherwise correction is exactly zero. With b the raw prediction and c the custom prediction, the deployed mathematical form is b + λ(c−b), λ in {0,1}. This is a selection heuristic rather than a guarantee of improved risk: tuning variability and class dependence can still make the accepted correction fail. It preserves the appropriate raw baseline, which itself can lose to the conventional model. The earlier cross-fitted residual-ridge movement experiment remains separately documented and unsuccessful; these source metrics do not retrospectively convert it into a positive result.

## Uncertainty, failures and deployment

Receipts retain every outer configuration, class error, position diagnostic and leave-one-class-out pooled gain. Intervals use 4,000 within-class paired player bootstrap draws and 10,000 class-bootstrap draws of fixed-prediction loss differences. The class bootstrap gives equal class weight; the player interval follows pooled player weight. They are different estimands. With few classes, neither interval captures refitting uncertainty, the adaptive research program, historical source revisions or prospective shift. Position rows are diagnostics and do not authorize subgroup selection. Individual paired standard errors used for fallback are heuristics, not formal multi-model significance tests.

All comparison receipts, including degradation and exact zero fallbacks, are published. More source rows or a point improvement cannot by themselves establish dependable scouting value or prove that new movement mathematics adds information. No new scouting recommendation model or APK is deployed. PerfectJet main was checked at `01fe017c41d7bdc7352be84fa6d4654a9d0c29c7`; its files and concurrent work were not modified. The original authorized research checkpoint was reused; no Kaggle redownload or paid charting access is claimed.

## Reproduction

Install `requirements-scouting.txt` and set `OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1` for deterministic CPU replay. Keep all player tables and predictions outside the checkout. From the source root:

```bash
python scripts/acquire_scouting_sources.py --cache ../scouting_inputs
python scripts/acquire_scouting_depth.py --cache ../scouting_inputs
python scripts/prepare_scouting_expansion.py --cache ../scouting_inputs --out ../scouting_derived --aggregate ../original_population.json
python scripts/prepare_scouting_depth.py --cache ../scouting_inputs --previous ../scouting_derived --out ../scouting_depth --aggregate ../depth_population.json
python scripts/run_scouting_depth.py --players ../scouting_depth/prospects.pkl --out ../scouting_predictions --aggregate ../depth_evaluation.json
python scripts/audit_scouting_depth.py --cache ../scouting_inputs --original ../scouting_derived/prospects.pkl --extended ../scouting_depth/prospects.pkl --out ../depth_audit.json
python -m unittest discover -s python/tests -p 'test_scouting*.py'
```

The complete source ZIP includes the exact acquired public files and their URL/hash manifests, so reproduction can use frozen bytes instead of fetching revised sources. Original 2013-population sensitivity receipts reference `research/scouting_depth/protocol_initial_2013.json` and the archived initial core. The final expanded receiving receipt references the current protocol. Selected-model prediction replay validates compatibility with the final kernel on every evaluated player; it does not substitute for a fresh independent validation sample. Restricted BDB rows stay outside public GitHub and source/data archives. A separate continuation preserves derived inputs and predictions. The installed native executable, refreshed aggregate feed and pinned source snapshot remain distinct identities.

## Primary sources

https://github.com/nflverse/nflverse-data/releases
https://github.com/nflverse/nfldata/blob/master/data/games.csv
https://github.com/sportsdataverse/cfbfastR-cfb-data/blob/main/DATASETS.md
https://py.sportsdataverse.org/docs/0.1.5/cfb/reference/loaders/usage
https://github.com/sportsdataverse/cfbfastR-cfb-data/blob/main/python/cfb_data_build/recruiting.py
