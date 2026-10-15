# Historical prospect identity, opportunity records and delayed aggregation

October 15, 2026. Retrospective development release. This account supersedes no earlier experiment: all earlier monographs, protocols, negative comparisons and predictions remain intact.

## Result and exact scope

The work begins from main's later 3,762-prospect, 240-archive checkpoint, rather than rerunning the original 2,533-prospect expansion. All 24 original 2014–2025 recruiting and roster archives have been hash-checked against their source manifests. Older already acquired rosters provide exclusion evidence and pre-draft name/birth checks. The new output verifies 2,790 college identities under a strict, suffix-preserving name-plus-birth rule, rejects 969 unsupported bridges, retains three ambiguous bridges unresolved, and clears identity-dependent inherited measurements for all 972 unresolved prospects. Clearing a bridge is a statement about inadequate evidence under this stricter contract, not proof the old link identified the wrong person. The 953 changed or cleared inherited identifiers include cases with absent birth evidence; 73 fewer name/birth bridges than the previous 2,863 reflect the stricter normalization and ambiguity policy.

There are 4,956 supported college opportunity player-season records. These are counts with explicit college source seasons and observed usage denominators, not reconstructed routes or on-field snaps. Their source-vintage field explicitly says historical publication is unverified. The public research archive retains exact sources, identity and rejection ledgers, guarded inputs and prediction files. Athlete data in this release come from the public historical scouting sources; restricted movement tracking rows are excluded.

The fixed mathematical experiment reduces pressure-rate MSE by 7.111% against the conventional baseline on 90 defenders. Opportunity MSE improves 0.652% on 1,454 players; receiving MSE improves 2.600% on 185 WR/TE, while remaining 0.225% worse than raw college and 0.831% worse than historical college alone. None of these statements establishes independent confirmation. The pressure player's paired bootstrap includes zero. Its two cohorts give an extremely limited class bootstrap: both observed cohort gains are positive, but two support points cannot characterize future draft classes reliably. Every comparison, including losses against stronger receiving baselines, appears below.

## Namespaces and defensible evidence

The recruiting producer explicitly labels recruit_id as the 247 RDB key. It distinguishes team_id, the ESPN school join key, from team_id_247. Its signed-school field takes precedence over committed-school fallback; the fallback is an additional source uncertainty. The roster column cfbd_recruit_ids identifies another namespace. The inspected public college crosswalk schema covers ESPN, Fox and Yahoo, not an authoritative 247-to-CFBD recruitment mapping. The inspected 247 schema supplies names, hometown, schools and ratings but no birth date or per-rating publication timestamp. These inspected routes did not yield the required authoritative mapping; this does not prove no mapping exists anywhere.

There are zero equal numeric recruit/CFBD-name pairs in this frozen audit. That empirical absence is not an argument for permitting numeric joins in another vintage. Namespace typing forbids the operation regardless of whether integers happen to collide. The tests deliberately construct such a collision with different names and require rejection.

A prospect college bridge requires a valid equal calendar birth date and exact normalized full name in one of the three seasons strictly before the draft. Accent and punctuation normalization is allowed; generational suffixes remain significant. Both public Combine and NFL display spellings may supply the prospect name. No nickname expansion, edit-distance rule, outcome, draft slot, current height, current weight or NFL performance resolves ambiguity. Multiple candidate college IDs clear the inherited ID. Missing birth evidence also clears it. This deliberately sacrifices recall to avoid pretending unsupported matches are verified. Birth and names remain current-vintage identity evidence and are not proof of what an analyst saw on draft day.

Recruit-to-college candidates use exact suffix-preserving name and the same ESPN school in the recruiting class or following season. An observed earlier enrollment rejects the candidate; it may represent a transfer, junior-college rerecruitment or a source error, and we do not guess which. A unique candidate must be unique in the reciprocal direction too. Multiple recruiting records for one athlete remain unresolved. The original 47,807 recruiting records yield 35,355 corroborated context links, 11,218 no-context cases, 668 earlier-enrollment conflicts, 468 nonunique recruiting histories and 98 ambiguous contexts. These figures cover all recruits, not drafted prospects.

Only 1,125 drafted prospects have both the verified prospect-college bridge and one such recruiting context before their draft. Their status is **corroborated context only**, never authoritative identity. Exact name/school/year can still confuse namesakes and lacks an independent birth or explicit crosswalk key. No rating, rank or eventual success is used to choose among candidates. The ledgers preserve candidate sets, rejected earlier IDs, the recruitment school and evidence seasons so a later authoritative crosswalk can adjudicate rather than overwrite uncertainty.

## Historical availability and exclusion of revised fields

Three times must be kept separate: the season the observation describes, the date these frozen bytes were retrieved, and a verified date when the exact value was published. The original manifests record retrieval on October 15, 2026, after all historical draft classes in this experiment. They do not record pre-draft versions of recruiting ratings. A source code comment calling signing classes immutable does not certify when each downloaded rating was fixed. A current rating assigned to a historical class is not automatically an archived-as-of rating.

The availability predicate therefore requires an authoritative identity link, an explicit timezone-aware publication timestamp and publication at or before the cutoff. Missing dates fail closed. All 1,125 context-linked prospect records have pre_draft_feature_eligible=false; zero recruitment ratings enter a predictive model. This is the substantive remaining gap in a recruitment-adjusted pre-draft dataset, rather than a reason to fabricate feature coverage.

The 2014 Andre Dillard roster row labels him Senior although the recruiting table assigns him the 2014 class. It demonstrates that season-tagged biographical fields cannot automatically be treated as historical observations. Standing, current age, active/status fields and roster draft metadata are excluded. Recruiting context does not use position or class standing to break ties. Later roster seasons never rescue a prospect's pre-draft link. Older roster rows can reject already enrolled recruits, but cannot supply later rating values. Derived opportunity records retain historical usage counts from the established source contract; neither those counts nor the inherited baseline experiments constitute an original-publication-vintage database.

## Coverage and selection

College identity coverage is 74.16% of the 3,762-prospect population; contextual recruitment covers 29.90% overall and 44.41% of the original 2,533-player snap population. These are distinct from the earlier 2,357 production-feature links: identity evidence alone does not imply a production table exists. Early classes have little or no recruiting coverage because the acquired recruitment series starts in 2014. Transfers, missing birth dates, suffix variants and unobserved small-school history also lower coverage. Coverage by position and every class is retained in identity_audit.json, together with outcome availability and outcome means both overall and within class. Those outcome diagnostics are calculated after matching; they cannot influence identity.

The observed-outcome means differ: among players with snap labels the whole-population mean log opportunity is approximately 5.537, versus 5.827 in birth-verified college identities and 5.767 in recruitment-context cases. Cohort composition contributes to these differences, so the receipt includes matched within-class splits rather than treating the pooled contrast as a causal effect. Efficiency also conditions on a player reaching at least 30 NFL targets. Drafted Combine invitees are not all college players, all draft entrants or all undrafted free agents. Unmatched people and missing outcomes are not zero-performance examples.

For a loss bounded by B² and observed fraction q, without a missing-at-random assumption, population risk lies in [q R_observed, q R_observed + (1−q)B²]. A narrow confidence interval within the linked subset cannot remove this missing-population uncertainty. We do not fit inverse-probability weights and claim they repair unknown identity selection. The complete audit exposes the selection rather than optimizing apparent gains by dropping hard-to-match people.

| Draft class | Prospects | Verified college identity | Recruitment context only | As-of eligible recruitment |
| --- | ---: | ---: | ---: | ---: |
| 2007 | 185 | 150 | 0 | 0 |
| 2008 | 209 | 169 | 0 | 0 |
| 2009 | 202 | 175 | 0 | 0 |
| 2010 | 208 | 156 | 0 | 0 |
| 2011 | 216 | 151 | 0 | 0 |
| 2012 | 209 | 101 | 0 | 0 |
| 2013 | 220 | 77 | 0 | 0 |
| 2014 | 221 | 81 | 0 | 0 |
| 2015 | 211 | 113 | 0 | 0 |
| 2016 | 209 | 147 | 3 | 0 |
| 2017 | 218 | 166 | 45 | 0 |
| 2018 | 208 | 182 | 116 | 0 |
| 2019 | 213 | 179 | 149 | 0 |
| 2020 | 226 | 198 | 166 | 0 |
| 2021 | 193 | 177 | 157 | 0 |
| 2022 | 218 | 197 | 166 | 0 |
| 2023 | 189 | 177 | 151 | 0 |
| 2024 | 207 | 194 | 172 | 0 |

## Recruitment-adjusted development and denominators

The intended adjustment is a college-only residual: D_i = P_i − x(R_i)' beta, where R is recruitment information, P a declared college production or opportunity rate, and beta fits only earlier eligible college cohorts. The implemented ridge version centers and scales recruitment using its fitting subset and solves (X'X + diag(0,20)) beta = X'P. It does not use NFL responses. Ineligible recruitment produces a missing residual. Fewer than twenty eligible fitting records raises an explicit error. Execution is currently blocked because authoritative/as-of recruitment coverage is zero. Publishing hypothetical residuals as measured player development would be unsupported.

The preserved college opportunity ledger distinguishes receiving targets, rushes, touches, active usage games, same-game team targets and scrimmage tackle totals. Receiving yards divided by targets measures production per credited target, not route-running ability; team target share measures involvement, not target success. Activity games are not guaranteed games played. Tackles divided by team scrimmage tackle points is a share, not tackle efficiency per defensive opportunity. NFL pressure still uses all defensive snaps; true pass-rush snaps were not obtained. No route, coverage, college on-field snap or pass-rush denominator is invented. A future recruitment residual must keep these denominator distinctions.

## The mathematical prediction experiment

A fixed convex forecaster combines the four existing conventional, historical-college, raw-college and custom predictions. These predictions were generated with the established whole-player chronological nested model bank; the new experiment does not refit or select their models on outer labels. Draft-pick controls are excluded. This isolates aggregation from new identity features and preserves the old negative results. The pressure improvement is not evidence that recruitment links or newly designed physiological metrics succeeded.

Let b be the fixed target cap and clip target and each expert prediction to [0,b]. The caps, chosen before this experiment's comparisons, are log(10001) for opportunity, 30 receiving yards/target and 100 pressures/100 defensive snaps. No observed target or expert prediction actually requires clipping in these runs; original-label comparison receipts are retained. Define each expert's normalized class loss as the within-class mean of ((prediction−target)/b)². Class losses are in [0,1]. Separate forecasters for even and odd draft classes enforce the two-year label-maturity gap. At class Y, only outcomes in Y−2,Y−4,... update its weights.

With four experts, cumulative past losses S_j, eta=1, and equal initial weights, w_j = exp(−S_j)/sum_k exp(−S_k). Predict sum_j w_j prediction_j. No hyperparameter or subgroup is selected from these outer errors. Class weight and player weight are different estimands: the update uses equal classes; headline MSE pools players. We report both, never transfer the theorem from one to the other.

For each parity subsequence of T classes, convexity of squared loss gives L_aggregate,t ≤ sum_j w_j L_j,t. Let W_t be the sum of exponentiated negative expert cumulative losses. Hoeffding's bounded-variable inequality gives log(W_(t+1)/W_t) ≤ −sum_j w_j L_j,t + 1/8. Summing this inequality and lower-bounding W_(T+1) by the contribution of any fixed expert yields sum_t L_aggregate,t − min_j sum_t L_j,t ≤ log(4)+T/8. Adding the two parity inequalities gives the corresponding delayed comparison. This deterministic calculation holds for any sequence of clipped predictions and labels; it does not assume independent cohorts. The bound is loose on this small dataset and is not a certificate of a positive scouting edge, a significance test or a risk bound versus a new future player.

Tests check chronological invariance by changing future outcomes, ambiguity rejection, namespace collisions, source duplicates, exact birth conflicts, publication gating, convex prediction bounds and the finite-sequence regret inequality. Numerical receipts calculate actual class losses and the regret budget. This is a mathematical derivation plus numerical tests, not a Lean formalization.

For pressure only 2023 and 2024 have evaluated predictions, so neither parity forecaster has an earlier eligible class and all weights remain exactly one quarter. Its 7.111% point gain is ordinary ensemble diversity. Opportunity weights depart only slightly from equal averaging (maximum prediction difference about 0.003332); receiving differences are below 0.000019. The equal-average diagnostic is retained explicitly. We do not claim a new aggregation algorithm or credit the tiny adaptive updates with the whole improvement.

## All fixed comparisons

Positive gain means lower pooled player MSE. Intervals are paired, class-stratified fixed-prediction player bootstraps; class bootstraps and leave-one-class-out checks remain in aggregation.json. They exclude refitting and this adaptive research program. Existing outcome inspection prevents independent confirmation claims even when point gains are positive.

| Target | Players | Comparison | Candidate MSE | Baseline MSE | Gain | Player 95% absolute gain |
| --- | ---: | --- | ---: | ---: | ---: | --- |
| target | 1454 | aggregate_vs_combine | 3.823040336 | 3.848146467 | +0.652% | [-0.07702612405608085, 0.1257715373760811] |
| target | 1454 | aggregate_vs_historical | 3.823040336 | 3.921998862 | +2.523% | [0.043094521523531326, 0.15639012925891846] |
| target | 1454 | aggregate_vs_raw | 3.823040336 | 3.967778167 | +3.648% | [0.09378767004046625, 0.19602646177676838] |
| target | 1454 | aggregate_vs_custom | 3.823040336 | 3.964630891 | +3.571% | [0.08364939375149875, 0.19605740210357062] |
| target | 1454 | aggregate_vs_original_combine_original_target | 3.823040336 | 3.848146467 | +0.652% | [-0.07702612405608085, 0.1257715373760811] |
| receiving_efficiency | 185 | aggregate_vs_combine | 2.234386934 | 2.294024866 | +2.600% | [-0.01786648731575485, 0.14193132052454566] |
| receiving_efficiency | 185 | aggregate_vs_historical | 2.234386934 | 2.215968838 | -0.831% | [-0.06443249665448433, 0.028996456222701472] |
| receiving_efficiency | 185 | aggregate_vs_raw | 2.234386934 | 2.229361400 | -0.225% | [-0.0539865663586974, 0.04398092707164763] |
| receiving_efficiency | 185 | aggregate_vs_custom | 2.234386934 | 2.337630858 | +4.417% | [-0.004908453877777306, 0.21019644249472705] |
| receiving_efficiency | 185 | aggregate_vs_original_combine_original_target | 2.234386934 | 2.294024866 | +2.600% | [-0.01786648731575485, 0.14193132052454566] |
| pressure_target | 90 | aggregate_vs_combine | 0.938937551 | 1.010819021 | +7.111% | [-0.0639984723940297, 0.20013673454655417] |
| pressure_target | 90 | aggregate_vs_historical | 0.938937551 | 1.252232434 | +25.019% | [0.11566525863645923, 0.5532279275434099] |
| pressure_target | 90 | aggregate_vs_raw | 0.938937551 | 1.036970882 | +9.454% | [-0.014450484097776627, 0.2133159717777408] |
| pressure_target | 90 | aggregate_vs_custom | 0.938937551 | 1.004169738 | +6.496% | [-0.08478235495770088, 0.20261119975124253] |
| pressure_target | 90 | aggregate_vs_original_combine_original_target | 0.938937551 | 1.010819021 | +7.111% | [-0.0639984723940297, 0.20013673454655417] |

No model is promoted, no PerfectJet files are changed, no betting recommendation is generated, and no native executable upgrade is asserted. The live research feed carries aggregate evidence and limitations. Original movement experiments and their negative findings remain available. A future independent confirmation needs a genuinely untouched, fully matured cohort and eligible feature vintages; the partial 2026 season does not complete a two-season 2025 outcome.

## Reproduction and release contract

Install requirements-scouting.txt. Public cache bytes and acquisition manifests are included in the complete release archive. Keep derived player tables outside the source checkout. The identity builder accepts the preserved public prospect checkpoint from the previous complete scouting release; the release includes that exact input and all three frozen prediction tables to make reuse explicit. The complete package contains the generic mobile source bundle pinned to an explicit Git snapshot, every public archive, original-file hashes, new ledgers, derived opportunity records and all comparison receipts. This packaging preserves generic executable build inputs; it does not claim an APK was rebuilt.

```bash
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python scripts/build_scouting_identity.py --cache ../scouting-public-inputs --players ../identity-replay/prospects.pkl --out ../identity-derived --receipts receipts/scouting_identity
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python scripts/evaluate_scouting_identity.py --predictions ../identity-replay/target_predictions.pkl ../identity-replay/receiving_efficiency_predictions.pkl ../identity-replay/pressure_target_predictions.pkl --out ../identity-aggregate --receipt receipts/scouting_identity/aggregation.json
python -m unittest discover -s python/tests -p 'test_scouting*.py'
python scripts/report_scouting_identity.py
python scripts/export_explorer_live.py
python scripts/export_app_ecosystem.py
python scripts/export_app_web.py
```

The full identity ledgers have checksums in the aggregate identity receipt. A replay verifies source archive bytes before linking. Current-vintage claims and authoritative as-of claims remain separate in machine-readable fields. The essential unresolved inputs are an independently evidenced recruitment identity crosswalk and rating publication snapshots from before the draft, followed by the appropriate on-field exposure data. More sophisticated regression cannot supply those missing facts.

## Inspected primary source contracts

The exact inspected source bytes and retrieval hashes are retained under research/scouting_identity/upstream and receipts/scouting_identity/primary_sources.json. The producer and loader schemas establish their own field meanings; they do not certify the historical truth or publication time of every row.

https://github.com/sportsdataverse/sportsdataverse-py/blob/main/sportsdataverse/cfb/cfb_roster_talent.py

https://github.com/sportsdataverse/sportsdataverse-py/blob/main/tools/codegen/schemas/native/sports247/sports247_recruits.yaml

https://github.com/sportsdataverse/sportsdataverse-py/blob/main/tools/validation/schemas/cfb_rosters_crosswalk.json

https://github.com/sportsdataverse/cfbfastR-cfb-data/blob/main/python/cfb_data_build/recruiting.py
