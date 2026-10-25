#!/usr/bin/env python3
"""Publish full retrospective strata and the surviving research hypothesis."""
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def main():
    folder=ROOT/'receipts/scouting_patterns';r=json.loads((folder/'stratification.json').read_text());p=r['tasks']['pressure_target'];lb=p['groups']['interaction=pos:correction_direction=LB:lower'];total=sum(len(v['groups']) for v in r['tasks'].values())
    release={'schema':'pp-scouting-patterns-release/1','groups_reported':total,'pressure_players':p['players'],'pressure_gain':p['groups']['all']['relative_gain'],
      'pressure_exposure_weighted_gain':p['exposure_weighted']['exposure_weighted_relative_gain'],'exploratory_LB_lower':lb,
      'largest_five_removed_pressure_gain':p['influence']['remove_largest_positive_gain_players']['5']['relative_gain'],
      'receiving_role_mean_control_gain':r['tasks']['receiving_efficiency']['role_mean_control']['summary']['relative_gain'],
      'retrospective_development':True,'independent_confirmation':False,'models_promoted':False,'recruitment_features_used':False,
      'monograph':'docs/SCOUTING_PATTERNS_MONOGRAPH.md','summary':'Retrospective stratification isolates pressure overprediction correction: 24 linebackers with lowered forecasts improve 55.19%, with 20 improving and positive gains in both observed classes. This exploratory subgroup is not independently confirmed. A simple matured-role mean outperforms richer models on receiving; no scouting model is promoted.'}
    (folder/'release.json').write_text(json.dumps(release,indent=2)+'\n')
    mpath=ROOT/'receipts/movement_language/release.json';m=json.loads(mpath.read_text());m['scouting_patterns']=release;m['summary']=release['summary'];mpath.write_text(json.dumps(m,indent=2)+'\n')
    pos=[]
    for name,g in p['groups'].items():
        if name.startswith(('pos=','correction_direction=','disagreement_band=','exposure_band=','interaction=pos:correction_direction=LB:')):
            pos.append(f"| {name} | {g['players']} | {100*g['relative_gain']:+.2f}% | {g['positive_classes']}/{g['classes']} | {100*g['player_win_fraction']:.1f}% |")
    controls=[]
    for task,v in r['tasks'].items():
        g=v['groups']['all'];c=v['role_mean_control']['summary'];controls.append(f"| {task} | {v['players']} | {g['baseline_mse']:.9f} | {g['candidate_mse']:.9f} | {c['candidate_mse']:.9f} | {100*c['relative_gain']:+.3f}% |")
    full_tables=[]
    for task,v in r['tasks'].items():
        full_tables.extend([f'### {task} — every reported group','', '| Group | Players | Gain | Positive classes | Outcome-conditioned | Simultaneous absolute-gain interval |','| --- | ---: | ---: | ---: | --- | --- |'])
        for name,g in v['groups'].items():
            interval=g['uncertainty']['simultaneous_player_95'] if g['uncertainty'] else 'unavailable'
            full_tables.append(f"| {name} | {g['players']} | {100*g['relative_gain']:+.3f}% | {g['positive_classes']}/{g['classes']} | {g['outcome_conditioned_not_a_routing_feature']} | {interval} |")
        full_tables.append('')
    text=r'''# Scouting pattern audit: correction direction, role, exposure and influence

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
PRESSURE_ROWS

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
CONTROL_ROWS

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

ALL_GROUPS
'''
    text=text.replace('PRESSURE_ROWS','\n'.join(pos)).replace('CONTROL_ROWS','\n'.join(controls)).replace('ALL_GROUPS','\n'.join(full_tables))
    (ROOT/'docs/SCOUTING_PATTERNS_MONOGRAPH.md').write_text(text.rstrip()+'\n');print(json.dumps({'groups':total,'release':release['schema']}))
if __name__=='__main__':main()
