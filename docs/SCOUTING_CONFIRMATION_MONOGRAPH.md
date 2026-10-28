# Frozen linebacker-pressure validation design

28 October 2026. Specification freeze, not a frozen 2025 prediction release.

## Hypothesis and decision

A prospect-observable rule applies the existing delayed ensemble only to source-position LB prospects whose ensemble forecast is below the conventional Combine forecast and whose identity and historical feature availability are verified. Other defensive prospects keep the Combine prediction. This evaluates a practical abstaining policy rather than retrospectively choosing successful corrections. No new benefit classifier is fitted on the 24 discovered cases. The comparison is calibration of pressures per100 defensive snaps, not intrinsic pass-rush ability or pressures per pass-rush opportunity.

The machine-readable protocol fixes the existing expert bank, chronological tuning, delayed ensemble, strength20 role-mean control, exact routing, four comparisons, two populations, uncertainty and success gates. Its implementation is in `python/perfectpower/scouting_confirmation.py`. CLI `scripts/evaluate_scouting_confirmation.py` separates outcome-free freeze from gated scoring. Neither command downloads outcomes. A canonical JSON digest binds each prediction packet; a public committed manifest must precede evaluation. A digest detects changes relative to a committed digest; it is not authentication by itself.

## Historical verification and limits

The preserved 202932518-byte package SHA256 is `008f25399bde6084907dc090506e4eca709939a4c719dc6e967373339626edd5`. The replay verifies the pressure-strata member against its published SHA256 before loading it and accepts only classes2023/2024. The original LB/lower mean absolute gains reproduce as0.27848041198734674 and0.3408788379290707. Historical source positions, original forecasts and all negative findings remain untouched. The strict new availability gate selects zero historical prospects: missing publication timestamps cannot honestly be marked verified. This is a replay of scoring/routing on preserved forecasts, not a refit or proof of historical as-of validity. Team labels were not preserved in this table; cluster intervals are correctly unavailable in its replay.

Synthetic tests exercise outcome-blindness, fallback, ambiguous identity, absent availability, upward correction, duplicates, missing outcome identities, nonfinite predictions, frozen-packet tampering, maturity locks, deterministic bootstrap and undefined zero exposure. Existing pattern/identity tests remain required. The role mean is trained using the existing `matured_role_mean` implementation; labels afterY−2 cannot enter training, as covered by retained tests. Frozen model fitting must still be replayed once dated feature inputs are obtained.

## Exact remaining freeze requirements

Before any 2025 confirmation outcomes are opened, preserve the complete Combine defensive roster (including undrafted players), unique crosswalk evidence, every predictor's dated source evidence, the explicit training-row manifest with labels through2023, exact dependency versions, fitted expert artifacts, inner tuning receipts and delayed weights. Then produce predictions and hash those artifacts and the prediction packet in GitHub. The current input contract requires these hashes, but does not independently certify assertions supplied by a caller: a reviewer must verify the evidence files. No 2025 prediction packet or fitted artifacts are claimed to exist in this release. The recovered package contains historical outcomes; this work opened only its historical pressure table and did not inspect future confirmation outcomes.

Historical training features have only season-based filters in the legacy pipeline; identity and publication availability guards must be applied before refitting, rather than describing the original predictions as guarded. Every used feature must have evidence dated by the class's April23 cutoff. Incomplete college evidence blocks the enriched-model freeze; it must not be turned into favorable outcome-based attrition. Preserve the full defensive roster and conventional fallback. Never hash a current snapshot and call that evidence of old availability.

2025 is already partly observed in the world. This design is pre-complete-outcome, not pre-draft. Record prior access to partial results. If contamination cannot be excluded, 2025 is secondary validation and an untouched later cohort is needed. The March1 2027 date is a conservative earliest scoring gate, not certification that the official outcome sources are complete.

## Evaluation and interpretation

The scored target is100 times summed regular-season pressures divided by summed defensive snaps in2025 and2026. Reconcile every frozen identity, including absent NFL participation, before scoring. Zero exposure stays undefined and its count is reported for each population through frozen_n minus n. The rate estimand is conditional on positive exposure; it cannot support an all-prospect ability claim. The broader policy is evaluated on the identical positive-exposure population. Integer count reconstruction and finite inputs are checked. Complete outcome-source hashes and reconciliation evidence must accompany the first primary receipt.

Success requires at least20 selected evaluable LBs, simultaneous positive lower loss-gain bounds against both Combine and the properly trained role mean, and a nonnegative full-defense lower bound against Combine. The last gate has zero tolerated population harm; it is deliberately stringent. With fewer than8 observed first-team clusters, uncertainty is unavailable and confirmation cannot succeed. Use earliest regular-season team (ties lexical) for cluster assignment after the outcome seal opens; no team or exposure enters routing. Bootstrap intervals condition on this cohort and fixed forecasts. They do not account for all cross-team dependence or establish transport across years. Candidate and ensemble coincide on selected LBs, and Combine and no-correction coincide everywhere; retain those redundant controls transparently.

All eight two-sided intervals use Bonferroni alpha.05/8 and10000 team bootstrap draws, seed42871. Report point losses, sample sizes, undefined rates, coverage and every comparison even on failure. No thresholds, cohort extensions or alternative primary endpoints may be selected after outcomes. Revisions require a new protocol/version and an untouched test. Automatic scoring never promotes a model.

The original55.19% reduction remains an exploratory result. The pooled pressure advantage's top-five deletion reversal, adverse direction/position cells and receiving role-mean superiority remain in `SCOUTING_PATTERNS_MONOGRAPH.md` and its receipts. Weekly automation checks freeze integrity and readiness, and is explicitly prohibited from inspecting partial confirmation outcomes or retuning the rule.

## Reproduction

Run `PYTHONPATH=python python3 -m pytest -q python/tests/test_scouting_confirmation.py python/tests/test_scouting_patterns.py python/tests/test_scouting_identity.py`.

Run `python3 scripts/replay_scouting_confirmation.py PATH_TO_PRESERVED_pressure_target_strata.pkl receipts/scouting_confirmation/historical.json` to reproduce the historical receipt. The complete original package remains linked from `receipts/scouting_patterns/publication.json`. No restricted original movement data or player-level influence data is added to public GitHub.

Live Explorer feed generation is separate from deployment/consumer verification. This change adds a status object only; no native executable upgrade or live Site synchronization is claimed.
