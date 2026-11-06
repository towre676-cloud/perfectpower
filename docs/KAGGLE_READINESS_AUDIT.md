# PerfectPower PR #16: independent Kaggle readiness audit

Audit prepared 5 November 2026 (America/New_York). Inspected PR head: `b7c57c0d35ae8a1b31592b7bff5e2084478d7e3d`, branch `codex/weekly-submission-audit-20261105`. GitHub reported an open, unmerged draft. Corrections below exist only in the local proposal. No GitHub write, Kaggle upload/publication, competition submission, rules acceptance, merge or Site change was performed.

**Decision: scientifically defensible negative-result package, but not yet a completed Kaggle entry.** The existing entry should be corrected and replayed. A new entry or favorable-result search is unnecessary.

## Findings and prepared corrections

| Priority | Finding in inspected package | Local proposed correction / remaining gate |
| --- | --- | --- |
| High | Raw mode writes the recomputed paired audit to `EVIDENCE['reliability_pair_review.json','loss_geometry.json','rules_review.json']`. This is one tuple key. The expected string key retains historical evidence, so raw-mode figures/audit silently mix old and new results. | Assign the fresh result to the single intended string key. Add an orchestration test that demonstrates replacement. |
| High | Figure 1 hardcodes the paired difference and its interval. Correcting the key alone cannot update its caption after a raw recomputation. | Read the paired difference and interval from the evidence for the active mode. Regenerate its PNG/SVG. |
| Medium | The original wrapper compares whichever model keys are returned, omits explicit baseline comparisons, and does not reject nonfinite losses. Missing keys or NaN could undermine the completion check. | Require all 12 pressure and 30 get-off candidate comparisons, nine baseline comparisons, finite losses and the existing 1e-12 tolerance. Regression tests cover missing keys, a changed baseline and NaN. |
| Medium | A raw run with reduced resampling counts can be described as executed without a machine-readable distinction from full reproduction. | Record `full_reproduction` separately: true only after the raw checks succeed with 20 pressure refits per temporal comparison and 16 mislinking runs. Reduced runs remain diagnostics. |
| Medium | Default temporary placement honors environment settings. A hosted configuration could direct temporary extracted records into the working output area. | Explicitly create the private raw directory under `/tmp` and retain the public-output ancestry guard. Never export that directory. |
| Medium | The wrapper's public audit records only Python, NumPy and Matplotlib versions. Hosted numeric-library differences could matter to exact replay. | Record SciPy, pandas, scikit-learn and IPython as well. Reconcile the actual hosted image with the supplied requirements; no dependency compatibility on Kaggle is claimed. |
| Low | The review still says nothing was pushed, although it now appears in PR #16. The writeup links an unpinned main directory. Attribution/license separation is insufficiently visible in the notebook. | Clarify the historical review status, pin the source link to the inspected commit, and add data attribution plus the existing code/prose license distinction. |
| Blocking entry completion | No attached public Kaggle notebook or submitted Writeup is established by the repository records. | Hosted execution, author-approved publication, real URL attachment, embedded visual review and an explicit final submission action remain. |

The historical notebook, extraction routines, estimators, protocols and original empirical receipts are unchanged. No favorable empirical result was substituted. The patch changes the wrapper, presentation provenance, documentation and tests.

## Independent verification completed

The original selection of nine model/reproducibility test files passed **54 tests** in this session. With three added wrapper tests, **57 tests pass**. The three new tests exercise default/reduced run status, fresh paired-result assignment, private-directory placement and corrupted replay rejection. Their expensive experiment boundary is stubbed; they do not reconstruct official data or validate fitted NFL results.

The original and proposed submission notebooks both pass nbformat validation and execute all **four code cells** sequentially in fresh Python processes, producing exactly **four displayed PNGs**. The proposed raw path refuses missing official inputs before modeling. Its embedded cohort preparation, feature extraction, compact/get-off model and repeatability modules import successfully.

A genuine local Jupyter-kernel attempt was also made after installing the missing notebook client/kernel packages. Startup failed with `Operation not permitted` in the socket resolver and `Kernel died before replying to kernel_info`. This is an execution-environment limitation, not evidence of a failed mathematical identity or a successful hosted run. No Kaggle kernel was run.

An independent arithmetic script, without importing the submission analyzer, recomputed all **42 candidate loss comparisons**, checked all reported relative gains to 1e-12, recalculated the decomposition and ceilings, and verified the **14 get-off fallback decisions**. The exact-rational loss-geometry certificate was regenerated and agreed with the stored certificate. Its mathematical proofs are sound for fixed records and the implemented constant-per-player correction, with the scope qualifications already stated in the companion document.

There are **38 successful evidence-integrity checks**: eight embedded receipt payloads/pins, the historical notebook hash, standalone compact release hash, historical get-off result hash, four embedded compute cells, and 23 embedded public modules. The historical raw pressure-output hash is not the standalone compact receipt hash: they represent separate runs with runtime metadata. The raw-output file itself is unavailable here, so its complete bytes cannot be independently authenticated. The historical replay script explicitly compares its 12 losses with the standalone receipt before recording success. This is recorded provenance, not a fresh reconstruction.

All four existing figures were visually inspected. Their point estimates, interval scaling, units, fallback markers and decomposition agree with the receipts. They display losses and uncertainty, including the very wide 2024 get-off interval. The proposed Figure 1 uses the active paired result rather than literal historical numbers. Original word count is 1,508 by whitespace; proposed writeup is **1,546 words**, including headings, captions and links, with **four figures and no tables**. Recount the final rendered Writeup after any editorial additions.

## Claim-to-evidence ledger

| Claim or claim group | Evidence and independent assessment |
| --- | --- |
| 74 DL players, 23/22/29 by class, 361 source attempts, 14,665 NFL records | `compact.json`, `getoff.json`, historical official-rebuild receipt, runner cohort guards. Consistent across records; actual joins and exclusions require official-input replay. |
| Conditional observed pressure-event fraction, rather than all-opportunity pressure probability | Historical `front_transfer.prepare` defines pressure from nonmissing `time_to_pressure` after its participation/get-off/exposure filters. Writeup accurately limits the denominator. |
| Speed gain rho 0.519 and recovery rho 0.259; 39 repeated players each; marginal intervals 0.158–0.801 and −0.080–0.559 | `repeatability.json`; inspected source uses alternating event-ID halves, player medians and source-only bootstrap. Values supported by receipt; saved attempt file is not available in this checkout, so the empirical correlations and bootstrap were not freshly rerun. |
| Paired difference 0.260, interval −0.105–0.650, 39 players, 84 complete shared attempts, 4,000 draws | `reliability_pair_review.json`; arithmetic difference agrees and interval crosses zero. Inspected paired-audit function jointly resamples common players and consumes no NFL response. Reproducing its empirical interval needs the unavailable attempt table. Remains post hoc and exploratory. |
| Hoop rho 1 on four players; four-bag no repeatability estimate | Marginal receipt and implementation agree. Neither supports a reliability promotion. |
| Selected compact development MSE 0.000959202 versus 0.000953206: 0.63% worse | Independently recomputed from `compact.json`. Preserved. |
| 2023→2024 selected compact exact fallback, MSE 0.001525834 | Receipt agrees; fixed correction worsens about 3.28%. Preserved. |
| Exploratory 2025 compact 0.000714146 to 0.000773802: 8.35% worse | Receipt agrees; selected and fixed predictions have the same aggregate loss. No new confirmation. |
| Conventional development forecast improves 16.0% relative to the global mean | Recomputed **16.039876%**, using the mean forecast as denominator. Does not establish movement value. |
| Earlier broader selected residual strategy worsens development 2.878% | `receipts/movement_language/residual.json` supports the historical value. Separate specification on reused players, not a replication or winning positive result. |
| Twenty complete training-player refits per temporal comparison and 16 mislinking runs | Compact receipt records these counts. All 16 selected mislinking gains are zero; this does not itself prove the correction was disabled internally on every run. Retain the narrower claim that the selected evaluation equals fallback, not useful learning or a p-value. |
| Half-second launch, 143 attempts covering 74 players; operational onset | `getoff_extraction.json`, extraction source and source tests support the recorded counts and exact 0.5-second interpolation. Counts need raw replay. The measure is not cue reaction time. |
| Fixed get-off gains +0.21%, −8.86%, −0.41%; all conditional intervals cross zero; all 14 selected fits fallback | Independently checked against all three primary-loss stages and the stored selection audits. Positive means error reduction. Preserved. |
| Within-player shares 92.1%, 95.4%, 96.1% | Independently subtract primary player-mean loss from equal-player auxiliary play loss. Context/fixed/selected variants preserve the same centered term to 1e-12. |
| Oracle maximum play-loss reductions 7.86%, 4.56%, 3.94%; 2024 −8.86% primary vs −0.404% auxiliary | Recomputed P/A and the two relative denominators. These are finite-record ceilings and two objectives, not achieved performance or irreducible noise. |
| Baseline feature subsets, training boundaries, caps and fallback | Inspected extraction/model source and passing boundary tests support the described implementation. Aggregate receipts alone cannot establish real-data leakage absence under every join; fresh raw replay and record-level review remain necessary. |
| No incremental forecasting value established; 2025 exploratory; conditional get-off task | Appropriate conclusion. Repeated players, adaptive specification history, conditional fixed-prediction intervals, sparse repeats and participation selection prevent stronger validation claims. |

The phrase “this revision exactly replays” in the competition narrative refers to the original preparation, whose execution is recorded in the retained review. This audit independently verifies the recorded result's consistency; it does not newly possess or replay that private attempt table.

## Rules, data and licensing assessment

The official Kaggle overview was retrieved, and the live Rules tab was independently read through Definitions in the rendered browser. Deadline: **6 January 2027, 23:59 UTC**. The entry needs readable Markdown, embedded visuals, an attached public Kaggle notebook and an explicit Combine-tracking-to-NFL analysis. The limit is at most 2,000 words and **fewer than ten** combined tables/figures. A receipt-only run is transparent supporting evidence; it does not itself demonstrate current use of mounted tracking data.

The rules allow one hackathon submission per team, with at most five people. Data carry CC BY-NC 4.0 and additional access/security restrictions. Public competition code must also be shared through competition-associated Kaggle channels under an appropriate open-source license. Winning submissions carry further licensing and reproduction obligations. Eligibility, team roster, track, rights and rules acceptance require author confirmation; this audit does not certify them.

The proposed notebook contains no stored cell outputs, official CSVs, private extracted tables or per-player forecasts. Its embedded literals contain source code and aggregate evidence; an identifier/prediction-key inspection found no player-row payload in those receipts. Raw records, model predictions and private logs are directed outside public working outputs. The audit bundle excludes private inputs and unrelated PR material. This is an inspected-content finding, not a blanket assurance about future Kaggle outputs or every repository file.

Existing Apache-2.0 code and CC BY 4.0 prose licenses remain separate from restricted inputs. Author review of submission-specific winning-solution licensing and third-party rights is still needed. Public GitHub code does not replace the required competition-associated Kaggle sharing/attachment.

## Exact remaining path to a valid entry

1. Review this correction patch. If approved, update PR #16 without merging it. No repository release or live application synchronization is part of this local audit proposal.
2. In an authorized Kaggle workspace, attach the official competition dataset. Verify all nine hashes from the embedded manifest. A changed dataset version must be reconciled explicitly; do not silently skip a pin or present changed data as an exact reproduction.
3. Reconcile/install the declared numerical dependencies in the hosted environment. Record actual versions, runtime, memory and any numerical deviations. Set `BDB_SUBMISSION_MODE=raw` before Run All and use 20 refits per temporal evaluation and 16 mislinking runs. In Kaggle, this can be configured by adding `os.environ['BDB_SUBMISSION_MODE']='raw'` immediately after importing `os` in the first setup cell.
4. Run every cell from a clean hosted session. Require 12 pressure, 30 get-off and nine baseline comparisons, successful paired-audit replacement and four displayed figures. Save the aggregate completion receipt and verify its full-reproduction flag. If exact replay fails, investigate rather than relaxing tolerance to manufacture a pass.
5. Inspect notebook outputs and downloadable files for restricted rows, identifiers, player predictions and private logs. Keep official data attached through the competition mechanism, not a copied public dataset. Inspect the rendered captions and final word/figure totals.
6. Confirm actual author/team/track eligibility, attribution and licensing. Obtain explicit approval for publication. Publish the reviewed competition-associated Kaggle notebook, record its real public URL/version, replace the writeup's placeholder/local attachment and embed the four images so they render on Kaggle.
7. Obtain explicit approval for the final entry. Submit the single final Writeup with its public notebook attachment before the deadline and retain the visible submission confirmation. Notebook publication alone is not submission.

Official sources: [submission requirements](https://www.kaggle.com/competitions/nfl-big-data-bowl-2027/overview/submission-requirements), [timeline](https://www.kaggle.com/competitions/nfl-big-data-bowl-2027/overview/timeline), [Rules](https://www.kaggle.com/competitions/nfl-big-data-bowl-2027/rules), [PR #16](https://github.com/towre676-cloud/perfectpower/pull/16).
