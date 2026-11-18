# Proposed Big Data Bowl 2027 materials: author review

Prepared 4 November 2026 against PerfectPower main commit `408744741bd3ef1a56987e1888f90c85a16bf149`. This paragraph describes the original local preparation on 4 November. The package subsequently reached draft PR #16 on 5 November; it remains unpublished and unsubmitted on Kaggle. See KAGGLE_READINESS_AUDIT.md for the independent audit and proposed local corrections.

## Competition requirements and scoring

The official [submission requirements and evaluation](https://www.kaggle.com/competitions/nfl-big-data-bowl-2027/overview/submission-requirements) specify at most 2,000 words, fewer than 10 tables or figures, readable markdown with embedded visuals, an attached public Kaggle Notebook and explicit use of Combine tracking linked to NFL performance. Judging weights are football 30%, data science 30%, writeup 20% and visualization 20%. The official [timeline](https://www.kaggle.com/competitions/nfl-big-data-bowl-2027/overview/timeline) gives 6 January 2027 at 23:59 UTC.

The proposed writeup has 1,508 whitespace-delimited words (1,571 under a more conservative lexical count), including headings, captions and links; it embeds four figures and no tables. Notebook narrative is also under 2,000 words. Supporting mathematical and review documents are separate from the entry body. Do not paste these supporting documents into the competition writeup.

The full [Rules tab](https://www.kaggle.com/competitions/nfl-big-data-bowl-2027/rules) was subsequently inspected directly in the rendered browser on 4 November 2026. It sets one hackathon submission per team, at most five team members, noncommercial/protected data use, competition-associated Kaggle public-code sharing and open-source winning-solution obligations. The detailed section mapping and license distinctions are recorded in `COMBINE_RULES_REVIEW.md`. Viewing the rules did not accept them or submit an entry.

| Judging component | Concrete revision | Remaining limitation |
| --- | --- | --- |
| Football, 30% | Define observed pressure denominator; distinguish longer-window speed gain from half-second launch; separate prospect calibration from snap timing | No demonstrated incremental forecasting edge; no opponent/assignment identification |
| Data science, 30% | Preserve conventional/mean controls and failures; joint paired reliability audit; exact loss decomposition; player-level separation | All cohorts previously examined; no independent confirmation |
| Writeup, 20% | One two-stage argument, explicit decisions, short definitions and transparent uncertainty | Required public Kaggle attachment awaits approval and creation |
| Visualization, 20% | Four color-accessible figures with repeat counts, wide intervals, explicit fallback and common loss units | Original trajectory/film examples require restricted raw observations |

## Evidence verified in this revision

- The historical original notebook bytes match the full official-rebuild receipt's SHA-256. Its 12 pressure and 30 get-off comparisons remain historical results, not new executions.
- Relative gains were recalculated from every saved MSE in the compact and get-off aggregate comparisons, including controls. Get-off selection was checked against all 14 saved audits: every fit retained fallback.
- Saved attempt bytes match historical SHA-256 `42be61c60d25ffbf5684417889a35525a875d9e668b64ed0589eaa164f37b20a`. Re-running the existing marginal repeatability audit exactly reproduced its entire receipt.
- A new source-only paired diagnostic used the same 39 players and 84 shared attempts. Correlation difference 0.2603; 4,000-draw descriptive interval [−0.1054, 0.6504]. It was selected after marginal results were known and remains exploratory.
- Exact loss decomposition was verified against all three get-off evaluations. Within-player residual shares are 92.1%, 95.4% and 96.1%; these are model-specific components, not irreducible error estimates.
- The existing eight-file model test suite passed 48 tests. Six new tests passed for the mathematical identity, corrupted aggregate detection and paired-audit independence from NFL responses. The historical report's 55-test count is not substituted for this session's cumulative 54 tests.
- The revised notebook validates as nbformat 4. All four code cells execute in a fresh Python process and display exactly four aggregate figures. A Jupyter TCP kernel could not start in this environment; no hosted Kaggle execution is claimed.

## Exactly what remains data-dependent

| Check | Inputs required | Status |
| --- | --- | --- |
| Fresh nine-file official reconstruction, timing/coordinate extraction, full pressure/get-off refits and wrapper raw-mode replay | All nine original SHA-pinned official CSVs | Not executed; raw CSVs absent |
| Paired speed/recovery rank comparison and original split-attempt replay | Saved source attempt features | Executed on hash-matched continuation |
| Alternate random/chronological splits of the existing extracted features | Saved attempt features | Possible, not run; additional exploratory sensitivity, not independent validation |
| Onset/smoothing robustness, raw trajectory QC, standardized effort/instruction comparisons | Original Combine tracking, plus instruction metadata where available | Not executed; instruction labels may not be supplied |
| Repeatability of half-second launch block | Raw pass-rush tracking or saved launch-event table | Not executed; do not inherit the longer-window metric's reliability |
| Exposure thresholds, outliers, NFL game/team clustering and refit uncertainty for get-off | Prepared rush/context records, game/player identities and original inputs | Not executed; prepared get-off table absent |
| Prospective transfer confirmation | Genuinely uninspected eligible cohort under a frozen protocol | Unavailable; reshuffling inspected players does not supply it |

## Proposed repository modifications

`docs/KAGGLE_COMBINE_WRITEUP.md` is replaced by the shorter competition narrative. New files add four PNG/SVG figure pairs, aggregate derivation receipts, a paired source-only audit, a full Rules review, sharp oracle ceilings and exact interaction/shrinkage certificates, a submission notebook, deterministic notebook/figure builders, a cell-execution verifier, three tests, this review and the mathematical companion. The original notebook, original estimator/extractor modules, source protocols and historical NFL receipts are unchanged. The complete patch and source snapshot are in the bundle.

The existing Explorer feed exporter was run locally as required by repository guidance. No public feed contract or live consumer was changed; any exporter failure or live endpoint result is recorded in the validation receipt. No Site deployment or native executable change is part of this proposal.

## Publication steps requiring author review

Review the writeup, four figures, notebook and patch. Full Rules inspection is complete. Confirm author/team eligibility and submission-specific licensing as applicable. After explicit authorization, create the public Kaggle notebook, verify its displayed figures and data handling in that environment, attach it to the writeup and replace the local notebook reference with its real Kaggle URL. A fresh official raw-mode run is recommended to verify the new wrapper; until then disclose that receipt-mode execution is the verification available for this revision. Public outputs must contain only the writeup, code and aggregate figures/receipts, never the private continuation or temporary working directory.

No entry submission is authorized. Approval to publish a notebook or repository patch would still not authorize submitting the competition entry unless explicitly stated.
