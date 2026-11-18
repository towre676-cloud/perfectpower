# Measurement, transfer and the loss a player constant can change

4 November 2026. Mathematical companion to the proposed Big Data Bowl 2027 entry. This document is supporting material, outside the competition writeup. The analysis remains retrospective; no scouting model is promoted.

## What the two empirical questions identify

Split-attempt Spearman correlation estimates agreement in player rankings under a particular split of retained attempts. It does not identify a latent biological reliability coefficient, within-athlete absolute measurement agreement, or forecasting utility. In particular, an ICC, standard error of measurement or classical-error attenuation correction cannot be recovered from these rank correlations alone. Applying the Spearman–Brown formula to them would need assumptions not demonstrated here.

The source-only audit uses the development classes, alternating event IDs within player and drill, and medians within halves. There are 39 repeated pass-rush players with 84 complete shared attempts. The original feature-specific audit was rerun from the hash-matched private continuation and exactly reproduced its JSON, including its source and input hashes. This is a fresh replay of saved-attempt features; it is not fresh reconstruction from raw sensor observations.

The new paired comparison uses the same complete attempts for both coordinates. Let r_s and r_a be their split-attempt Spearman correlations. The observed difference r_s − r_a is 0.2603238866. Resampling the common players jointly across both features and both halves, with 4,000 draws and seed 20261104, gives the pointwise percentile interval [−0.1053659249, 0.6504284520]. All draws are valid. This source-only diagnostic was selected after the marginal results were known. It is exploratory, has no adjustment for researcher selection, and does not establish a superiority claim. NFL labels never enter this function.

The longer-window speed-gain coordinate is an onset-scenario average of net smoothed speed change over the retained active window, followed by player medians. It is distinct from the half-second launch coordinate. Reliability of one must not be transferred to the other by naming them both “burst.”

## Baseline-relative forecasting gain

For baseline b_i, response y_i and actual prediction change d_i, define e_i = y_i − b_i. The squared-error reduction is exactly

\[
 e_i^2-(e_i-d_i)^2=2e_i d_i-d_i^2.
\]

The prediction change must align with held-player baseline errors sufficiently to pay for its own squared magnitude. Shrinking or capping a correction bounds its size; it does not ensure favorable alignment. This identity also holds for the compact pressure estimator if d_i is defined as its actual post-clipping change, rather than the pre-clipping ridge output.

The selection rule compares a bounded fixed correction to exact zero using training players. Passing an inner one-standard-error heuristic does not establish a nonnegative expected future gain. The compact selected policy's negative development and exploratory 2025 outcomes demonstrate why outer reporting must preserve failed selections. Exact fallback has zero observed loss difference by construction. A degenerate bootstrap interval at zero for that comparison is not a confidence interval asserting no useful tracking signal in the population.

Denominators matter. In development the conventional pressure MSE is 0.0009532055705 and the global mean MSE is 0.0011353074846. The conventional reduction relative to the mean is 16.04%. Conversely, the mean is 19.10% worse relative to the conventional baseline. These are the same comparison with different denominators. Neither is evidence that movement improves on conventional measurements.

## Exact player-mean and play-level decomposition

For player i with n_i held-out plays, let e_ij = y_ij − b_ij and let ē_i be their average residual. Define the primary player loss P_i = ē_i², the auxiliary loss A_i = (1/n_i)Σ_j e_ij² and the centered residual component V_i = (1/n_i)Σ_j(e_ij − ē_i)². Expanding the square gives

\[
 A_i=P_i+V_i.
\]

No distributional assumption is needed; V_i uses divisor n_i, not an unbiased sample-variance divisor. Giving each player equal weight preserves A = P + V. The identity also survives averaging losses across repeated fits because it holds separately within every player/fit.

In the implemented get-off estimator, Combine source traits and launch measurements are constant within player. Its prediction has the form c(x_ij) + s_i + d_i, where c is the shared context fit, s_i is the conventional source offset and d_i is the bounded launch offset. There is no clipping of the real-valued time response. Subtracting d_i from every residual changes the player's average residual but leaves every centered residual unchanged:

\[
 (e_{ij}-d_i)-(\bar e_i-d_i)=e_{ij}-\bar e_i.
\]

Consequently V_i is identical with and without the correction. The absolute changes in primary and auxiliary loss are equal. Their *relative* changes differ because the denominators differ. The same statement holds between context-only and context-plus-source predictions when they share the context fit.

The receipt arithmetic verifies the invariance to numerical tolerance 10⁻¹² for context-only, fixed and selected predictions relative to conventional-plus-context. The baseline components are:

| Evaluation | Primary P (s²) | Auxiliary A (s²) | Centered residual V (s²) | V/A |
| --- | ---: | ---: | ---: | ---: |
| Repeated 2023/24 development | 0.004430011243 | 0.056355198952 | 0.051925187709 | 92.1391% |
| 2023→2024 | 0.002550499742 | 0.055902442901 | 0.053351943159 | 95.4376% |
| Exploratory 2025 | 0.002263030824 | 0.057389589574 | 0.055126558750 | 96.0567% |

For 2024 the fixed correction's absolute reduction is −0.0002259736525 s². Dividing by P gives −8.85998%; dividing by A gives −0.404229%. This is one observed loss change evaluated relative to two different objectives. It is not a disagreement between studies. Within-player residual variation is not irreducible noise: context interactions, assignments, opponents, measurement error and model misspecification could contribute. A player-constant correction is structurally unable to change it; a different model need not have that limitation.

The proposed movement-by-context extension is a future hypothesis, not an evaluated remedy. It would require fitting within the same player-separated boundaries, retaining all baseline controls and testing on genuinely uninspected data before claiming transfer.

## Scope of verification

The original nine-file official reconstruction is historical evidence tied to the unchanged notebook SHA-256 09d327c78bf20cc434ef6ce770b9fbb4126a772b037afd6968a296e41dc3204a. Its receipt reports exact agreement for 12 pressure and 30 get-off MSE comparisons. It does not certify the new wrapper notebook. The revised notebook's receipt mode was executed cell by cell in a fresh Python process and recreated four aggregate figures; no raw tracking inputs or get-off context were present. Its raw mode reuses the historical compute cells and compares those same 42 MSE values if official inputs become available.

The original repeatability audit's saved-attempt replay is new execution and is distinguished from the historical NFL fits. No new feature search, NFL outcome inspection, estimator refit or independent validation was performed. The separate sealed linebacker study was not read.

## Sharp oracle ceiling for every player-constant correction

**Theorem.** Fix the existing baseline predictions and the retained evaluation records. Among all possible constants d_i, even constants selected with knowledge of the held-out responses, the minimum auxiliary loss is V. Hence the largest possible relative play-loss reduction is P/A.

**Proof.** For every player,

\[
 A_i(d_i)=V_i+(\bar e_i-d_i)^2\ge V_i.
\]

The lower bound is attained by the label-aware oracle d_i = ē_i. Average equally across players. Since A = V + P, maximum absolute reduction is P and maximum relative reduction is P/A. The bound is sharp. It applies separately within each repeated fit and therefore to their averaged losses as well. ∎

| Existing evaluation | Maximum possible play-MSE reduction by any player constants | Oracle minimum play MSE (s²) |
| --- | ---: | ---: |
| Repeated development | 7.860874% | 0.051925187709 |
| 2023→2024 | 4.562412% | 0.053351943159 |
| Exploratory 2025 | 3.943278% | 0.055126558750 |

These are ceilings for the fixed baseline and evaluated records, not achieved gains, population bounds or transferable future-class guarantees. Source-only corrections form a smaller class than the unrestricted label-aware oracle, so they cannot exceed this ceiling on these same records. Changing the context model changes the baseline and can change the ceiling.

**Bounded version.** If |d_i| ≤ c_i, minimizing the square gives the exact oracle

\[
 d_i^*=\operatorname{clip}(\bar e_i,-c_i,c_i),\qquad
 A_{\min}=\frac1N\sum_i\left[V_i+(|\bar e_i|-c_i)_+^2\right].
\]

The bounded optimum can never beat the unrestricted one. For a common bound c, a bound needing only P is

\[
 A_{\min}\ge V+(\sqrt P-c)_+^2.
\]

To prove it, apply the reverse triangle inequality to the equal-player Euclidean norm: ||μ−d|| ≥ (||μ||−||d||)_+ ≥ (√P−c)_+. The bound is tight when all |μ_i| = √P, with corrections aligned with μ. Exact evaluation of the per-player clipped oracle requires player residual means; they are unavailable for the current get-off study and were not invented from aggregates.

## A centered interaction can target variation without changing average calibration

**Theorem.** Let h_ij be any proposed play-varying correction. Define its within-player centered version q_ij = h_ij − mean_j(h_ij), and let r_ij = e_ij − ē_i. For a combined correction d_ij = a_i + q_ij,

\[
 A-A_{\mathrm{new}}
 =\frac1N\sum_i(2\bar e_i a_i-a_i^2)
 +\frac1N\sum_i\left[2\overline{r_iq_i}-\overline{q_i^2}\right].
\]

**Proof.** Expand mean_j[(e_ij−a_i−q_ij)²]. Both r_i and q_i have zero within-player mean, so their cross-terms with constants vanish. The first bracket is the change in systematic mean error; the second is the change in centered residual variation. ∎

Thus a centered interaction with a_i = 0 leaves primary player-mean loss exactly unchanged, while it may improve or worsen auxiliary snap-level loss. On the fixed records it helps precisely when 2 mean_i mean_j(r_ij q_ij) > mean_i mean_j(q_ij²). A movement-by-context feature is a candidate for this *different* task, not an established improvement. The prediction and all nuisance fits must exclude held-player responses. Centering may use the player's observed covariates for this retrospective conditional task; centering over a full held-out season would not by itself define an online prediction procedure. Online use would require a separately fixed causal/running centering rule and new evaluation.

## A failed full-strength correction does not determine optimal shrinkage

For a fixed player correction direction d, let C = mean_i(ē_i d_i) and D = mean_i(d_i²). At scale λ, exact mean-loss gain is

\[
 G(\lambda)=2\lambda C-\lambda^2D.
\]

If D > 0, the oracle scale on [0,1] is clip(C/D,0,1). If C ≤ 0, no positive scale helps. If C > 0, sufficiently small positive scales help on these same records. Both statements concern hindsight oracles, not a valid procedure for choosing λ on held-out data.

Knowing G(1) alone does not identify C or D. Here is an exact finite witness. Take four players with baseline residual mean 1 each. Direction (1,−1,1,−1) has C = 0, D = 1 and full-strength gain −1; its best nonnegative scale is zero. Direction (3,−1,1,1) has C = 1, D = 3 and the same full-strength gain −1; its best scale is 1/3 with hindsight gain 1/3. Both have baseline MSE 1 and full-strength candidate MSE 2. Multiplying all residuals and directions by a common positive factor makes both examples obey any positive correction cap while preserving their different optimal scales.

Therefore the observed −8.86% get-off result cannot justify either “all shrinkage must fail” or “more shrinkage will fix it.” Computing the alignment and correction-energy terms requires the unavailable get-off prediction vectors. Any future scaling choice belongs strictly inside training; using this study's held-out failures to select a new scale would be further retrospective development.

## Arithmetic certificates and proof status

`audit_combine_loss_geometry.py` converts the saved decimal MSEs to rational numbers and records exact P/A fractions, minimum losses and finite witnesses in `receipts/kaggle_combine/loss_geometry.json`. Rational arithmetic is exact for the stored decimal values; it does not turn underlying floating-point empirical MSEs into exact measurements of population risk. The proofs above are mathematical derivations, with exact finite regression checks; they are not Lean-formalized theorems. No NFL model is refitted or promoted by these additions.
