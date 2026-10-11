# Locating the structural advantage

This study leaves the 0.10.2 native counter unchanged. Its purpose is to locate
repeatable advantages and test a structural prediction on previously unmeasured
inputs. The 400 MC2024/MC2025 competition instances are development evidence,
not independent training examples or unseen holdouts.

The structural measurement applies unit propagation, builds each residual
component's primal graph, and follows a minimum-degree order with variable-ID
tie breaking. Acceptance requires at most 8192 variables per component,
initial directed edges at most 400000, bucket scope at most 18, and estimated
states at most 8000000 per component. It measures a heuristic upper bound,
not minimum treewidth. Profiling is bounded to 8 MiB, 300000 literals and
clause width 1024. Exclusions remain explicit. No solver times enter profiling.

The recurring-reference-win seeds are MC2025 cases 043, 069, 071, 073 and 074,
and MC2024 cases 010, 013, 054, 085, 086, 090, 091 and 096. Their original
source families will be resolved by normalized CNF matching against the
corrected MC2024 collected archive, Zenodo record 14969231, expected MD5
d2976e44c6a678404c01da779cb09007. Canonical identities retain declared free
variables and literal signs while ignoring clause/literal order, duplicates
and tautologies. This is not a semantic-isomorphism audit.

All profileable members of the matched families will be inspected without
solver timings. Existing normalized competition matches will be excluded.
Members sharing a declared variable count with an unnormalized, oversized
known input will also be excluded conservatively. The fresh scope consists
of up to 24 predicted-tractable cases with largest residual component above
256, and up to 12 noncontradictory profileable rejected controls. Each group
is selected in round-robin family order, with lexicographic SHA256 order
within each family. No elapsed time, count, previous result or solver outcome
may influence selection. If a group has fewer candidates, retain all and
report the shortfall; do not backfill after measurement.

The selected manifest, all normalized exclusions, source-member identities,
profiles and native-source identity must be written before invoking solvers.
These are fresh inputs for this study from known source families, not a
family-independent blind holdout. Selection for structural tractability is
intentional and must not be represented as an all-corpus ranking.

The first comparison uses PerfectPower 0.10.2, paired baseline 0.10.1,
deterministic Ganak 2.8 and archived D4 2024, serially with rotated solver
order, five-second cold subprocess budgets and 6 GiB virtual-address limits.
Every selected input remains in the denominator, including failures. Native
compilation is warmed separately. Results include coverage, PAR-2, exact
count agreement, predictor-group outcomes and measured versus censored speed
ratios. A timeout ratio is only a lower bound, never an exact speedup.

Every predicted-tractable selected case, including any failures, then receives
three trials at the same five-second budget. This repeat scope is fixed by
the structural label, not by which solver won the first screen. Any current
exact count unconfirmed by another solver receives one thirty-second
reference-validation trial; unresolved counts remain explicitly unconfirmed.
No longer result replaces a primary failure. The selection and all failures
are retained in the complete evidence handoff. Source mapping failures remain
unresolved rather than being guessed from adjacency or filenames.

Before any fresh timing, the 2024 archive inspection found no normalized match
for the declared advantage seeds among its 2505 CNF members. Provenance search
therefore extends to the organizers' 2020–2023 collected archives. Expected
MD5 identities are c69a07dc1f1fed5cdbc434d005ea5752 (2020, record 10004947),
74463335843cdbec64a5d0993fd66518 (2021, record 10006441),
afe4d1d517c12f018f17e08b85aa27d1 (2022, record 10014715), and
0519f1ae0003c68ec06ff217259a8be2 (2023, record 10012822).
Selection uses the earliest archive year with any resolved seeds, while later
archives remain provenance-only. This archive rule is fixed before their
contents or fresh solver results are inspected. All other structural selection
rules, caps and repetitions above remain unchanged. It avoids replacing a
missing source match with an unrelated source family.
