# Prospective generated-width family extension

Normalized provenance matches in the checksum-verified MC2021 collected archive
resolve the strong three-literal cluster to the GPUSAT submission's
`plain/dynasp_all` directory. Eight declared winning seeds match this directory:
MC2024 085, 086, 090 and 091, and MC2025 069, 071, 073 and 074. These are
generated benchmark instances, not demonstrated production workloads.

Before inspecting solver outcomes for this additional cohort, select up to 24
predicted-tractable and 12 rejected controls from that directory only. Apply
the same bounded unit-propagation/component min-degree predictor: maximum
scope 18, estimated states 8000000 per component, largest component above 256
for positive selection, per-component variables at most 8192, initial directed
edges at most 400000. Keep byte/literal/clause profile limits and exclusions.
Reject unit contradictions from selection. Exclude normalized matches to all
profileable MC2024/MC2025 inputs and to the first fresh cohort. Conservatively
exclude any declared variable count shared with an oversized known competition
input. Sort each group by SHA256 with source member as tie breaker, and take
the declared cap. Do not backfill after timing or select by favorable results.

Write the complete source-directory inventory, exclusions, selected manifest,
protocol and profiler identities before solver invocation. Use the unchanged
0.10.2 counter with source SHA256
f2b0276553ce201aceb13a7bd46bc5837a54bdb1634fc497ae8c3b3ebe9006aa.
This is a prospective extension within a known generated-width family. It is
not a blind real-world or family-independent evaluation.

Run the same four solvers at five seconds and 6 GiB, serially with rotated
order and cold subprocess timings. Retain every selected case in the primary
scope. Repeat every predicted-tractable case, including failures, three times
at the same limits. Independently confirm current exact counts; unconfirmed
answers receive a separate thirty-second reference check and never replace
primary failures. Report this cohort separately from the first fresh cohort.
No profiling or provenance computation overlaps timed comparisons.
