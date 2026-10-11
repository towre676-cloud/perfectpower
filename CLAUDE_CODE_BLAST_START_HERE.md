# BLAST polynomial atlas: start here

The October 11 mining extension is documented in `docs/BLAST_MINING_MACHINERY.md`. Run `make blast-mining-test` and `make blast-mining` for source replay, compressed HSP DAG populations, separator/native selection counts, overlapping motif series, Hall/flow assignment certificates and triangle-filled similarity topology. Open `web/blast-mining/index.html` for the three-record batch explorer. New CLI commands are `mine`, `verify-mining`, `mining-report` and `motif`. The optional native backend requires C++17 and Boost; the default separator backend uses the Python standard library.

This branch extends PerfectPower with exact biological-sequence exploration. The main monograph is `docs/BLAST_POLYNOMIAL_ATLAS_MONOGRAPH.md`; the runnable offline demonstration is `web/blast-atlas/index.html`. The retained public inputs and actual BLAST+ output are in `examples/blast/`. The default package still has no external Python dependencies.

Run `make blast-test` for the independent checks and `make blast-atlas` to regenerate the atlas. Run `make blast-lean` in a configured Lean 4.20.0/mathlib environment for the source-bound formal build. `receipts/blast/kernel_build.json` records the actual build undertaken for this release. Two pre-existing kernel-dependent checked-SOE tests were skipped in the ordinary regression invocation; the new literal SOE packets were compiled separately.

The package exposes `perfectpower-blast` and `python -m perfectpower.blast_cli`. Use `align` for complete bounded global families, `pair` for exact scalar local/global alignment, `ingest` for tabular output with BTOP, and `report` for offline HTML. Acquisition commands are explicit: `fetch`, `blast`, `submit` and `retrieve`. The URL API's ordinary tabular output is saved as raw evidence because it need not expose the BTOP fields required by the strict importer.

The main adapters call existing repository machinery rather than replacing it: `psg_polynomial.Polynomial`, `psg_jets.convolution`, `future_states`, `checked_soe.compile_soe`, `observable_machine.minimal_machine`, `semantic_fibres.Transport`, `diagnostic_programs.DiagnosticPolicy`, `gamma_arithmetic.normalize`, `weighted_hodge`, and `connection_polytope.ConnectionGraph`.

Preserve the explicit scope distinctions. The family polynomial counts operation paths of the declared global model. Scalar local alignment returns one optimum, not all local multiplicities. Parameter regions concern the supplied feature support. SOE proves supplied finite-machine behavior, not source-adapter correctness. Similarity graphs are supplied evidence objects, not inferred phylogenies. Fixed-comparison binomial tails are never BLAST E-values. Protein composition adjustment and translated coordinate adapters remain unimplemented.

The suffix recurrence now has an explicit Lean finite-language proof. The retained INS corpus and the independent OXBench structural-domain evaluation extend the empirical work. OXBench is not an orthology/paralogy benchmark: its external structure-derived reference sets measure domain retrieval and conserved-residue agreement.
The combined release targets `codex/blast-mining-machinery-20261011`.
Read `docs/BLAST_CERTIFICATION_MONOGRAPH.md` for exact claim boundaries.
`data/blast_corpus/manifest.json` pins all 930 INS-query RefSeq accessions;
`query_sources.json` pins external mouse Ins1 annotation. BLAST tabular sources
are lossless `.tsv.gz` files. `receipts/blast/certification/` contains every pair,
every HSP audit and annotation, all CDS audit states, repeated timings, and
fresh Lean logs. Generic proofs are `PerfectPower/BlastRecurrence.lean` and
`PerfectPower/BlastSourceReplay.lean`. The generated literal kernel run covers
all word-28 HSPs. Word-7 and word-11 outputs have complete executable audits.
Do not relabel their receipts as literal kernel checked, and do not generalize
the measured recall to nt/nr or biological orthology. Whole-corpus reproduction
is offline unless `python/develop_blast_certification.py --run-blast` is explicitly
selected; live source acquisition is a separate `python/fetch_blast_corpus.py`
command. Require a new manifest for any database refresh.

Read `docs/BLAST_OXBENCH_MONOGRAPH.md` for the complete 395-set, 3,292-occurrence protein benchmark. `make blast-oxbench-test` runs all BLAST tests; `make blast-oxbench-replay` replays both retained search outputs offline. `python scripts/check_blast_oxbench.py` independently checks source coordinates, every positive-pair denominator, and bounded exhaustive chain populations. `python scripts/check_oxbench_kernel.py --lean lean` checks the shared generic proofs and 24 literal protein HSPs. The entire protein output is executable-replayed; only the listed literal samples are kernel-checked. The standard run retrieves 73,006 of 101,750 directed positive pairs with either ordinary or exact chaining, versus 73,003 using single HSPs. Complete counting costs more than maximum-only chaining on this corpus.

See `docs/BLAST_FINISH_RELEASE.md` and `receipts/blast/finish/` for the combined completion evidence and remaining mathematical claim boundaries. Publication status is recorded separately from local validation; a local commit is not proof that the GitHub branch advanced.
