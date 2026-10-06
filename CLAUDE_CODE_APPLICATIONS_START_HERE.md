# Direct-use applications handoff

Read docs/OPEN_CONTENT_MONOGRAPH.md and docs/DIRECT_USE_BUILD_ROADMAP.md. Eight persistent kinds now cover population, projected values, linear sequences, nonlinear factorial families, inverse design, gain graphs, geometry and combinatorial sizes. The archive has no size cap. Existing research history, Lean sources and receipts are retained.

```bash
export PYTHONPATH=python
python -m unittest discover -s python/tests -p test_open_content.py
python python/develop_open_content.py --output /tmp/open-content
python -m perfectpower service --database /tmp/open-content.sqlite \
  < receipts/open_content/service_requests.jsonl
python -m perfectpower service --database /tmp/open-content.sqlite --http-port 8080
make test
```

The demo requires a C99 compiler and a repository checkout for native source lookup. The mathematical runtime uses the standard library. PDF rendering uses optional reportlab/matplotlib; Lean builds require the pinned Mathlib environment.

Open receipts/open_content/geometry_workbench.html directly in a browser. Branch/infinity panels have certified transitions to the finite panel, and selected grid points display exact transport and density factors. This is a local compatible workbench, not a global atlas.

Catalogue addresses refer to canonical definitions. Alias replacement preserves old definitions. Restrictions and graph reweights create derived objects. Projected degree-0/1/2 fields use distinct-value identities; symbolic equality joins retain original parameter pairs and require a supported complete curve backend. Do not confuse these identities.

Graph sampling is exact for declared orders 2 through 64, using rational or certified algebraic comparisons; a work-budget failure returns no draw. Keep analytic premises and Python execution separate from Lean verification. Every stored comparison can be recomputed by verify_decision.

The tuner checks every full compiled output against independent Python dot products. Conventional C dot-product and cache-friendly untiled C controls are interleaved with candidates. Preserve all controls, trial times and scope. The old application's separately timed conventional Python kernel won its own demo and remains historical evidence.

Whole declared source families are held out. Public files omit answers; withhold heldout_private.json during blind evaluation. The measured public-prompt baseline is an exact solver, not an LLM. Canonical source aliases cannot cross splits, but differently encoded mathematical equivalences still require source review.

Distinguishing experiments now optimize globally over finite words with positive operator costs. Bounded calibration supports inequalities and every tied optimum inside the supplied finite box. Neither work-budget failure may be labeled a complete optimum.

The flavor diagnostics prove exact constraints within a specified scalar polynomial model. They do not derive physical mixing. Keep the full operator audit and unresolved interaction obligations. Historical open notes are retained verbatim with source hashes; their keyword matches are not automatic present-day proof statuses.

For every research/software push, provide a complete source ZIP and corresponding monograph PDF. There is no archive size cap. New Python functionality is tested and replayable; this release adds no Lean theorem. General effective arithmetic, smooth global geometry, analytic/kernel foundations and UV model derivation remain open.

The three largest full receipts are deterministic `.json.gz` files. Use `python python/unpack_open_content.py` to create plain JSON copies locally; no records are omitted.
