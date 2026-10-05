# Direct-use applications handoff

Read docs/APPLICATIONS_MONOGRAPH.md and docs/DIRECT_USE_BUILD_ROADMAP.md. Six persistent object kinds, measured tuning and grouped evaluation are implemented. There is no new Lean theorem or industrial speedup claim.

```bash
export PYTHONPATH=python
python -m unittest discover -s python/tests -p test_applications.py
python python/develop_applications.py --output /tmp/apps
python -m perfectpower service --database /tmp/apps.sqlite \
  < receipts/applications/service_requests.jsonl
make test
```

Open receipts/applications/geometry_workbench.html directly in a browser. It is offline. Application APIs are in application_objects.py, catalogue.py, query_service.py, configuration_tuning.py and task_protocol.py under python/perfectpower. Service methods require explicit allowlisting and validation.

Catalogue addresses refer to canonical definitions. Explicit alias replacement preserves old definitions. Restrictions and graph reweights create derived objects. Equality joins preserve multiplicities and require both inputs and the full result to fit budgets.

Graph sampling uses exact rational event probabilities for orders 2,3,4,6. Tests exhaust random paths and compare independent basis sums. Higher-order floating-point decisions must not be labelled exact. This is a gain-graph basis model, not a generic unsigned spanning-tree service.

The tuner checks real outputs against an independent reference and records all trials. The conventional baseline wins the demo. Preserve that finding. New kernels and hardware claims require new measurements.

Signed siblings stay in one task partition. Public files omit answers; withhold heldout_private.json during blind evaluation. The recorded evaluation is oracle replay, not agent accuracy or unseen-family generalization.

Global chart transitions, broader effective backends and physical symmetry derivations remain open. For every research/software push, provide a complete source ZIP below 30 MB and the corresponding monograph PDF.
