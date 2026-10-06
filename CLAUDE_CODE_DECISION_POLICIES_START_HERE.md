# Decision policies handoff

Read docs/DECISION_POLICIES_MONOGRAPH.md. CalibrationPolicy discovers complete closed cells with an exact optimizer at every vertex, including lower-dimensional cells and all ties. DiagnosticPolicy minimizes worst-case cost over all finite operator words and adaptive resettable trees within its budgets. ProjectedPopulation now supports complete cubic collision ellipses and higher-degree fields with strict discrete monotonicity on the convex source hull.

```sh
export PYTHONPATH=python
python python/develop_decision_policies.py --output /tmp/policies
python -m unittest discover -s python/tests -p test_decision_policies.py
python -m perfectpower service --database /tmp/policies.sqlite < receipts/decision_policies/service_requests.jsonl
make test
```

Open receipts/decision_policies/policy_workbench.html locally. Its decisions use BigInt rational arithmetic. Drawing alone uses approximate coordinates. All model setting digits are retained as strings in the viewer.

Ten catalogue kinds are supported. New kinds calibration_policy and diagnostic_policy expose decide and step/run respectively. Prefer named readout costs; positional costs use canonical sorted readout names. Diagnostic hypotheses cover the full observable state space, with no seed-reachability restriction. Experiments reset to the original unknown hypothesis; reset cost is zero, readouts are noiseless and operator costs strictly positive. Stateful or noisy experiments require different mathematics.

The coupled setting example has fifteen cells and a minimax diagnosis cost three versus four for its cheapest single complete readout. The lazy-window example discovers one relevant setting among 231 feasible possibilities using four oracle calls. Cubic projection addresses 2×10^50-1 distinct values without enumeration. Preserve the distinction between complete declared-model policies and physical deployment assumptions.

All operation budgets fail without a completed-policy claim. Full Python evidence is provided; no new Lean theorem or physical quark interaction is claimed. Include the complete uncapped ZIP and monograph with every research/software push.
