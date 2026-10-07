# One-command reproduction.  `make verify` must end green on a fresh checkout.
PY      ?= python3
SAGEPY  ?= sage -python
export PYTHONPATH := python

.PHONY: residue-determinant
residue-determinant:
	bash scripts/check_residue_determinant.sh

.PHONY: elliptic-bridges
elliptic-bridges:
	bash scripts/check_elliptic_bridges.sh


.PHONY: why3-session verify release-verify lean audit lint test cert-audit receipts counts descent-gate fresh oeis check-clean crosscheck fuzz bench paper adapter-bench nia-ledger nia-timing why3-bridge order-cost

verify: lean audit lint test cert-audit receipts counts descent-gate dresden-lean check-clean
	@echo "verify: OK"

# A release that advertises the SMT adapter must run its tests: fail if z3-solver is missing.
release-verify:
	@$(PY) -c "import z3" || (echo 'release-verify: z3-solver is required (pip install z3-solver)'; exit 1)
	$(MAKE) verify

lean:
	./scripts/build_heavy.sh

audit: lean
	./audit/check_axioms.sh
	lake env lean audit/CertReject.lean

lint: lean
	lake env lean audit/Lint.lean

test:
	@$(PY) -c "import importlib.util as u; print('z3-solver:', 'present: adapter/certificate tests run' if u.find_spec('z3') else 'ABSENT: adapter/certificate tests skipped')"
	$(PY) -m unittest discover -s python/tests
	$(PY) -m unittest discover -s continuation_tests
	$(PY) -m unittest discover -s expert_push/tests
	$(PY) -m unittest discover -s galois_merge/tests

# Public elliptic witnesses, complete rational [2] fibres and discovery-free replay.
.PHONY: elliptic-witnesses
elliptic-witnesses:
	$(PY) -m unittest discover -s python/tests -p 'test_elliptic_*.py'
	$(PY) python/develop_elliptic_witnesses.py

.PHONY: elliptic-composed-division
elliptic-composed-division:
	$(PY) -m unittest discover -s python/tests -p 'test_elliptic_division.py'
	$(PY) python/develop_elliptic_division.py

.PHONY: elliptic-subgroups
elliptic-subgroups:
	$(PY) -m unittest discover -s python/tests -p 'test_elliptic_subgroups.py'
	$(PY) python/develop_elliptic_subgroups.py

.PHONY: elliptic-division-lean
elliptic-division-lean:
	lake build PerfectPower.EllipticDivision
	lake env lean audit/EllipticDivision.lean

.PHONY: nonflavor-frontier-lean nonflavor-frontier-receipts
nonflavor-frontier-lean:
	lake build PerfectPower.NativeRationalRoots PerfectPower.EllipticPointDivision PerfectPower.FiniteDomainCertificate PerfectPower.RectangularDeterminant PerfectPower.GeneralCRT PerfectPower.FactorialWindow PerfectPower.QuarticCollision
	lake env lean audit/NonFlavorFrontier.lean
	lake env lean audit/FactorialWindowGenerated.lean

nonflavor-frontier-receipts:
	$(PY) python/develop_nonflavor_frontier.py --monodromy

cert-audit:
	$(PY) python/independent_cert_audit.py

receipts:
	$(PY) python/make_receipts.py
	$(PY) python/make_atlas_receipts.py
	$(PY) python/make_lean_certificates.py
	$(PY) python/adversarial_runge.py 300
	$(PY) python/pillai_census.py 18 1000
	$(PY) crosscheck/mordell_census.py --from-jsonl 10000
	$(PY) crosscheck/check_binomial.py
	$(PY) crosscheck/check_genus1.py
	$(PY) crosscheck/check_theorem_g.py
	$(PY) python/make_lean_genus1.py
	$(PY) python/make_lean_census.py
	$(PY) python/make_lean_mordell_descent.py
	$(PY) python/uniformity.py
	$(PY) python/make_pell_heat_receipt.py
	$(PY) python/make_lean_mordell_branch.py
	$(PY) python/make_lean_thue_branch.py
	$(PY) python/unit_basis_witness.py
	$(PY) python/norm_rep_localization.py
	$(PY) python/make_lean_unit_fields.py
	$(PY) python/order_transport.py
	$(PY) python/norm_cover.py
	$(PY) python/make_lean_curves.py
	$(PY) python/descent_coverage.py
	$(PY) python/positive_k.py
	$(PY) python/class_list_cert.py
	$(PY) python/class_list_cert.py k2
	$(PY) python/rank_one_sources.py
	$(PY) python/class_list_cert.py rank1
	$(PY) python/positive_k_next.py
	$(PY) python/skolem3_scan.py --receipt receipts/positive_k_next.json --radius 6 --output receipts/skolem3_candidates.json
	$(PY) python/positive_k_oeis.py
	$(PY) python/make_mordell_registry.py
	$(PY) python/gap_atlas.py
	$(PY) python/make_lean_bounded.py
	$(PY) python/make_lean_plans.py
	$(PY) python/constraint_demos.py
	$(PY) python/make_oeis_problems.py
	$(PY) python/d72_local.py
	$(PY) python/d72_delta_box.py 40
	$(PY) python/d72_unit_sieve.py
	$(PY) python/descent_residual.py
	$(PY) galois_merge/run_repo_adapters.py
	$(PY) python/make_oeis_auto.py
	$(PY) python/make_oeis_atlas.py
	$(PY) python/make_mordell_obstructions.py

# Estimated kernel cost of the unresolved curves (receipts/order_cost.json; an estimate, not a proof;
# about five minutes, so not part of verify)
order-cost:
	$(PY) python/order_cost.py

counts: audit
	$(PY) python/make_counts.py

# An unseen constraint, proved end to end (fixed seed here; `make fresh` draws a new one).
descent-gate: lean
	$(PY) python/descent_fresh.py --seed 20260930

fresh: lean
	$(PY) python/descent_fresh.py

# Compare with a local OEIS snapshot (not committed; see docs/OEIS.md):
#   make oeis STRIPPED=~/oeis/stripped.gz NAMES=~/oeis/names.gz RETRIEVED=2026-09-30
oeis:
	$(PY) -m perfectpower oeis --stripped $(STRIPPED) --names $(NAMES) --retrieved $(RETRIEVED) \
	  $(if $(REVIEWED),--reviewed $(REVIEWED)) > receipts/oeis_atlas.json

# Regenerated files must match the committed ones exactly.
check-clean:
	git diff --exit-code -- receipts/ certs/ data/ docs/figures/ docs/STATUS.md PerfectPower/Generated/ README.md audit/axioms_report.txt

# Optional: needs Sage or passagemath (see crosscheck/README.md).
crosscheck:
	$(SAGEPY) crosscheck/cubics_sage.py 12 100000
	$(SAGEPY) crosscheck/binomial_curves.py
	PYTHONPATH=python $(SAGEPY) crosscheck/genus1_sage.py 400 3
	$(SAGEPY) crosscheck/theorem_g_sage.py 8 8 4
	$(SAGEPY) crosscheck/mordell_census.py 10000 4
	$(SAGEPY) crosscheck/branch_thue_pari.py 600
	$(SAGEPY) crosscheck/thue_fields_pari.py
	$(SAGEPY) crosscheck/field756_pilot.py
	$(SAGEPY) crosscheck/d72_unit_pilot.py 40
	$(SAGEPY) crosscheck/thue_bound_d72.py
	$(SAGEPY) crosscheck/thue_bound_field756.py

# Host-solver adapter benchmark (constructed instances; needs z3-solver on PYTHONPATH)
adapter-bench:
	$(PY) python/host_adapter_bench.py 10

# Independent QF_NIA corpus (independent_nia/; needs z3-solver on PYTHONPATH): adapter ledger and
# query-level z3 timing.  Not part of verify (timings are machine-dependent).
nia-ledger:
	$(PY) python/nia_ledger.py independent_nia --baseline independent_nia/reports/z3_cvc5.json --baseline independent_nia/reports/z3_elster.json --baseline independent_nia/reports/z3_staub.json --out independent_nia/reports/perfectpower_ledger.json

nia-timing:
	$(PY) python/nia_query_timing.py independent_nia --query-timeout 2 --file-budget 120 --out independent_nia/reports/z3_query_timing.json

# Why3 consumer bridge on the example VCs (needs why3 and z3; not part of verify)
why3-bridge:
	$(PY) python/make_why3_bridge.py

# Differential fuzzers with fixed seeds (python/fuzz/); the finite-bucket scan goes to 1e8.
fuzz:
	PYTHONPATH=python $(PY) python/fuzz/fuzz_structural_vs_scan.py 1 1500
	PYTHONPATH=python $(PY) python/fuzz/fuzz_structural_vs_scan.py 2 1500
	PYTHONPATH=python $(PY) python/fuzz/fuzz_pell_quadratic.py 7 400
	PYTHONPATH=python $(PY) python/fuzz/fuzz_finite_bucket_late_hits.py 11 1500 100000000

# Certificate benchmarks (timings vary by machine; not part of verify).
bench:
	$(PY) python/cert_benchmarks.py
	$(PY) python/constraint_benchmarks.py

paper:
	cd paper && pdflatex -interaction=nonstopmode perfectpower.tex >/dev/null && pdflatex -interaction=nonstopmode perfectpower.tex >/dev/null && rm -f *.aux *.log *.out

# Native Why3 sessions (why3_isqrt/sessions): replay the committed sessions with `why3 replay`.
why3-session:
	$(PY) why3_isqrt/native_session.py --check

.PHONY: connected-closures-lean connected-closures-receipts
connected-closures-lean:
	lake build PerfectPower.CauchyBinet PerfectPower.IntegralRecognition PerfectPower.FiniteDomainCertificate
	lake env lean audit/ConnectedClosures.lean
	lake env lean audit/PopulationGenerated.lean
	lake env lean audit/PopulationEdgeCases.lean

connected-closures-receipts:
	$(PY) python/develop_connected_closures.py --periods

.PHONY: native-bridges-lean native-bridges-receipts
native-bridges-receipts:
	$(PY) python/develop_native_bridges.py

native-bridges-lean:
	lake build PerfectPower.NativeRationalRoots PerfectPower.EllipticPointDivision PerfectPower.PicardLefschetz PerfectPower.ResiduePopulation
	lake env lean audit/NativeBridges.lean
	lake env lean audit/NativeBridge_rational.lean
	lake env lean audit/NativeBridge_residue.lean
	lake env lean audit/NativeBridge_braid.lean
	lake env lean audit/NativeBridge_torsion.lean

.PHONY: native-halves-receipts native-halves-lean
native-halves-receipts:
	$(PY) python/develop_native_halves.py
native-halves-lean:
	lake build PerfectPower.EllipticPointDivision
	lake env lean audit/NativeHalves.lean

.PHONY: native-halves-refinement-receipts native-halves-refinement-lean
native-halves-refinement-receipts:
	$(PY) python/develop_native_halves_refinement.py
native-halves-refinement-lean:
	lake build PerfectPower.EllipticQuarticLifts
	lake env lean audit/NativeHalvesRefinement.lean

.PHONY: power-free-receipts power-free-check
power-free-receipts:
	$(PY) python/develop_power_free_local.py
power-free-check:
	bash scripts/check_power_free_local.sh

.PHONY: check-bounded-residue-patch
check-bounded-residue-patch:
	bash scripts/check_bounded_residue_patch.sh

.PHONY: dresden dresden-test
dresden:
	PYTHONPATH=python $(PY) python/develop_dresden.py
dresden-test:
	PYTHONPATH=python $(PY) -m unittest discover -s python/tests -p 'test_dresden*.py' -v

.PHONY: dresden-deep
dresden-deep:
	PYTHONPATH=python python3 python/develop_deep_dresden.py

.PHONY: dresden-lean
dresden-lean:
	bash scripts/check_dresden_lean.sh

.PHONY: dresden-polynomial
dresden-polynomial:
	PYTHONPATH=python $(PY) python/develop_dresden_polynomial.py
