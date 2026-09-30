# One-command reproduction.  `make verify` must end green on a fresh checkout.
PY      ?= python3
SAGEPY  ?= sage -python
export PYTHONPATH := python

.PHONY: verify lean audit lint test cert-audit receipts counts descent-gate fresh oeis check-clean crosscheck fuzz bench paper

verify: lean audit lint test cert-audit receipts counts descent-gate check-clean
	@echo "verify: OK"

lean:
	lake build

audit: lean
	./audit/check_axioms.sh
	lake env lean audit/CertReject.lean

lint: lean
	lake env lean audit/Lint.lean

test:
	$(PY) -m unittest discover -s python/tests
	$(PY) -m unittest discover -s continuation_tests

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
	$(PY) python/make_lean_plans.py
	$(PY) python/constraint_demos.py
	$(PY) python/make_oeis_problems.py
	$(PY) python/make_oeis_atlas.py

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
	git diff --exit-code -- receipts/ certs/ data/ docs/figures/ PerfectPower/Generated/ README.md audit/axioms_report.txt

# Optional: needs Sage or passagemath (see crosscheck/README.md).
crosscheck:
	$(SAGEPY) crosscheck/cubics_sage.py 12 100000
	$(SAGEPY) crosscheck/binomial_curves.py
	PYTHONPATH=python $(SAGEPY) crosscheck/genus1_sage.py 400 3
	$(SAGEPY) crosscheck/theorem_g_sage.py 8 8 4
	$(SAGEPY) crosscheck/mordell_census.py 10000 4

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
