# One-command reproduction.  `make verify` must end green on a fresh checkout.
PY      ?= python3
SAGEPY  ?= sage -python
export PYTHONPATH := python

.PHONY: verify lean audit lint test receipts counts check-clean crosscheck paper

verify: lean audit lint test receipts counts check-clean
	@echo "verify: OK"

lean:
	lake build

audit: lean
	./audit/check_axioms.sh

lint: lean
	lake env lean audit/Lint.lean

test:
	$(PY) -m unittest discover -s python/tests

receipts:
	$(PY) python/make_receipts.py
	$(PY) python/make_atlas_receipts.py
	$(PY) python/make_lean_certificates.py
	$(PY) python/adversarial_runge.py 300
	$(PY) python/pillai_census.py 18 1000
	$(PY) python/make_lean_census.py
	$(PY) python/uniformity.py

counts: audit
	$(PY) python/make_counts.py

# Regenerated files must match the committed ones exactly.
check-clean:
	git diff --exit-code -- receipts/ data/ docs/figures/ PerfectPower/Generated/ README.md audit/axioms_report.txt

# Optional: needs Sage or passagemath (see crosscheck/README.md).
crosscheck:
	$(SAGEPY) crosscheck/cubics_sage.py 12 100000
	$(SAGEPY) crosscheck/mordell_census.py 10000 4

paper:
	cd paper && pdflatex -interaction=nonstopmode perfectpower.tex >/dev/null && pdflatex -interaction=nonstopmode perfectpower.tex >/dev/null && rm -f *.aux *.log *.out
