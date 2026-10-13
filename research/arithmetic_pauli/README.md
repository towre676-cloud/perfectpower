# Height–Pauli arithmetic laboratory

This research package studies exact prime-transition graphs, perfect-power selection rules, height-barrier geodesics, spinor spectra, and effective transport. It does not construct an operator with the Riemann zeros as its spectrum and does not establish a computational advantage over direct perfect-power testing.

Run from this directory with Python 3.10 or later after installing requirements.txt:

```sh
python -m pip install -r requirements.txt
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python research.py --seconds 620
OPENBLAS_NUM_THREADS=1 python selection.py
OPENBLAS_NUM_THREADS=1 python controls.py
python geodesics.py
python ballot.py
python generating.py
python summarize.py
```

On Windows PowerShell set `$env:OPENBLAS_NUM_THREADS='1'` and `$env:OMP_NUM_THREADS='1'` before running the Python commands. Run research.py first: it resets CSV outputs. Run the other programs sequentially for a clean reproduction. summarize.py removes repeated ballot rows by their exact parameter keys. The adaptive matched-control ensemble stops at the requested elapsed duration, so its size varies by hardware; deterministic grids, seeds, and arithmetic calculations are retained.

MONOGRAPH.md states the derived identities, numerical findings, proof boundaries, and next integration target. results/ contains complete CSV observations and JSON computation receipts. Most integer calculations are exact arbitrary-precision computations; Pauli spectra are floating-point; the survival-series calculations use high precision with an analytical truncation bound but are not interval-certified. The subsequent formal push adds 32 generic Lean theorems and 24 literal proofs; see ../../docs/ARITHMETIC_HEIGHT_PAULI_MONOGRAPH.md for their exact scope.
