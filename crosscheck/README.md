# Independent cross-validation (optional, needs Sage)

`cubics_sage.py` compares the repository's scan of $m^2=n^3+an+b$ ($n\le10^5$) with Sage's `EllipticCurve.integral_points()` for all nonsingular curves with $|a|,|b|\le12$. Sage's routine combines Mordell–Weil generators (mwrank, `proof=True`) with elliptic-logarithm sieving. The result is written to `receipts/cubic_crossval.json`.

```sh
python3 -m venv /opt/sagevenv
/opt/sagevenv/bin/pip install "passagemath-schemes[eclib,pari,flint]" passagemath-symbolics passagemath-repl
PYTHONPATH=python /opt/sagevenv/bin/python crosscheck/cubics_sage.py 12 100000   # about 90 s
```

The receipt was produced with passagemath 10.8.12. Two engine issues arose:

- **A PARI segfault.** PARI's `ellratpoints` segfaults on $(a,b)=(-6,-5)$. The script replaces that step, which lists the integral $x$ in a bounded real interval, with an exact integer scan of the same interval.
- **A rank mwrank cannot prove.** For $(11,2)$, mwrank cannot prove the rank, possibly because of a nontrivial $\text{Sha}[2]$. The rank is then proved by the analytic route: `rank(only_use_mwrank=False, proof=True)` gives rank $0$, which rests on Kolyvagin.

Any row whose rank still cannot be proved is labelled `conditional_on_unproven_rank`, and any engine failure is labelled `scan_only`.

This is an external certificate. The repository does not re-check Sage's Baker bound or its sieve, and Lean plays no part in it.
