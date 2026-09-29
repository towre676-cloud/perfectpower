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

## Further Sage computations (`make crosscheck`)

| Script | Receipt | Plain-Python gate (run by `make receipts`) |
|---|---|---|
| `binomial_curves.py` | `receipts/binomial_curves.json`: integral points of $Y^2=X^3+1$ and $Y^2=X^3-36X$ | `check_binomial.py`. It ties the receipt to the Lean hypotheses in `PerfectPower/Binomial.lean` and the Lean hit lists, rescans $\|X\|\le10^6$, and writes `receipts/binomial_gate.json`. |
| `genus1_sage.py 400 3` | `receipts/genus1_crossval.json`: 400 non-monic/shifted cubics and cubes $m^3=$ quadratic, reduced to integral Weierstrass models | `check_genus1.py`. It recomputes each model, re-verifies each stored point and pull-back, reruns the exact sieve scan to $10^6$, and recomputes each label. |
| `mordell_census.py 10000 4` | `data/mordell_census.jsonl` (per curve), CSV, summary | `mordell_census.py --from-jsonl 10000`. It checks the domain (exact key set, unique, sorted) and each row (hash, points, scan, label). |
| `theorem_g_sage.py 8 8 4` | `receipts/theorem_g_check.json`: Singular normalisation genus (every case) and Sage places at infinity (under a per-case alarm), compared with $\chi=d'(1-S)$ | none; the Lean table `profile_table_ok` covers the combinatorial half |

In the genus-one reduction, every integral $(n,m)$ maps to an integral point of the model, with the congruences written in the script's docstring. So pulling back Sage's complete list of model points loses nothing. The gates never rerun Sage. They check that the stored output is internally consistent, matches the Lean statements, and agrees with an exact scan.
