# Integration record (added in the repository; the package files above are unmodified)

This package came from another session and is kept verbatim. `MANIFEST.json` covers every file
except itself and this note. What the repository did with it:

| item in the package | status here |
|---|---|
| Python kernels, `tests/` (10 tests) | executed; part of `make test` |
| `run.py` receipts (`mordell_scan`, `class_numbers`, `orbit_checks`) | re-run; byte-identical to the shipped receipts |
| Gaussian-unit correction (`i = (-i)^3`) | adopted: `descent.diagnose` now reports `UNIT_BEYOND_PM1` (a limit of the certificate, which assumes units `±1`), with `units.all_cubes = true` for `D = 1`; `docs/OEIS.md` §8 corrected |
| `lean/EffectiveEnumeration.lean` (uncompiled draft, `import Mathlib`) | ported to `PerfectPower/EffectiveEnumeration.lean` with specific imports, compiled, axiom-audited; the exact lift theorem `even_quartic_lift`, the `u = 0` fibre and `even_quartic_complete` were added |
| join `mordell_scan.json` to the 155-curve ledger | done in `python/make_mordell_obstructions.py` → `receipts/mordell_obstructions.json` (`expert_scan_join`): 155 joined, 98 nonempty to `x ≤ 10^5`, 155/155 signed counts equal the published counts; bounded evidence only |
| "the 23 unproved OEIS IDs" | already superseded in this session: the √2 atlas has 28 proved, 3 exceptional-set, 1 transported, 7 unproved (`docs/OEIS.md` §3); Pythagorean predicates are proved (`SqrtTwoBatch.lean`); convergents (A001333) remain open |
| `src/sage_mordell.py` | not executed (no Sage run in this session) |
| `src/experiments.py` (quartic lifts, monomial counts) | receipts shipped; not re-run here |
| Bilu–Tichy monomial counting | not formalized |

No unresolved Mordell curve is closed by this material.
