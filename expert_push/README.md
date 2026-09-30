# PerfectPower expert push — 2026-09-30

Start with CLAUDE_CODE_START_HERE.md. MONOGRAPH.md develops all five requested targets and exact remaining premises. This is an additive package against the reported f7ae11b baseline; it is not an integrated repository release.

Executed work: ten independent unit tests; 200 signed nonsingular Mordell curves through x=100000 inclusive (103 nonempty, 340 signed points); 100 negative order discriminants with reduced forms; 100 continued-fraction checks; 200 orbit norm/doubling checks; five even-quartic models with 22 source points and exact lift checks; 64 monomial counting cases. All receipts are JSON and all experimental kernels use Python's standard library.

Run `python3 -m unittest discover -s tests -v`, `python3 run.py --out receipts`, then `python3 src/experiments.py`. Windows may use `py -3` instead of `python3`. No external data download is required to reproduce these new receipts.

The Gaussian-unit correction is substantive: i=(-i)^3, so all four Gaussian units are cubes. The actual baseline descent failure still needs inspection. The quartic map is degree two, with exact integer-lift filters; it is not birational. Bounded searches do not prove global completeness.

lean/EffectiveEnumeration.lean is an uncompiled draft with an explicit bound-to-list theorem and quartic algebra. src/sage_mordell.py is an unexecuted external algorithm adapter. Neither Lean nor Sage was installed here. The actual 23 OEIS IDs and 155-curve obstruction ledger were unavailable, so no new entry promotion or complete unresolved curve is claimed.

The SHA256 manifest covers package members except itself. ZIP validation and tests completed before delivery. The companion monograph is included inside the ZIP as well as supplied separately for reading.
