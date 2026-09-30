"""receipts/oeis_problems.json: PerfectPower's side of the OEIS comparison.

For each problem: its orbit, and coordinates of it with terms, an exact recurrence (checked on
the terms), the growth rate, the certified counting constant and the Lean theorems.  Also the
unresolved Mordell curves y^2 = x^3 + k (|k| <= 100) with the points a scan finds: the targets
for which an OEIS entry citing a complete result would be most useful.  No OEIS data is used.

    python3 python/make_oeis_problems.py
"""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'python'))

from perfectpower.oeis import problems, unresolved_mordell  # noqa: E402


def main():
    out = {'problems': problems(), 'unresolved_mordell': unresolved_mordell()}
    path = ROOT / 'receipts' / 'oeis_problems.json'
    path.write_text(json.dumps(out, indent=1, default=str) + '\n')
    n = sum(len(p['coordinates']) for p in out['problems'])
    print(f"{len(out['problems'])} problems, {n} coordinates, "
          f"{len(out['unresolved_mordell'])} unresolved Mordell curves -> {path.relative_to(ROOT)}")


if __name__ == '__main__':
    main()
