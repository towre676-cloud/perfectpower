#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
out=receipts/descent_t3
mkdir -p "$out"
lake build PerfectPower.DescentCounting PerfectPower.DescentDeltaLabel 2>&1 | tee "$out/build.log"
for part in Delta Cover Counting; do
  lake env lean "audit/VerifyDescent${part}.lean" 2>&1 | tee "$out/${part}-axioms.log"
done
python3 - <<'PY'
import pathlib, re
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for part in ['Delta','Cover','Counting']:
    audit = pathlib.Path(f'audit/VerifyDescent{part}.lean').read_text()
    log = pathlib.Path(f'receipts/descent_t3/{part}-axioms.log').read_text()
    expected = len(re.findall(r'^#print axioms ', audit, re.M))
    rows = re.findall(r'depends on axioms:\s*\[([^]]*)\]', log)
    assert len(rows) == expected, (part, len(rows), expected)
    for row in rows:
        actual = {v.strip() for v in row.split(',') if v.strip()}
        assert actual <= allowed, (part, actual - allowed)
    print(f'{part}: {expected} declarations passed standard-axiom allowlist')
PY
python3 scripts/check_descent_t3.py
