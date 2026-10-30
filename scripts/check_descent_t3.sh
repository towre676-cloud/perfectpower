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
import hashlib, json, pathlib, re, subprocess
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
reports = {}
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
    reports[part] = {'declarations': expected, 'axioms': sorted({
        v.strip() for row in rows for v in row.split(',') if v.strip()})}
sources = sorted(pathlib.Path('PerfectPower').glob('Descent*.lean'))
sources += [pathlib.Path('PerfectPower/SquareclassUniqueness.lean'),
            pathlib.Path('PerfectPower/DescentRankBridge.lean'),
            pathlib.Path('PerfectPower/IsogenyIndexBridges.lean'),
            pathlib.Path('PerfectPower/TwoIsogenyPointMap.lean'),
            pathlib.Path('PerfectPower/TwoIsogenyDual.lean')]
receipt = {
    'status': 'lean_kernel_replay_passed',
    'lean_version': subprocess.check_output(['lean','--version'],text=True).strip(),
    'mathlib_commit': subprocess.check_output(
        ['git','-C','.lake/packages/mathlib','rev-parse','HEAD'],text=True).strip(),
    'audits': reports,
    'source_sha256': {str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources},
    'mordell_weil_decomposition_discharged': False,
    'prime_saturation_discharged': False,
    'global_height_bound_discharged': False,
}
pathlib.Path('receipts/descent_t3/lean_audit.json').write_text(
    json.dumps(receipt,indent=2,sort_keys=True)+'\n')
PY
python3 scripts/check_descent_t3.py
