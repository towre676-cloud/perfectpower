#!/usr/bin/env bash
set -euo pipefail
PYTHONPATH=python python3 python/develop_native_staged_halves.py
lake build PerfectPower.EllipticPointLaw PerfectPower.TriplingCoordinates \
  PerfectPower.TypedDivisionPackets PerfectPower.PolynomialSourceSemantics \
  PerfectPower.SubgroupDivisionClosure
audit_log=$(mktemp)
trap 'rm -f "$audit_log"' EXIT
lake env lean audit/EllipticBridgesAudit.lean | tee "$audit_log"
lake env lean receipts/elliptic_bridges/TypedRootPacket.lean | tee -a "$audit_log"
lake env lean receipts/elliptic_bridges/TypedHalvesAnchor.lean | tee -a "$audit_log"
lake env lean receipts/elliptic_bridges/TypedHalvesCoset.lean | tee -a "$audit_log"
lake env lean receipts/elliptic_bridges/TypedHalvesNonsquare.lean | tee -a "$audit_log"
lake env lean receipts/elliptic_bridges/NativeStagedHalves.lean | tee -a "$audit_log"
python3 - "$audit_log" <<'PY'
import re,sys
text=open(sys.argv[1]).read()
sets=re.findall(r'depends on axioms:\s*\[([^]]*)\]',text)
assert len(sets)>=14, 'missing theorem audit output'
allowed={'propext','Classical.choice','Quot.sound'}
for values in sets:
    assert {v.strip() for v in values.split(',') if v.strip()}<=allowed, values
assert 'sorryAx' not in text and 'Lean.ofReduceBool' not in text
print('focused axioms: standard only')
PY
PYTHONPATH=python python3 -m unittest discover -s python/tests -p 'test_elliptic_saturation.py'
PYTHONPATH=python python3 -m unittest discover -s python/tests -p 'test_legendre_endpoint.py'
PYTHONPATH=python python3 python/develop_elliptic_bridges.py
