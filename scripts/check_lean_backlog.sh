#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p .lake/build/lib/lean/PerfectPower receipts/lean_backlog
for module in PositiveGeometry HolomorphicArithmetic PeriodNormalization MonomialConsequences ConnectionDeterminant LegendreBounds; do
  lake env lean "PerfectPower/$module.lean" -o ".lake/build/lib/lean/PerfectPower/$module.olean"
done
lake env lean audit/LeanBacklog.lean > receipts/lean_backlog/axioms.log
python3 python/build_lean_backlog_packets.py
lake env lean -s 65536 receipts/lean_backlog/ArithmeticPackets.lean > receipts/lean_backlog/packets.log
bash scripts/check_quartic_cutoff.sh
python3 - <<'PY'
import hashlib,json,re
from pathlib import Path
logs=['receipts/lean_backlog/axioms.log','receipts/lean_backlog/packets.log','receipts/lean_backlog/quartic_axioms.log']
counts=[]
for p in logs:
    s=Path(p).read_text()
    groups=re.findall(r'depends on axioms: \[([^\]]*)\]',s)
    assert groups and 'error:' not in s and 'sorryAx' not in s
    for group in groups:
        assert not ({x.strip() for x in group.split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'})
    counts.append(len(groups))
assert counts == [31,21,5], counts
paths=[str(p) for p in Path('PerfectPower').glob('*.lean') if p.stem in
       ['PositiveGeometry','HolomorphicArithmetic','PeriodNormalization','MonomialConsequences','ConnectionDeterminant','LegendreBounds','QuarticCutoff']]
paths += ['audit/LeanBacklog.lean','scripts/check_lean_backlog.sh','python/build_lean_backlog_packets.py',
          'receipts/lean_backlog/ArithmeticPackets.lean','PerfectPower/Tactic/SquareLeadingQuartic.lean',
          'audit/QuarticCutoff.lean','scripts/check_quartic_cutoff.sh']
r={'status':'passed','audited_declarations':sum(counts),'log_report_counts':counts,
   'source_sha256':{p:hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in paths},
   'log_sha256':{p:hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in logs},
   'packet_input_receipt':'receipts/lean_backlog/packet_inputs.json',
   'scope':'Seven new modules and their audits; analytic interpretations and the full heavy root build are separate.'}
Path('receipts/lean_backlog/validation.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({'status':r['status'],'audited_declarations':r['audited_declarations']}))
PY
