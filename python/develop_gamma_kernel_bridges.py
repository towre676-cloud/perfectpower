"""Reproduce universal Gamma kernel query receipts against the pinned Mathlib."""
import hashlib
import json
from pathlib import Path
from time import perf_counter

from perfectpower.checked_factorial_unit import unit_certificate, check_unit
from perfectpower.checked_landau import landau_certificate, check_landau

ROOT = Path(__file__).resolve().parents[1]


def main():
    rows = []
    for n, p, depth in [(0,2,1), (37,2,3), (123,3,2), (256,5,2), (10**30,2,2)]:
        packet = unit_certificate(n,p,depth)
        start = perf_counter(); result = check_unit(packet, timeout=120)
        if not result['accepted']:
            raise RuntimeError(result)
        rows.append(dict(kind='factorial_unit',packet=packet,acceptance=result,
                         seconds=perf_counter()-start))
    for a,b in [([],[]), ([2],[1,1]), ([3],[1,2]), ([6],[1,2,3]), ([12,1],[6,4,3])]:
        packet = landau_certificate(a,b)
        start = perf_counter(); result = check_landau(packet, timeout=120)
        if not result['accepted']:
            raise RuntimeError(result)
        rows.append(dict(kind='landau_integrality',packet=packet,acceptance=result,
                         seconds=perf_counter()-start))
    corpus_path = ROOT/'data/gamma_bober52.json'
    corpus = json.loads(corpus_path.read_text())
    proposals = []
    for row in corpus['rows']:
        packet = landau_certificate(row['numerator'],row['denominator'],work_limit=32768)
        proposals.append(dict(table_line=row['table_line'],
                              cells=len(packet['arithmetic']['intervals']),
                              source_sha256=packet['source_sha256'], proof_status='emitted'))
    result = dict(schema='pp-gamma-kernel-bridges/1', queries=rows,
                  independent_corpus_sha256=hashlib.sha256(corpus_path.read_bytes()).hexdigest(),
                  independent_corpus_proposals=proposals,
                  accepted_queries=len(rows), all_52_kernel_checked=False,
                  full_repository_verified=False,
                  scope='21 generic theorems separately audited; ten actual original-equation queries accepted; corpus proposals are unaccepted')
    output = ROOT/'receipts/gamma_kernel_bridges/queries.json'
    output.parent.mkdir(parents=True,exist_ok=True)
    output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(accepted_queries=len(rows), corpus_proposals=len(proposals),
                         all_52_kernel_checked=False)))


if __name__ == '__main__':
    main()
