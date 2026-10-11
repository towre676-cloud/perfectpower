#!/usr/bin/env python3
"""Independent subset and aligned-string audits of retained benchmark results."""
import gzip,json,sys
from pathlib import Path
from itertools import combinations
from collections import defaultdict,Counter
from hashlib import sha256
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'python'))
from perfectpower.blast_io import tabular,replay
from perfectpower.blast_benchmark import load_dataset,residue_pairs,stream_hits
OUT=ROOT/'receipts/blast/oxbench';DATA=ROOT/'data/oxbench'
def main():
    manifest,records,groups,refs,mapping=load_dataset(DATA);checks=[]
    for task in ('blastp','blastp-fast'):
        hits=stream_hits(DATA/(task+'.tsv.xz'));hit_count=0
        family={k:g for g,ids in groups.items() for k in ids}
        pairs=defaultdict(list)
        for h in hits:
            f=h.fields;hit_count+=1
            if family[f['qseqid']]==family[f['sseqid']] and f['qseqid']!=f['sseqid']:pairs[f['qseqid'],f['sseqid']].append(h)
            aligned=replay(h,records[f['qseqid']],records[f['sseqid']],nucleotide=False)
            q,s=f['qstart'],f['sstart'];decoded=set()
            for a,b in zip(aligned['query'],aligned['subject']):
                if a!='-' and b!='-':decoded.add((q,s))
                q+=a!='-';s+=b!='-'
            if decoded!=residue_pairs(h):raise AssertionError('independent coordinate decoding')
        result=json.loads(gzip.decompress((OUT/(task+'-evaluation.json.gz')).read_bytes()))
        expected=sum(len(v)*(len(v)-1) for v in groups.values())
        if len(result['pairs'])!=expected:raise AssertionError('missing positive pair')
        if len({(r['query'],r['subject']) for r in result['pairs']})!=expected:raise AssertionError('duplicate positive pair')
        for method,total in result['totals'].items():
            got=sum(r['methods'][method]['retrieved'] is True for r in result['pairs'])
            if got!=total['retrieved_pairs']:raise AssertionError('recall aggregation')
        # Prefer complex populations, include at least one candidate pair per represented family.
        candidates=sorted((r for r in result['pairs'] if 1<=r['hsps']<=12 and r['chain_status']=='complete'),key=lambda r:(-r['hsps'],r['family'],r['query'],r['subject']))
        selected=[];families=set()
        for r in candidates:
            if len(selected)<200 or r['family'] not in families:
                selected.append(r);families.add(r['family'])
        subsets=0
        for row in selected:
            hs=pairs[row['query'],row['subject']];spectrum=Counter();maxcov=0
            for n in range(1,len(hs)+1):
                for subset in combinations(range(len(hs)),n):
                    subsets+=1;ordered=sorted(subset,key=lambda i:hs[i].fields['qstart'])
                    legal=all(hs[a].fields['qend']<hs[b].fields['qstart'] and hs[a].fields['send']<hs[b].fields['sstart'] for a,b in zip(ordered,ordered[1:]))
                    if not legal:continue
                    cov=sum(hs[i].fields['qend']-hs[i].fields['qstart']+1 for i in subset);maxcov=max(maxcov,cov)
                    if cov>=row['threshold_residues']:spectrum[n]+=1
            if str(sum(spectrum.values()))!=row['chain_count'] or [list(v) for v in sorted(spectrum.items())]!=row['length_polynomial']:
                raise AssertionError('exhaustive population disagrees')
            if maxcov!=row['coverage']['exact_chain']:raise AssertionError('coverage optimum disagrees')
        checks.append({'task':task,'source_hsps_independently_decoded':hit_count,'all_positive_pairs_audited':expected,'exhaustive_pairs':len(selected),'exhaustive_families':len(families),'subsets_tested':subsets,'accepted':True})
    receipt={'schema':'pp-oxbench-independent-tests/1','checks':checks,'scope':'independent subset enumeration, aligned-string residue coordinates, carrier and recall totals; not correctness of BLAST heuristic search or annotation truth'}
    (OUT/'independent.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
