#!/usr/bin/env python3
"""Regenerate the batch explorer and cross-check all complete finite populations.

With --run-blast, explicitly execute installed BLAST+ on the retained multi-
record FASTA. Otherwise replay the retained tabular output without a network.
"""
import argparse
from fractions import Fraction as Q
from hashlib import sha256
import json
from pathlib import Path
import time

from perfectpower.blast_alignment import weights
from perfectpower.blast_client import local_blast
from perfectpower.blast_io import fasta, tabular
from perfectpower.blast_mining import ChainIndex, HSPSelectionPopulation, capacity_assignment, mine, motif_series, motif_values, verify_mining
from perfectpower.blast_mining_report import write_mining_report
from perfectpower.blast_report import json_ready

ROOT = Path(__file__).resolve().parents[1]


def save(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(json_ready(value), sort_keys=True, indent=2)+'\n')


def main():
    parser = argparse.ArgumentParser(); parser.add_argument('--run-blast', action='store_true')
    parser.add_argument('--native-check', action='store_true'); args = parser.parse_args()
    example = ROOT/'examples/blast'; records_path = example/'insulin_family.fasta'
    text = ''.join((example/name).read_text().rstrip()+'\n' for name in ('NM_000207.3.fasta','XM_043971863.1.fasta','NM_008386.4.fasta'))
    records_path.write_text(text)
    hits_path = example/'insulin_family_blast.tsv'
    if args.run_blast:
        receipt = local_blast(records_path, records_path, hits_path)
        # Keep a reproducible command and source hashes without workstation paths.
        receipt['command'] = ['blastn' if Path(x).name == 'blastn' else Path(x).name if x in (str(records_path),str(hits_path)) else x for x in receipt['command']]
        receipt['result_path'] = 'examples/blast/'+hits_path.name
        save(example/'insulin_family_blast.tsv.provenance.json',receipt)
    records = fasta(text); hits = tabular(hits_path.read_text())
    hashes = {'tabular':sha256(hits_path.read_bytes()).hexdigest(), 'query_fasta':sha256(records_path.read_bytes()).hexdigest(), 'subject_fasta':sha256(records_path.read_bytes()).hexdigest()}
    result = mine(hits, records, records, motifs=['ACG','CGT'], minimum_coverage='1/5', source_hashes=hashes)
    verify_mining(result, hits, records, records, source_hashes=hashes)
    save(ROOT/'receipts/blast/mining_v2.json',result)
    exploratory = mine(hits, records, records, maximum_evalue='100', minimum_coverage='0', source_hashes=hashes)
    save(ROOT/'receipts/blast/mining_exploratory.json',exploratory)
    comparisons = []
    for label, collection in [('conservative',result),('permissive',exploratory)]:
      for row in collection['selections']:
        hs = [hits[i] for i in row['hit_indices']]
        expected = sum(r['index']['count'] for r in collection['chains'] if tuple(r['group'][:2]) == tuple(row['pair']))
        assert row['population']['count'] == expected
        comparison = {'view':label,'pair':row['pair'], 'separator_count':expected, 'dag_count':expected}
        if args.native_check:
            with HSPSelectionPopulation(hs,backend='native') as population:
                assert population.count == expected
                for r in sorted({0, expected//2, expected-1}):
                    if r < 0: continue
                    point = population.select(r)
                    with HSPSelectionPopulation(hs) as other:
                        assert other.rank(point) == r
                comparison['native_count'] = population.count
        comparisons.append(comparison)
    flow = capacity_assignment([hits[i] for i in result['retained_hit_indices']], {k:2 for k in records}, query_ids=records)
    save(ROOT/'receipts/blast/mining_crosscheck.json',{'pairs':comparisons,'capacity_assignment':flow, 'scope':'exact counts on retained public candidates; no whole-database recall measurement'})
    series = motif_series(['A','AA'],alphabet='AC',probabilities={'A':'1/3','C':'2/3'})
    save(ROOT/'receipts/blast/motif_overlap_series.json',{'model':series,'values':[motif_values(series,n) for n in (0,3,20,100)], 'large_modular':motif_values(series,10**12,modulus=1000000007)})
    out = ROOT/'web/blast-mining/index.html'; out.parent.mkdir(parents=True,exist_ok=True)
    write_mining_report(result,out)
    write_mining_report(exploratory,out.with_name('permissive.html'))
    print(json.dumps({'records':len(records),'imported_hsps':len(hits),'retained_hsps':len(result['retained_hit_indices']),
                      'exploratory_hsps':len(exploratory['retained_hit_indices']),
                      'pair_counts':comparisons,'report':str(out)},indent=2))


if __name__ == '__main__': main()
