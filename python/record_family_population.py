"""Rebuild original-equation evidence for the broad family release."""
import json
from pathlib import Path
from perfectpower.checked_family_population import family_population_certificate,check_family_population
from perfectpower.checked_pell_family import pell_family_certificate,check_pell_family


def main():
    queries=[{'ranks':[0,1,100],'objective':['pow','y',2]}]
    cases=[('square_positive',family_population_certificate([0,0,1],queries,offset=15),check_family_population),
           ('square_negative',family_population_certificate([0,1],queries,offset=-15),check_family_population),
           ('large_linear',family_population_certificate([3,10**30],queries,family='mordell_minus2'),check_family_population),
           ('large_zero_fibre',family_population_certificate([3,0,0,10**30],queries,family='mordell_minus2'),check_family_population),
           ('minus13',family_population_certificate([16,0,1],queries,family='mordell_minus13'),check_family_population),
           ('minus5_empty',family_population_certificate([0,0,1],queries,family='mordell_minus5'),check_family_population),
           ('descent_empty',family_population_certificate([5,0,1],queries,family='mordell_descent',offset=-9985),check_family_population),
           ('signed_D3',pell_family_certificate(3,100,queries,domain='integer',global_ranks=[4]),check_pell_family),
           ('D13_minimum',pell_family_certificate(13,1000,global_objective=['pow','y',2]),check_pell_family),
           ('large_count_rank1000',pell_family_certificate(2,10**30,global_ranks=[1000],global_objective=['add','x','y']),check_pell_family),
           ('unbounded_D7',pell_family_certificate(7,100,global_objective=['mul',-1,'x']),check_pell_family)]
    records=[]
    for name,packet,check in cases:
        r=check(packet)
        if not r['accepted']:raise RuntimeError(name+': '+str(r))
        records.append(dict(name=name,packet=packet,acceptance=r))
        print(name+': kernel checked',flush=True)
        checkpoint=Path(__file__).resolve().parents[1]/'receipts/family_population_queries.json'
        checkpoint.write_text(json.dumps(dict(schema='pp-family-population-replay/1',complete=False,records=records),indent=2)+'\n')
    out=Path(__file__).resolve().parents[1]/'receipts/family_population_queries.json'
    out.write_text(json.dumps(dict(schema='pp-family-population-replay/1',complete=True,records=records),indent=2)+'\n')


if __name__=='__main__':main()
