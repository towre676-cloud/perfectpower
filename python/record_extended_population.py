"""Rebuild kernel acceptance evidence for nonlinear global and Pell populations."""
import argparse
import json
from pathlib import Path
from perfectpower.checked_nonlinear_population import nonlinear_population_certificate,check_nonlinear_population
from perfectpower.checked_pell_population import pell_population_certificate,check_pell_population


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'receipts/extended_population_queries.json')
    args=parser.parse_args()
    queries=[{'ranks':[0,1,8],'objective':['pow','y',2]},
             {'condition':['le',1,'x'],'objective':['mul','x','y']}]
    cases=[('quadratic_minus2',nonlinear_population_certificate([2,0,1],queries),check_nonlinear_population),
           ('repeated_quartic',nonlinear_population_certificate([3,0,0,0,1],queries),check_nonlinear_population),
           ('degree32_repeated_fibre',nonlinear_population_certificate([3]+[0]*31+[1],[{'objective':['pow','y',2]}]),check_nonlinear_population),
           ('quadratic_minus4',nonlinear_population_certificate([1,0,1],queries,family='mordell_minus4'),check_nonlinear_population),
           ('empty_fibre',nonlinear_population_certificate([0,0,1],queries),check_nonlinear_population),
           ('positive_domain',nonlinear_population_certificate([1,0,1],queries,family='mordell_minus4',domain='positive'),check_nonlinear_population),
           ('pell_cutoff_and_global_ranks',pell_population_certificate(1000,queries,global_ranks=[0,4,8]),check_pell_population),
           ('pell_large_cutoff_and_max_rank',pell_population_certificate(10**30,[{'ranks':[0,39,40],'objective':['pow','y',2]}],global_ranks=[128]),check_pell_population)]
    records=[]
    for name,packet,check in cases:
        acceptance=check(packet)
        if not acceptance['accepted']:raise RuntimeError(name+': '+str(acceptance))
        records.append(dict(name=name,packet=packet,acceptance=acceptance))
        print(name+': kernel checked',flush=True)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(dict(schema='pp-extended-population-replay/1',records=records),indent=2)+'\n')


if __name__=='__main__':main()
