#!/usr/bin/env python3
"""Prepare residual-study private inputs without modifying any donor experiment."""
import argparse,json
from pathlib import Path
import pandas as pd
from run_movement_transfer import extract

def prepare(data,cohort,out):
    unit,receipt=extract(data,cohort,out)
    source=pd.read_pickle(cohort)
    if 'combine_position' not in source:raise ValueError('source Combine position required')
    if source.groupby('nfl_id').combine_position.nunique().max()>1:raise ValueError('inconsistent source position')
    unit['combine_position']=unit.nfl_id.map(source.groupby('nfl_id').combine_position.first())
    unit.to_pickle(out/'players.pkl')
    return receipt

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--data',type=Path,required=True);p.add_argument('--cohort',type=Path,required=True);p.add_argument('--private-out',type=Path,required=True);a=p.parse_args()
    root=Path(__file__).resolve().parents[1]
    if root==a.private_out.resolve() or root in a.private_out.resolve().parents:p.error('private output must be outside repository')
    print(json.dumps(prepare(a.data,a.cohort,a.private_out)))
if __name__=='__main__':main()
