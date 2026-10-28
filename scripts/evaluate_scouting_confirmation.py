#!/usr/bin/env python3
"""Freeze JSON forecasts without outcomes, or score a previously frozen packet."""
import argparse,json,sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'python'))
import pandas as pd
from perfectpower.scouting_confirmation import freeze,score,digest
p=argparse.ArgumentParser(description=__doc__);sub=p.add_subparsers(dest='command',required=True)
f=sub.add_parser('freeze');f.add_argument('--predictions',required=True);f.add_argument('--protocol',required=True);f.add_argument('--lineage',required=True)
s=sub.add_parser('score');s.add_argument('--packet',required=True);s.add_argument('--outcomes',required=True);s.add_argument('--as-of',required=True);s.add_argument('--complete',action='store_true')
for c in (f,s):c.add_argument('--out',required=True)
a=p.parse_args()
if a.command=='freeze':r=freeze(pd.read_json(a.predictions),digest(json.loads(Path(a.protocol).read_text())),json.loads(Path(a.lineage).read_text()))
else:r=score(json.loads(Path(a.packet).read_text()),pd.read_json(a.outcomes),a.as_of,a.complete)
Path(a.out).write_text(json.dumps(r,indent=2,allow_nan=False)+'\n')
