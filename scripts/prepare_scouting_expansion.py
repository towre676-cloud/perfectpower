#!/usr/bin/env python3
"""Build source-only metrics and explicitly matured NFL labels in a private cache."""
import argparse,hashlib,json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'python'))
from perfectpower.scouting_metrics import build_population

def default(x):
    if hasattr(x,'item'):return x.item()
    raise TypeError(type(x).__name__)

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--cache',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--aggregate',type=Path,required=True);a=p.parse_args()
    if ROOT==a.out.resolve() or ROOT in a.out.resolve().parents:p.error('generated player data must stay outside repository')
    a.out.mkdir(parents=True,exist_ok=True);unit,history,audit=build_population(a.cache)
    unit.to_pickle(a.out/'prospects.pkl');history.to_pickle(a.out/'college_history.pkl')
    audit['source_manifest_sha256']=hashlib.sha256((a.cache/'acquisition.json').read_bytes()).hexdigest();audit['protocol_sha256']=hashlib.sha256((ROOT/'docs/SCOUTING_EXPANSION_PROTOCOL.json').read_bytes()).hexdigest();a.aggregate.parent.mkdir(parents=True,exist_ok=True);a.aggregate.write_text(json.dumps(audit,default=default,indent=2)+'\n');print(json.dumps(audit,default=default))
if __name__=='__main__':main()
