"""Check a construction trace against the literal public OR-Library instance."""
import argparse
import json
from pathlib import Path
import sys
import time
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'python'))
from perfectpower.planning_certificate import verify, digest
from verify_planning_independent import original_cases, bdd_input


def main():
    p=argparse.ArgumentParser()
    p.add_argument('certificate',type=Path)
    p.add_argument('--case',type=int,default=50)
    p.add_argument('--receipt',type=Path)
    args=p.parse_args()
    weights,caps,_,_=original_cases()[args.case]
    _,order=bdd_input(weights,caps)
    rows=[[weights[j][k] for j in order] for k in range(len(caps))]
    start=time.perf_counter()
    result=verify(args.certificate,rows,caps)
    result.update(seconds=time.perf_counter()-start,certificate_sha256=digest(args.certificate),
                  raw_source_sha256=digest(ROOT/'data/planning/mknap1.txt'),order_original_indices=order,
                  checker_sha256=digest(ROOT/'python/perfectpower/planning_certificate.py'))
    if args.receipt:
        args.receipt.parent.mkdir(parents=True,exist_ok=True)
        args.receipt.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
