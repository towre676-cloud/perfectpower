"""Sequentially check k=22 generated modules, with explicit partial-check receipts."""
import argparse
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser()
parser.add_argument('--limit',type=int,help='check this many chunks; leaves source unproved')
args = parser.parse_args()
if args.limit is not None and args.limit < 1:
    parser.error("limit must be positive")
parts=ROOT/'PerfectPower/Generated/RankOneSources/K22Parts'
chunks=sorted(parts.glob('Chunk*.lean'),key=lambda p:int(p.stem[5:]))
receipt_path=ROOT/'receipts/k22_split.json'
receipt=json.loads(receipt_path.read_text())
if args.limit is None and len(chunks) != receipt['chunk_modules']:
    parser.error('regenerate the complete split with python3 python/rank_one_split.py first')
receipt.pop('failed_module',None)
receipt.update(status='partial kernel check; source not proved',checked_chunks=[])
receipt_path.write_text(json.dumps(receipt,indent=2)+'\n')
files=[parts/'Defs.lean']+chunks[:args.limit]
if args.limit is None: files.append(ROOT/'PerfectPower/Generated/RankOneSources/K22.lean')
for src in files:
    rel=src.relative_to(ROOT)
    out=ROOT/'.lake/build/lib/lean'/rel.with_suffix('.olean')
    out.parent.mkdir(parents=True,exist_ok=True)
    print('CHECK',rel,flush=True)
    result=subprocess.run(['lake','env','lean','-o',str(out),str(rel)],cwd=ROOT)
    if result.returncode:
        receipt['failed_module']=str(rel)
        receipt_path.write_text(json.dumps(receipt,indent=2)+'\n')
        raise SystemExit(result.returncode)
    if src.stem.startswith('Chunk'): receipt['checked_chunks'].append(src.stem)
    receipt_path.write_text(json.dumps(receipt,indent=2)+'\n')
if args.limit is None:
    receipt['status']='all chunks and source theorem kernel checked'
    receipt_path.write_text(json.dumps(receipt,indent=2)+'\n')
