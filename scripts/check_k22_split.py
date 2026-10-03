"""Sequentially check k=22 generated modules, with explicit partial-check receipts."""
import argparse
import json
import subprocess
import hashlib
import re
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser()
parser.add_argument('--limit',type=int,help='check this many chunks; leaves source unproved')
parser.add_argument('--resume',action='store_true',help='reuse checks only with matching proof-input hashes and existing Lean objects')
args = parser.parse_args()
if args.limit is not None and args.limit < 1:
    parser.error("limit must be positive")
parts=ROOT/'PerfectPower/Generated/RankOneSources/K22Parts'
chunks=sorted(parts.glob('Chunk*.lean'),key=lambda p:int(p.stem[5:]))
receipt_path=ROOT/'receipts/k22_split.json'
receipt=json.loads(receipt_path.read_text())
if args.limit is None and len(chunks) != receipt['chunk_modules']:
    parser.error('regenerate the complete split with python3 python/rank_one_split.py first')
def proof_hash(src):
    seen=set()
    def visit(path):
        if path in seen: return b''
        seen.add(path)
        data=path.read_bytes()
        dependencies=b''
        for module in re.findall(rb'^import (\S+)',data,re.M):
            if module.startswith(b'PerfectPower.'):
                dependencies+=visit(ROOT/(module.decode().replace('.','/')+'.lean'))
        return str(path.relative_to(ROOT)).encode()+b'\0'+data+dependencies
    config=(ROOT/'lean-toolchain').read_bytes()+(ROOT/'lake-manifest.json').read_bytes()
    return hashlib.sha256(config+visit(src)).hexdigest()
previous=receipt.get('checked_proof_inputs',{}) if args.resume else {}
receipt.pop('failed_module',None)
receipt.update(status='partial kernel check; source not proved',checked_chunks=[],checked_proof_inputs={})
receipt_path.write_text(json.dumps(receipt,indent=2)+'\n')
files=[parts/'Defs.lean']
if receipt.get('integer_endpoints'):
    files += [ROOT/'PerfectPower/RankOneIntegerSlab.lean',parts/'IntegerDefs.lean']
files += chunks[:args.limit]
if args.limit is None: files.append(ROOT/'PerfectPower/Generated/RankOneSources/K22.lean')
for src in files:
    rel=src.relative_to(ROOT)
    out=ROOT/'.lake/build/lib/lean'/rel.with_suffix('.olean')
    out.parent.mkdir(parents=True,exist_ok=True)
    fingerprint=proof_hash(src)
    if args.resume and previous.get(src.stem)==fingerprint and out.exists():
        print('REUSE',rel,flush=True)
        if src.stem.startswith('Chunk'):
            receipt['checked_chunks'].append(src.stem)
            receipt['checked_proof_inputs'][src.stem]=fingerprint
        receipt_path.write_text(json.dumps(receipt,indent=2)+'\n')
        continue
    print('CHECK',rel,flush=True)
    before=time.monotonic()
    result=subprocess.run(['lake','env','lean','-o',str(out),str(rel)],cwd=ROOT)
    if result.returncode:
        receipt['failed_module']=str(rel)
        receipt_path.write_text(json.dumps(receipt,indent=2)+'\n')
        raise SystemExit(result.returncode)
    print('PASS',rel,round(time.monotonic()-before,3),flush=True)
    if src.stem.startswith('Chunk'):
        receipt['checked_chunks'].append(src.stem)
        receipt['checked_proof_inputs'][src.stem]=fingerprint
    receipt_path.write_text(json.dumps(receipt,indent=2)+'\n')
if args.limit is None:
    receipt['status']='all chunks and source theorem kernel checked'
    receipt_path.write_text(json.dumps(receipt,indent=2)+'\n')
