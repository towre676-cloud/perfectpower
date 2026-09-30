"""Read real committed .seq files or a corpus ZIP without extracting it.
python3 corpus_adapter.py --source ../perfectpower/data/oeis --out receipts/oeis_actual.json
Strict parsing, byte hashes, actual offsets, finite agreement only. Never promotes proofs.
"""
from pathlib import Path
import argparse,zipfile,json,hashlib,sys
sys.path.insert(0,str(Path(__file__).resolve().parent/'src'))
from arithmetic import parse_seq,match_shift
p=argparse.ArgumentParser();p.add_argument('--source',required=True);p.add_argument('--out',required=True);p.add_argument('--max-shift',type=int,default=20);a=p.parse_args()
src=Path(a.source)
if src.is_dir():items=((str(f),f.read_bytes()) for f in sorted(src.rglob('*.seq')))
elif zipfile.is_zipfile(src):
 z=zipfile.ZipFile(src);items=((n,z.read(n)) for n in z.namelist() if n.endswith('.seq'))
else:raise SystemExit('Source must be .seq directory or ZIP containing .seq files')
rows=[];errors=[]
for name,raw in items:
 try:
  e=parse_seq(raw.decode('utf-8'));shifts=match_shift(e,a.max_shift)
  rows.append({**e,'source_member':name,'sha256':hashlib.sha256(raw).hexdigest(),'B_index_shifts':shifts,'status':'finite_term_agreement_only' if shifts else 'no_match_in_tested_family'})
 except (ValueError,UnicodeError) as e:errors.append({'source_member':name,'error':str(e)})
output={'source':str(src),'max_shift':a.max_shift,'entry_count':len(rows),'matching_entries':sum(bool(r['B_index_shifts']) for r in rows),'errors':errors,'entries':rows,'promotion_allowed':False}
dst=Path(a.out);dst.parent.mkdir(parents=True,exist_ok=True);dst.write_text(json.dumps(output,indent=2))
print('Parsed',len(rows),'matched',output['matching_entries'],'errors',len(errors))
