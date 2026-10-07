"""Persist an exact census and every complete dimension packet through level 64."""
import gzip,json,hashlib
from pathlib import Path
from math import gcd
from perfectpower.weil_commutant import certify_commutant,verify_commutant
ROOT=Path(__file__).resolve().parents[1]

def main():
    out=ROOT/'receipts/weil_commutant';out.mkdir(parents=True,exist_ok=True)
    packets={};records=[]
    for n in range(2,65):
        p=certify_commutant(n);assert verify_commutant(p)
        packets[n]=p;records.append({k:p[k] for k in ['level','dimension','allowed_entries','rank_lower_bound','prime','root','rank_work']})
        print(n,p['dimension'],flush=True)
    pairs=[]
    for a in range(2,65):
        for b in range(a+1,65):
            if a*b<=64 and gcd(a,b)==1:
                assert packets[a*b]['dimension']==packets[a]['dimension']*packets[b]['dimension']
                pairs.append({'factors':[a,b],'product':a*b,'dimension':packets[a*b]['dimension']})
    raw=json.dumps({'schema':'pp-weil-census/1','packets':list(packets.values())},separators=(',',':')).encode()
    with (out/'complete_packets.json.gz').open('wb') as stream:
        with gzip.GzipFile(filename='',mode='wb',fileobj=stream,mtime=0) as z:z.write(raw)
    summary={'levels':63,'maximum_level':64,'all_packets_replayed':True,'coprime_pairs':pairs,
      'dimensions':records,'uncompressed_packet_sha256':hashlib.sha256(raw).hexdigest(),
      'prime_power_formulas':'PAPER_PROOF: docs/WEIL_LOCAL_DIMENSION_MONOGRAPH.md; not an all-level Lean theorem',
      'execution_verified':False,'method':'integer cyclotomic basis identities and nonzero prime-field rank minors'}
    (out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print('Exact levels:',len(packets),'all coprime pairs:',len(pairs))
if __name__=='__main__':main()
