"""Original Fourier/chirp equation cross-checks beyond the old dense ceiling."""
import argparse,gzip,json,time
from pathlib import Path
from perfectpower.weil_commutant import certify_commutant,verify_commutant
from perfectpower.weil_orbit import closed_form

ROOT=Path(__file__).resolve().parents[1]
LEVELS=(65,72,81,96,100,108,112,121,125,128)


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--refresh',action='store_true');args=parser.parse_args()
    folder=ROOT/'receipts/weil_beyond64';folder.mkdir(exist_ok=True);rows=[];packets=[]
    archive=folder/'packets.json.gz'
    cached={c['level']:c for c in json.loads(gzip.decompress(archive.read_bytes()))}if archive.exists()else{}
    for n in LEVELS:
        path=folder/f'{n}.json';start=time.monotonic()
        p=certify_commutant(n,work_limit=100000000)if args.refresh or (n not in cached and not path.exists())else cached[n]if n in cached else json.loads(path.read_text())
        if p['level']!=n or not verify_commutant(p)or p['dimension']!=closed_form(n):
            raise ArithmeticError('Fourier/chirp and formula dimensions disagree')
        packets.append(p)
        rows.append(dict(level=n,dimension=p['dimension'],allowed_entries=p['allowed_entries'],
                         minor_rank=p['rank_lower_bound'],prime=p['prime'],root=p['root'],
                         rank_work=p['rank_work']))
        print(n,p['dimension'],'seconds',round(time.monotonic()-start,3),flush=True)
    archive.write_bytes(gzip.compress(json.dumps(packets,separators=(',',':')).encode(),mtime=0))
    (folder/'summary.json').write_text(json.dumps(dict(schema='pp-weil-beyond64/1',levels=len(rows),
            maximum_level=128,rows=rows,all_packets_replayed=True,
            method='original Fourier/chirp equations, rational operators and nonzero modular rank minors',
            lean_dimension_proofs=0),indent=2)+'\n')


if __name__=='__main__':main()
