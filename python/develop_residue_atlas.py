"""Reproduce complete bivariate residue atlases and native population proofs."""
from pathlib import Path
import json
from perfectpower.residue_atlas import atlas_packet,verify_atlas,native_atlas,atlas_population,atlas_scan


def main():
    out=Path(__file__).resolve().parents[1]/'receipts'/'residue_atlas';out.mkdir(parents=True,exist_ok=True)
    huge=[[-10**12,10**12],[-10**12,10**12]];small=[[-10,10],[-10,10]]
    cases=[
        ('VerticalParabola',[[1,0,1],[-1,2,0]],5,2,huge),
        ('HorizontalParabola',[[1,1,0],[-1,0,2]],2,4,huge),
        ('SingularCusp',[[1,0,2],[-1,3,0]],2,3,small),
        ('SingularCircle',[[1,2,0],[1,0,2]],2,3,small),
        ('GlobalObstruction',[[1,0,2],[-1,2,0],[-2,0,0]],2,2,huge),
        ('Mordell',[[1,0,2],[-1,3,0],[2,0,0]],3,2,small),
        ('Quartic',[[1,0,2],[-1,4,0]],3,2,small),
    ]
    corpus={}
    for name,terms,p,k,bounds in cases:
        packet=atlas_packet(terms,p,k);assert verify_atlas(packet),name
        population=atlas_population(packet,bounds)
        row={'atlas':packet,'population':population}
        if population['count']<=4096:row['scan']=atlas_scan(packet,bounds)
        corpus[name]=row
        (out/(name+'.lean')).write_text(native_atlas(packet,bounds))
    (out/'corpus.json').write_text(json.dumps(corpus,indent=2)+'\n')
    print('7 complete atlases, native proofs and exact populations')


if __name__=='__main__':main()
