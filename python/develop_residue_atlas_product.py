"""Reproduce factored multi-prime covers and native CRT count certificates."""
from pathlib import Path
import json
from perfectpower.residue_atlas_product import product_packet,verify_product,product_population,product_scan,native_product


def main():
    out=Path(__file__).resolve().parents[1]/'receipts'/'residue_atlas_product';out.mkdir(parents=True,exist_ok=True)
    huge=[[-10**12,10**12],[-10**12,10**12]];small=[[-10,10],[-10,10]]
    cases=[
        ('FactoredTripleParabola',[[1,0,1],[-1,2,0]],[[2,3],[3,2],[5,2]],huge,16),
        ('HorizontalDouble',[[1,1,0],[-1,0,2]],[[2,3],[5,2]],huge,4096),
        ('SingularCusp',[[1,0,2],[-1,3,0]],[[2,3],[3,2]],small,8),
        ('MordellDouble',[[1,0,2],[-1,3,0],[2,0,0]],[[2,3],[3,2]],small,4096),
        ('GlobalObstruction',[[1,0,2],[-1,2,0],[-2,0,0]],[[2,2],[3,2]],huge,8),
        ('LinearMixedCharts',[[2,1,0],[3,0,1],[-1,0,0]],[[2,2],[3,2]],small,8),
    ]
    corpus={}
    for name,terms,factors,bounds,limit in cases:
        packet=product_packet(terms,factors,explicit_limit=limit);assert verify_product(packet)
        population=product_population(packet,bounds);row={'product':packet,'population':population}
        if population['count']<=4096:row['scan']=product_scan(packet,bounds)
        corpus[name]=row
        (out/(name+'.lean')).write_text(native_product(packet,bounds))
    (out/'corpus.json').write_text(json.dumps(corpus,indent=2)+'\n')
    print('6 complete CRT products and native programs')


if __name__=='__main__':main()
