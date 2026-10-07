"""Independent full product-modulus census and direct signed-box source scan."""
from pathlib import Path
import json,random
from perfectpower.residue_atlas_product import product_packet,verify_product,product_population,product_scan,product_rank,product_select
from crosscheck_residue_atlas import horner


def main():
    rng=random.Random(20261008);empty=0;cases=120
    for i in range(cases):
        terms=[[rng.choice([-3,-2,-1,1,2,3]),x,y] for x,y in [(0,0),(1,0),(0,1),(2,0),(0,2),(1,1),(3,0)]]
        factors=[[2,1+i%2],[3,1]];packet=product_packet(terms,factors,explicit_limit=1 if i%3==0 else 4096)
        assert verify_product(packet);m=packet['modulus'];terms=packet['terms']
        roots=[[x,y] for x in range(m) for y in range(m) if horner(terms,x,y)%m==0]
        assert len(roots)==packet['combination_count']
        if packet['roots'] is not None:assert packet['roots']==roots
        b=[[-8,9],[-9,8]]
        candidates=[[x,y] for x in range(-8,10) for y in range(-9,9) if horner(terms,x,y)%m==0]
        points=[[x,y] for x in range(-8,10) for y in range(-9,9) if horner(terms,x,y)==0]
        count=product_population(packet,b)['count'];assert count==len(candidates)
        assert product_scan(packet,b)['points']==points
        if count:
            rank=rng.randrange(count);z=product_select(packet,b,rank)
            assert z in candidates and product_rank(packet,b,z)==rank
        empty+=not roots
    receipt={'seed':20261008,'cases':cases,'engine':'independent nested Horner; direct product-modulus square and rectangle enumeration',
             'root_cardinalities_agree':True,'explicit_tables_agree':True,'factored_counts_agree':True,
             'source_scans_agree':True,'rank_select_roundtrips':True,'empty_products':empty}
    out=Path(__file__).resolve().parents[1]/'receipts'/'residue_atlas_product'/'crosscheck.json'
    out.write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))


if __name__=='__main__':main()
