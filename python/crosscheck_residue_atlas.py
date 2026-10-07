"""Independent seeded Horner census, full-box counts and source scans."""
from pathlib import Path
import json,random
from perfectpower.residue_atlas import atlas_packet,verify_atlas,atlas_population,atlas_rank,atlas_select,atlas_scan


def horner(terms,x,y):
    degree=max(i for _,i,_ in terms);result=0
    for i in range(degree,-1,-1):
        cs={j:c for c,k,j in terms if k==i};row=0
        for j in range(max(cs,default=0),-1,-1):row=row*y+cs.get(j,0)
        result=result*x+row
    return result


def main():
    rng=random.Random(20261007);cases=120;empty=0;singular=0
    for case in range(cases):
        terms=[[rng.choice([-3,-2,-1,1,2,3]),i,j] for i,j in [(0,0),(1,0),(0,1),(2,0),(0,2),(1,1),(3,0)]]
        p=[2,3,5][case%3];k=1+case%2;packet=atlas_packet(terms,p,k)
        assert verify_atlas(packet)
        terms=packet['terms'];m=packet['modulus']
        expected=[[a,b] for a in range(m) for b in range(m) if horner(terms,a,b)%m==0]
        assert packet['roots']==expected
        bounds=[[-8,9],[-9,8]]
        candidates=[[x,y] for x in range(-8,10) for y in range(-9,9) if horner(terms,x,y)%m==0]
        points=[[x,y] for x in range(-8,10) for y in range(-9,9) if horner(terms,x,y)==0]
        pop=atlas_population(packet,bounds);assert pop['count']==len(candidates)
        assert atlas_scan(packet,bounds)['points']==points
        if pop['count']:
            index=rng.randrange(pop['count']);z=atlas_select(packet,bounds,index)
            assert z in candidates and atlas_rank(packet,bounds,z)==index
        empty+=not expected
        singular+=sum(n['chart']=='singular' for level in packet['levels'] for n in level['nodes'])
    receipt={'seed':20261007,'cases':cases,'engine':'independent nested integer Horner evaluation',
             'complete_root_tables_agree':True,'full_signed_box_counts_agree':True,
             'complete_source_scans_agree':True,'rank_select_roundtrips':True,
             'empty_final_tables':empty,'singular_parent_nodes':singular}
    out=Path(__file__).resolve().parents[1]/'receipts'/'residue_atlas'/'crosscheck.json'
    out.write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))


if __name__=='__main__':main()
