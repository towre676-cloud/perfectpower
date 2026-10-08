"""Independent Horner, direct LCM-square and simultaneous signed-box census."""
import json
import random
from math import lcm
from pathlib import Path
from crosscheck_residue_atlas import horner
from perfectpower.residue_atlas_intersection import intersect_atlases as explicit_intersection, intersection_population as explicit_population
from perfectpower.residue_atlas import atlas_packet
from perfectpower.residue_atlas_product import product_packet
from perfectpower.residue_atlas_intersection_factored import (intersect_atlases, verify_intersection,
    intersection_population, intersection_scan, intersection_select, intersection_rank)

def main():
    rng=random.Random(20261008);cases=120;empty=0;checks=0
    for i in range(cases):
        terms=[[[rng.choice([-2,-1,1,2]),x,y] for x,y in [(0,0),(1,0),(0,1),(2,0),(0,2),(1,1)]] for _ in range(2)]
        if i%2:
            inputs=[product_packet(terms[0],[[2,1+i%3],[3,1]]),product_packet(terms[1],[[2,1],[3,2]])]
        else:inputs=[atlas_packet(terms[0],2,1+i%3),atlas_packet(terms[1],2,1+(i+1)%3),atlas_packet(terms[1],3,1)]
        conditions=[]
        for a in inputs:
            for local in a.get('locals',[a]):conditions.append((local['terms'],local['modulus']))
        p=intersect_atlases(inputs,explicit_limit=1 if i%3==0 else 4096);assert verify_intersection(p)
        explicit=explicit_intersection(inputs)
        m=lcm(*(a['modulus'] for a in inputs));assert p['modulus']==m
        assert explicit['modulus']==m and len(explicit['roots'])==p['combination_count']
        def satisfies(x,y):return all(horner(t,x,y)%n==0 for t,n in conditions)
        roots=[[x,y] for x in range(m) for y in range(m) if satisfies(x,y)];checks+=m*m
        assert len(roots)==p['combination_count'] and explicit['roots']==roots
        if p['roots'] is not None:assert roots==p['roots']
        bounds=[[-8,9],[-9,8]]
        candidates=[[x,y] for x in range(-8,10) for y in range(-9,9) if satisfies(x,y)]
        points=[[x,y] for x in range(-8,10) for y in range(-9,9) if all(horner(t,x,y)==0 for t,_ in conditions)]
        count=intersection_population(p,bounds)['count'];assert count==len(candidates)==explicit_population(explicit,bounds)
        assert intersection_scan(p,bounds)['points']==points
        if count:
            rank=rng.randrange(count);z=intersection_select(p,bounds,rank)
            assert z in candidates and intersection_rank(p,bounds,z)==rank
        empty+=not roots
    result={'seed':20261008,'cases':cases,'square_coordinate_checks':checks,'empty_intersections':empty,
      'engine':'independent nested Horner; direct least-common-multiple square and signed rectangle enumeration',
      'existing_explicit_service_agrees':True,'lcm_periods_agree':True,'complete_roots_agree':True,'factored_counts_agree':True,
      'simultaneous_source_scans_agree':True,'rank_select_roundtrips':True}
    out=Path(__file__).resolve().parents[1]/'receipts'/'residue_atlas_intersection_factored'/'crosscheck.json'
    out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))

if __name__=='__main__':main()
