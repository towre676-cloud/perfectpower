"""Rebuild six source-bound intersection receipts and native Lean programs."""
import json
from pathlib import Path
from perfectpower.residue_atlas import atlas_packet
from perfectpower.residue_atlas_product import product_packet
from perfectpower.residue_atlas_intersection_factored import (intersect_atlases, verify_intersection,
    intersection_population, intersection_scan, native_intersection)

PARABOLA=[[1,0,1],[-1,2,0]]
LINE=[[1,0,1],[-1,1,0]]
Y=[[1,0,1]]

def main():
    out=Path(__file__).resolve().parents[1]/'receipts'/'residue_atlas_intersection_factored';out.mkdir(exist_ok=True)
    cases=[
      ('different_sources',[atlas_packet(PARABOLA,2,3),atlas_packet(LINE,2,2)],[[-8,9],[-9,8]],1),
      ('overlapping_products',[product_packet(PARABOLA,[[2,2],[3,1]]),product_packet(LINE,[[2,1],[3,2]])],[[-6,7],[-7,6]],4096),
      ('singular_projection',[atlas_packet([[1,0,2],[-1,2,0]],2,3),atlas_packet([[1,1,0],[1,0,1]],2,2)],[[-8,8],[-8,8]],1),
      ('empty_conflict',[atlas_packet(Y,2,2),atlas_packet([[1,0,1],[-1,0,0]],2,1)],[[-8,8],[-8,8]],1),
      ('enormous_factored',[product_packet(PARABOLA,[[2,3],[3,2],[5,1]],explicit_limit=1),atlas_packet(LINE,2,2)],
         [[-10**40,10**40],[-10**40,10**40]],1),
      ('idempotent_sources',[atlas_packet(PARABOLA,2,2),atlas_packet(PARABOLA,2,1),atlas_packet(PARABOLA,2,2)],[[-5,5],[-5,5]],4096)]
    summary=[]
    for name,inputs,bounds,limit in cases:
        p=intersect_atlases(inputs,explicit_limit=limit);assert verify_intersection(p)
        population=intersection_population(p,bounds)
        data={'name':name,'input_moduli':[a['modulus'] for a in inputs],'packet':p,'population':population}
        if population['count']<=4096:data['scan']=intersection_scan(p,bounds)
        (out/(name+'.json')).write_text(json.dumps(data,indent=2)+'\n')
        (out/(name+'.lean')).write_text(native_intersection(p,bounds))
        summary.append({'name':name,'input_moduli':data['input_moduli'],'intersection_modulus':p['modulus'],
          'local_root_counts':[len(a['roots']) for a in p['locals']], 'combination_count':p['combination_count'],
          'rectangle_population':population['count'],'points':data.get('scan',{}).get('points'),
          'global_obstruction':p['global_obstruction']})
    (out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary))

if __name__=='__main__':main()
