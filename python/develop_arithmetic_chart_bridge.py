"""Rebuild the denominator-aware chart and unordered determinant release."""
import json
from pathlib import Path
from perfectpower.rational_power_atlas import (power_atlas,verify_power_atlas,power_population,
    power_scan,power_patch,verify_power_patch,native_power_atlas)
from perfectpower.weighted_gram_determinant import weighted_determinant,verify_weighted_determinant

def main():
    out=Path(__file__).resolve().parents[1]/'receipts'/'arithmetic_chart_bridge';out.mkdir(exist_ok=True)
    cases=[
      ('denominator_prime',['0','1/2'],2,[[2,2]],[[-8,8],[-4,4]],[]),
      ('triangular_square',['0','-1/2','1/2'],2,[[2,2],[3,1]],[[-8,9],[-4,4]],[]),
      ('partial_integer_domain',['0','0','1/4'],2,[[3,1]],[[-6,6],[-3,3]],[]),
      ('three_integral_charts',['0','0','1/9'],2,[[2,2]],[[-6,6],[-2,2]],[]),
      ('shared_partial_domain',['0','1/2'],3,[[2,2],[3,1]],[[-6,9],[-3,3]],[{'terms':[[1,1,0],[1,0,1]],'prime':2,'exponent':2}]),
      ('mixed_branch_cusp',[0,0,0,1],2,[[2,3],[3,2]],[[-5,5],[-5,5]],[]),
      ('empty_integer_domain',['1/2'],2,[[2,1]],[[-3,3],[-3,3]],[]),
      ('enormous_original_rectangle',['0','1/2'],2,[[2,3],[3,2],[5,1]],[[-10**40,10**40],[-10**40,10**40]],[])]
    summary=[]
    for name,coefficients,d,factors,bounds,restrictions in cases:
        atlas=power_atlas(coefficients,d,factors,restrictions=restrictions,explicit_limit=1)
        assert verify_power_atlas(atlas);population=power_population(atlas,bounds)
        record={'name':name,'atlas':atlas,'population':population}
        if population['count']<=4096:
            record['patch']=power_patch(atlas,bounds);assert verify_power_patch(record['patch'])
        (out/(name+'.json')).write_text(json.dumps(record,indent=2)+'\n')
        (out/(name+'.lean')).write_text(native_power_atlas(atlas,bounds))
        summary.append({'name':name,'denominator':atlas['denominator'],'integral_residues':[c['residue'] for c in atlas['charts']],
          'x_period':atlas['x_period'],'y_period':atlas['y_period'],'population':population['count'],
          'points':record.get('patch',{}).get('scan',{}).get('points'),
          'lift_orientations':record.get('patch',{}).get('lift_orientations')})
    matrices=[('real',[[1,0],[0,1],[1,1]],[2,3,5]),
              ('complex',[[1,[0,1]],[[0,1],1],[1,1]],[[1,1],[2,-1],0]),
              ('zero_weights',[[1,0],[0,1],[1,1]],[1,0,2]),
              ('rank_deficient',[[1,2],[2,4]],[1,1])]
    weighted=[]
    for name,B,w in matrices:
        packet=weighted_determinant(B,w);assert verify_weighted_determinant(packet)
        weighted.append({'name':name,'packet':packet})
    (out/'weighted_determinants.json').write_text(json.dumps(weighted,indent=2)+'\n')
    (out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary))

if __name__=='__main__':main()
