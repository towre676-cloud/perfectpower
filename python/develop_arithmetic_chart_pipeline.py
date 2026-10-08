"""Reproduce rational-power transport, normalized branches and weighted minors."""
import json
from pathlib import Path
from perfectpower.integer_valued_power_charts import *
from perfectpower.branching_residue_patch import *
from perfectpower.unordered_weighted_determinant import *


def main():
    out=Path(__file__).resolve().parents[1]/'receipts'/'arithmetic_chart_pipeline'
    out.mkdir(parents=True,exist_ok=True);summary={}
    cases=[('OddPell',['7/2',0,'1/2'],2,0),('Triangular',[0,'-1/2','1/2'],2,0),
           ('PartialFour',[0,'1/6','1/6'],3,0),('EmptyDomain',['1/2'],2,0)]
    for name,cs,d,k in cases:
        packet=power_charts(cs,d,[[-20,20]]*2,offset=k,explicit_limit=1)
        scan=chart_scan(packet);branches=branch_power_charts(packet,2,3)
        branched_scan=branch_power_scan(branches)
        assert scan['points']==branched_scan['points']
        row={'power_charts':packet,'scan':scan,'branched_scan':branched_scan}
        (out/(name+'.json')).write_text(json.dumps(row,indent=2)+'\n')
        (out/(name+'.lean')).write_text(native_power_charts(packet))
        summary[name]={'charts':len(packet['charts']),'crt_candidates':scan['candidate_count'],
                       'blowup_candidates':branched_scan['candidate_count'],'solutions':len(scan['points'])}
    for name,H in [('Crossing',[[1,1,1]]),('Cusp',[[1,0,2],[-1,3,0]])]:
        packet=branching_patch(H,[[-8,8]]*2,2,3);scan=patch_scan(packet)
        (out/(name+'.json')).write_text(json.dumps({'patch':packet,'scan':scan},indent=2)+'\n')
        (out/(name+'.lean')).write_text(native_branching_patch(packet))
        summary[name]={'nodes':len(packet['nodes']),'leaves':len(packet['leaf_ids']),
                       'switches':packet['chart_switch_count'],'candidates':packet['candidate_count'],
                       'solutions':len(scan['points'])}
    cases=[('SparseWeights',[[0,1,0],[0,0,1]],[[1,1],[1,0],[0,1]],[0,2,3],2),
           ('ThreeByFive',[[1,2,0,-1,1],[0,1,2,1,-2],[1,0,1,2,1]],
            [[1,0,1],[0,1,2],[1,1,0],[2,1,1],[1,-1,2]],[0,1,1,2,3],3),
           ('StructuralZero',[[1,2,3],[2,4,6]],[[1,0],[0,1],[1,1]],[0,2,1],3)]
    for name,C,V,w,q in cases:
        packet=weighted_determinant(C,V,w,q)
        (out/(name+'.json')).write_text(json.dumps(packet,indent=2)+'\n')
        (out/(name+'.lean')).write_text(native_weighted_determinant(packet))
        summary[name]={'subsets':packet['subset_count'],'determinant':packet['determinant'],
                       'divisor':packet['guaranteed_divisor']}
    patch=branching_patch([[1,1,1]],[[-16,16]]*2,2,3)
    i=next(i for i in patch['leaf_ids'] if patch['nodes'][i]['source_residue']==[0,0])
    bridge=chart_determinant(patch,i,[[0,0],[8,0],[0,8]],[[0,0],[1,0],[0,1]])
    (out/'ChartDeterminant.json').write_text(json.dumps(bridge,indent=2)+'\n')
    (out/'ChartDeterminant.lean').write_text(native_weighted_determinant(bridge['weighted_certificate']))
    summary['ChartDeterminant']={'determinant':bridge['weighted_certificate']['determinant'],
                                'divisor':bridge['weighted_certificate']['guaranteed_divisor']}
    (out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))

if __name__=='__main__':main()
