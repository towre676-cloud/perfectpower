"""Rebuild complete prime-preimage presentations and joint saturation examples."""
from pathlib import Path
import json
from perfectpower.elliptic_arithmetic import EllipticCurve,encode_point
from perfectpower.elliptic_lattice_presentation import from_preimage,subgroup_index
from perfectpower.elliptic_lattice_verifier import verify_subgroup_presentation,verify_saturation_presentation,verify_subgroup_index

def main():
    out=Path(__file__).resolve().parents[1]/'receipts'/'elliptic_prime_subgroups';out.mkdir(exist_ok=True)
    E=EllipticCurve([-4,1]);P=E.checked([0,1]);Q=E.checked([2,1]);rank1=EllipticCurve([0,0,1,-1,0]);A=rank1.checked([0,0]);summary=[]
    def save(name,packet,check):
        assert check(packet);(out/(name+'.json')).write_text(json.dumps(packet,indent=2)+'\n')
        core=packet.get('preimage',packet.get('presentation',{}).get('preimage'))
        summary.append({'name':name,'schema':packet['schema'],'replayed':True,
            'prime':core['prime'] if core else None,'actual_subgroup_index':packet.get('actual_subgroup_index'),
            'status':packet.get('saturation',{}).get('status'),
            'root_nodes':core['root_nodes'] if core else packet.get('saturation',{}).get('root_nodes')})
    for p in (5,7):
        c=E.subgroup_presentation([E.add(P,Q),E.add(E.mul(P,p-1),E.neg(Q))],p)
        save('hidden_'+str(p),c,verify_subgroup_presentation)
        save('hidden_'+str(p)+'_actual_index',subgroup_index(c,[P,Q],[[1,1],[p-1,-1]],[[1,0],[p-1,-1]]),verify_subgroup_index)
        save('dependent_'+str(p),rank1.subgroup_presentation([A,A],p),verify_subgroup_presentation)
        save('recover_'+str(p),rank1.subgroup_presentation([rank1.mul(A,p)],p),verify_subgroup_presentation)
    for p,E,count in [(5,EllipticCurve([0,-1,1,0,0]),5),(7,EllipticCurve([1,-1,1,-3,3]),7)]:
        c=E.subgroup_presentation([],p);assert len(c['preimage']['kernel_fibre']['points'])==count
        save('torsion_kernel_'+str(p),c,verify_subgroup_presentation)
        save('torsion_closed_'+str(p),E.saturation_presentation([],primes=[p],coefficient_bound=4),verify_saturation_presentation)
    s=rank1.saturation_presentation([rank1.mul(A,35)]);save('mixed_35_closed',s,verify_saturation_presentation)
    indices=[]
    for j,(stage,(a,b)) in enumerate(zip(s['saturation']['stages'],[(35,7),(7,7),(7,1),(1,1),(1,1)])):
        packet=subgroup_index(from_preimage(stage['preimage']),[A],[[a]],[[b]])
        save('mixed_35_stage_'+str(j)+'_index',packet,verify_subgroup_index);indices.append(packet['actual_subgroup_index'])
    assert indices==[5,1,7,1,1]
    save('mixed_35_step_limit',rank1.saturation_presentation([rank1.mul(A,35)],max_steps=1),verify_saturation_presentation)
    save('membership_inconclusive',rank1.saturation_presentation([A],max_steps=1,coefficient_bound=0),verify_saturation_presentation)
    (out/'summary.json').write_text(json.dumps({'cases':summary,'actual_joint_stage_indices':indices,
      'all_replayed':True,'complete_mordell_weil_group':False,'lean_execution':False},indent=2)+'\n')
    print(json.dumps({'packets':len(summary),'stage_indices':indices,'all_replayed':True}))

if __name__=='__main__':main()
