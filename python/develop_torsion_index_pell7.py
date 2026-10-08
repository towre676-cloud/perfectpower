"""Regenerate worked torsion-aware subgroup and complete Pell receipts."""
import json
from pathlib import Path
from perfectpower.elliptic_arithmetic import EllipticCurve
from perfectpower.elliptic_torsion_index import torsion_subgroup_index,verify_torsion_subgroup_index
from perfectpower.pell7_complete import certificate,verify_certificate


def main():
    target=Path(__file__).resolve().parents[1]/'receipts/torsion_index_pell7';target.mkdir(parents=True,exist_ok=True)
    results=[]
    for curve,p in (([0,-1,1,0,0],5),([1,-1,1,-3,3],7)):
        E=EllipticCurve(curve);c=E.subgroup_presentation([],p);G=[E.checked(P) for P in c['preimage']['generators']];T=G[0]
        coords=[[next(j for j in range(p) if E.mul(T,j)==P)] for P in G]
        result=torsion_subgroup_index(c,[],[T],[p],[],coords)
        assert verify_torsion_subgroup_index(result)
        name=f'empty_to_rational_{p}_kernel.json';(target/name).write_text(json.dumps(result,indent=2)+'\n')
        results.append(dict(file=name,actual_index=result['actual_subgroup_index'],
                            group_invariant_factors=result['generator_lattice']['group_invariant_factors']))
    c=certificate();assert verify_certificate(c);(target/'pell7_complete.json').write_text(json.dumps(c,indent=2)+'\n')
    out=dict(torsion_examples=results,pell_seeds=c['seeds'],execution_verified=False)
    (target/'summary.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))

if __name__=='__main__':main()
