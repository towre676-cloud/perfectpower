"""Regenerate complete eleven/thirteen fibres, subgroup and chart receipts."""
import json,gzip
from pathlib import Path
from perfectpower.elliptic_arithmetic import EllipticCurve
from perfectpower.elliptic_prime_division import rational_prime_division,rational_division_general
from perfectpower.elliptic_prime_division_verifier import verify_prime_division,verify_general_division
from perfectpower.elliptic_lattice_verifier import verify_saturation_presentation
from perfectpower.mordell_cover_charts import chart_cover,lift_chart_point,search_cover_box

ROOT=Path(__file__).resolve().parents[1]

def main():
    out=ROOT/'receipts/elliptic_eleven_thirteen';out.mkdir(exist_ok=True)
    E=EllipticCurve([0,0,1,-1,0]);P=E.checked([0,0]);rows=[]
    def save(name,c):
        data=(json.dumps(c,indent=2)+'\n').encode()
        if len(data)>500000:name+='.gz';data=gzip.compress(data,mtime=0)
        (out/name).write_bytes(data);rows.append(dict(file=name,schema=c['schema']))
    for p in (11,13):
        c=rational_prime_division(E,E.mul(P,p),p);assert verify_prime_division(c)
        save(f'division_{p}.json',c)
        c=rational_prime_division(E,None,p,local_obstructions=True);assert verify_prime_division(c)
        save(f'kernel_{p}.json',c)
        c=rational_prime_division(E,P,p,local_obstructions=True);assert verify_prime_division(c)
        save(f'empty_{p}.json',c)
    c=rational_division_general(E,E.mul(P,143),143);assert verify_general_division(c);save('division_143.json',c)
    c=E.saturation_presentation([E.mul(P,143)],primes=[11,13]);assert verify_saturation_presentation(c)
    assert c['saturation']['generators']==[['0','0']];save('saturation_143.json',c)
    C=dict(quartic=['-2','0','0','1'],x_numerator=['0','-2','0','0','1'],y_numerator=['4','0','0','-4','0','0','1'])
    chart=chart_cover(-2,C,[[1,3],[0,1]]);point=lift_chart_point(chart,['0','5'])
    save('translated_cover_chart.json',dict(schema='pp-mordell-cover-chart-example/1',chart=chart,lift=point))
    # Genuine live discovery at height two on the new chart.
    c=search_cover_box(-2,C,matrix=[[1,3],[0,1]],numerator_bound=2,denominator_max=1);assert c['lifts'][0]['mordell_point']==['3','5'];save('live_translated_cover_box.json',c)
    frontier=json.loads((ROOT/'receipts/mordell_frontier.json').read_text())
    summary=dict(schema='pp-elliptic-eleven-thirteen-release/1',worked_packets=rows,
                 supported_primes=[2,3,5,7,11,13],source_generator_limit=4,root_node_limit=100000,
                 sturm_degree_limit=256,prime_division_degrees={'11':121,'13':169},
                 source_to_target_chart_identity=True,
                 backend_rank_determined=frontier['ranks_determined_by_backend_bounds'],
                 matching_point_witnesses=frontier['ranks_with_matching_point_witnesses'],
                 missing_witness_curves=sum(not r['witness_rank_determined'] for r in frontier['remaining']),
                 backend_rank_corrections=len(frontier['backend_census_rank_corrections']),
                 integral_lists_promoted=0,new_lean_theorems=0,execution_verified=False)
    (out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary),flush=True)

if __name__=='__main__':main()
