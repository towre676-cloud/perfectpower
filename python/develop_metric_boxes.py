"""Reproduce shared metric/arithmetic certificates and selected kernel exports."""
import hashlib,json
from fractions import Fraction as Q
from pathlib import Path
from perfectpower import bernstein_boxes as B
from perfectpower.metric_boxes import compare,verify,MetricBoxSpace,chart_density
from perfectpower.box_lean import emit_metric,emit_exclusion,emit_certificate
from perfectpower.voronoi_certificate import produce
from perfectpower.voronoi_lean import emit

ROOT=Path(__file__).resolve().parents[1];OUT=ROOT/'receipts/metric_boxes';OUT.mkdir(exist_ok=True)
AUDIT=ROOT/'audit/MetricBoxPackets';AUDIT.mkdir(exist_ok=True)
HEADER='import PerfectPower.BernsteinBoxes\nset_option maxHeartbeats 20000000\nset_option maxRecDepth 100000\nnamespace PerfectPower.MetricBoxExamples\nopen PerfectPower.BernsteinBoxes\n'
manifest=[]
def save(name,packet,source=None,names=None):
    path=OUT/(name+'.json');path.write_text(json.dumps(packet,indent=2)+'\n')
    if source is not None:
        lean=AUDIT/(name+'.lean');lean.write_text(HEADER+source+'\n'+'\n'.join('#print axioms '+n for n in names)+'\nend PerfectPower.MetricBoxExamples\n')
        manifest.append({'file':str(lean.relative_to(ROOT)),'declarations':len(names),'packet':str(path.relative_to(ROOT))})

metrics=[];queries=0
for g in range(1,5):
    coeff=[0,-1]+[0]*(2*g-1)+[1]
    for chart in ['branch','infinity']:
        p=compare(coeff,chart,[-Q(1,4),Q(1,4),-Q(1,4),Q(1,4)],Q(99,100),Q(103,100),4,branch=0 if chart=='branch' else None,depth=2)
        assert p['complete'] and verify(p)
        name=f'genus_{g}_{chart}'
        if g==1 and chart=='branch':source,names=emit_metric('elliptic_branch',p);save('elliptic_branch',p,source,names)
        else:save(name,p)
        space=MetricBoxSpace(p)
        for i in range(5):
            for j in range(5):
                x,y=Q(i-2,8),Q(j-2,8);q=space.point([x,y]);lo,hi=map(Q,q['density_interval'])
                N=B.evaluate(p['chart_data']['numerator'],x,y);D=B.evaluate(p['chart_data']['denominator_modulus_squared'],x,y)
                assert lo*lo<=N*N/D<=hi*hi;queries+=1
        metrics.append({'name':name,'genus':g,'chart':chart,'complete':True,'queries':space.statistics()['queries']})
    branch=chart_density(coeff,'branch',0);infinity=chart_density(coeff,'infinity')
    assert branch['numerator']==infinity['numerator'] and branch['denominator_modulus_squared']==infinity['denominator_modulus_squared']
p=compare([0,-1,0,1],'finite',[2,3,0,Q(1,4)],Q(1,6),Q(1,2),1,depth=2)
assert verify(p) and p['complete'];source,names=emit_metric('elliptic_finite',p);save('elliptic_finite',p,source,names)
F=[(0,2,1),(3,0,-1)];G=[(0,1,1),(1,0,-1),(0,0,-1)]
p=B.compile_system([F,G],[0,1,-10**100,10**100],depth=2);assert B.verify_exclusion(p) and p['excluded']
s,names=emit_exclusion('square_cube_side',p);save('joint_exclusion',p,s,names)
p=B.certify([(2,0,1),(0,2,1),(0,0,Q(1,4))],[-1,1,-1,1],depth=6);assert B.verify(p) and p['complete']
s,names=emit_certificate('adaptive_quadratic',p);save('adaptive',p,s,names)
# The dense genus-two expansion is deliberately superseded by the all-genus theorem.
(AUDIT/'genus_two_branch.lean').unlink(missing_ok=True)
(OUT/'genus_two_branch.json').unlink(missing_ok=True)
complete=0;unresolved=0;checked_points=0;cases=[]
for d in range(2,8):
    for power in range(2,10):
        for a in [1,2,-1]:
            eqs=[[(0,d,1),(power,0,-1)],[(0,1,a),(1,0,-1)]]
            result=B.solve_affine_faces(eqs,[0,1,-10**100,10**100]);assert B.verify_affine_faces(result)
            brute=[[x,y] for x in [0,1] for y in range(-2,3) if all(B.evaluate(p,x,y)==0 for p in eqs)]
            if result['complete']:assert result['models']==brute;complete+=1
            else:unresolved+=1
            checked_points+=10;cases.append({'exponent':d,'power':power,'affine_coefficient':a,'complete':result['complete'],'models':result['models'] if result['complete'] else None})
(OUT/'affine_faces_corpus.json').write_text(json.dumps(cases,indent=2)+'\n')
mesh={'vertices':4,'triangles':[[0,2,1],[0,1,3],[0,3,2],[1,2,3]],'edge_lengths':[[a,b,'1'] for a in range(4) for b in range(a+1,4)]}
packet_source='import PerfectPower.RationalVoronoiPacket\nset_option maxHeartbeats 20000000\nset_option maxRecDepth 100000\nnamespace PerfectPower.KernelVoronoiExamples\nopen PerfectPower.RationalVoronoiPacket\n'
leaves=0;winners=0
for depth in [0,1,2]:
    p=produce(mesh,[0,1],[[0,Q(3,4),0,0]],depth);name='tetrahedron_'+str(depth)
    save(name,{'mesh':mesh,'packet':p});packet_source+=emit(name,mesh,p);leaves+=len(p['pieces']);winners+=sum(p['site'] is not None for p in p['pieces'])
packet_source+='''
def badRadius : Packet := {tetrahedron_2_packet with leaves := tetrahedron_2_packet.leaves.map (fun l => {l with radius := 0})}
theorem reject_bad_radius : accepts tetrahedron_2_mesh badRadius=false := by decide +kernel
#print axioms reject_bad_radius
def badGradient : Packet := {tetrahedron_2_packet with fields := [[0,10,0,0]]}
theorem reject_bad_gradient : accepts tetrahedron_2_mesh badGradient=false := by decide +kernel
#print axioms reject_bad_gradient
end PerfectPower.KernelVoronoiExamples
'''
path=AUDIT/'voronoi_packets.lean';path.write_text(packet_source);manifest.append({'file':str(path.relative_to(ROOT)),'declarations':5})
(OUT/'kernel_manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
summary={'metric_cases':metrics,'metric_point_queries':queries,'affine_face_cases':len(cases),
         'complete_affine_face_cases':complete,'unresolved_affine_face_cases':unresolved,
         'independent_integer_checks':checked_points,'native_voronoi_packets':3,'native_voronoi_leaves':leaves,
         'native_strict_winner_leaves':winners,'global_smooth_distance_comparison':False,
         'uniform_family':'y²=x^(2g+1)-x, all g≥1; ‖t‖²≤1/8, density relative to 4 between (99/100)² and (103/100)²',
         'producer_kernel_flag':False}
(OUT/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary),flush=True)
