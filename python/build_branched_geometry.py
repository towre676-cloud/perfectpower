"""Attach branching, finite connection matrices and cell models to the atlas."""
import json,hashlib
from collections import Counter
from pathlib import Path
from perfectpower.branched_geometry import profile,faithful_laplacian,cell_surface,cycle_graph,lift_components


def build(output='receipts/branched_geometry',source='receipts/divisor_sum/complete_quartics.json'):
    out=Path(output);out.mkdir(parents=True,exist_ok=True)
    source=Path(source);curves=json.loads(source.read_text())['rows']
    rows=[];patterns={};genera=set()
    for i,curve in enumerate(curves):
        for d in (2,3,4,6):
            p=profile(curve['coefficients'],d);genera.add(p['genus_per_component'])
            key=(d,tuple(p['root_multiplicities']))
            patterns.setdefault(key,p)
            names=('power','components','component_cover_degree','genus_per_component',
                   'euler_per_component','euler_total','root_multiplicities',
                   'finite_ramification_per_component','infinity_ramification_per_component',
                   'complex_polynomial_power','signed_content','integer_polynomial_root')
            rows.append({'curve_index':i,**{k:p[k] for k in names}})
    source_hash=hashlib.sha256(source.read_bytes()).hexdigest()
    (out/'quartic_topology.json').write_text(json.dumps({'source_sha256':source_hash,'rows':rows,
        'execution_verified':False,'scope':'classical normalization invariants, not new finite-hit bounds'},separators=(',',':'))+'\n')
    connections=[]
    for (d,labels),p in sorted(patterns.items()):
        s=faithful_laplacian(labels,d);n,edges=cycle_graph(labels,d)
        actual=len(lift_components(n,edges,d))
        if actual!=p['components']:raise AssertionError('normalized components disagree with sheet graph')
        connections.append({'power':d,'root_multiplicities':labels,'normalized_components':actual,**s})
    (out/'connections.json').write_text(json.dumps(connections,separators=(',',':'))+'\n')
    examples=[]
    for name,f,d in (
        ('genus_two',[0,-1,0,0,0,1],2),('genus_three',[-1,0,0,0,0,0,0,1],2),
        ('split_square',[1,-2,1],2),('content_obstruction',[2,-4,2],2),
        ('two_cuspidal_components',[0,0,0,0,0,0,1],4),
        ('integer_square_root',[1,4,4],2),('negative_even_content',[-1],2),
        ('negative_odd_content',[-8],3),('rational_conic',[1,0,1],2),('pell_conic',[1,0,2],2)):
        p=profile(f,d);s=faithful_laplacian(p['root_multiplicities'],d)
        examples.append({'name':name,'profile':p,'connection':s});genera.add(p['genus_per_component'])
    (out/'examples.json').write_text(json.dumps(examples,separators=(',',':'))+'\n')
    models=[cell_surface(g) for g in sorted(genera)]
    (out/'cell_models.json').write_text(json.dumps(models,separators=(',',':'),default=str)+'\n')
    lean=['import PerfectPower.BranchedGeometry','namespace PerfectPower.Generated.GeometryCells',
          'set_option maxRecDepth 100000','set_option maxHeartbeats 0']
    def matrix(rows):
        return '!['+','.join('!['+','.join(map(str,r))+']' for r in rows)+']'
    for p in models:
        g=p['genus'];v,e,f=p['vertices'],p['edges'],p['faces']
        lean += [f'def boundary1_{g} : Matrix (Fin {v}) (Fin {e}) ℚ := {matrix(p["boundary1"])}',
                 f'def boundary2_{g} : Matrix (Fin {e}) (Fin {f}) ℚ := {matrix(p["boundary2"])}',
                 f'theorem chain_{g} : boundary1_{g}*boundary2_{g}=0 := by decide +kernel',
                 f'theorem charge_{g} : ({sum(6-q for q in p["dual_face_sizes"])} : ℤ)=6*({v}-{e}+{f}) := by norm_num',
                 f'#print axioms chain_{g}',f'#print axioms charge_{g}']
    lean.append('end PerfectPower.Generated.GeometryCells')
    (out/'GeometryCells.lean').write_text('\n'.join(lean)+'\n')
    summary={'topology_rows':len(rows),'source_quartics':len(curves),'powers':[2,3,4,6],
        'unique_monodromy_patterns':len(patterns),'exact_connection_matrices':len(connections),
        'cell_model_genera':sorted(genera),'examples':len(examples),
        'genus_distribution':dict(Counter(str(r['genus_per_component']) for r in rows)),
        'complex_power_rows':sum(r['complex_polynomial_power'] for r in rows),
        'integer_root_rows':sum(r['integer_polynomial_root'] is not None for r in rows),
        'source_sha256':source_hash,'execution_verified':False,
        'scope':'topology and finite exact matrices; no intrinsic Voronoi construction, periods or new arithmetic height theorem'}
    (out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    return summary

if __name__=='__main__':print(json.dumps(build(),indent=2))
