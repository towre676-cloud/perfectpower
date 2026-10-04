"""Compute intrinsic cells, original-curve metrics and closed-cycle periods."""
import json,hashlib,math
from pathlib import Path
from fractions import Fraction as Q
from perfectpower.intrinsic_torus import legendre_torus,legendre_point
from perfectpower.analytic_surface import AnalyticSurface
from perfectpower.conformal_mesh import hyperelliptic_mesh,heat_voronoi


def build(output='receipts/analytic_geometry'):
    import numpy,scipy
    out=Path(output);out.mkdir(parents=True,exist_ok=True)
    tori=[]
    for lam in ('1/10','1/4','1/3','1/2','2/3','3/4','9/10'):
        p=legendre_torus(lam)
        p['curve_sites']=[legendre_point(Q(lam),complex(*s),p['height']) for s in p['sites']]
        assert abs(p['area_partition_residual'])<1e-10
        assert p['topology_diagnostics']['euler']==0 and p['topology_diagnostics']['disk_cell_condition']
        tori.append(p)
    (out/'legendre_intrinsic_voronoi.json').write_text(json.dumps(tori,separators=(',',':'))+'\n')
    surface_specs=[('original_genus_two',[0,-1,0,0,0,1],2),('real_genus_two',[0,4,0,-5,0,1],2),
                   ('genus_three',[-1,0,0,0,0,0,0,1],2),('cyclic_cubic',[-1,0,0,1],3),
                   ('repeated_genus_two',[0,-1,2,-1,0,1,-2,1],2)]
    surfaces=[];cycles=0
    for name,f,d in surface_specs:
        s=AnalyticSurface(f,d);periods=s.pair_periods()
        words=[]
        for i in range(min(len(s.roots)-1,3)):
            word=[i+1,i+2,-i-1,-i-2];a=s.word_period(word,1e-9);b=s.word_period(word,1e-11)
            a['tighter_tolerance_replay']=b
            a['maximum_replay_difference']=max((math.dist(x,y) for x,y in zip(a['period_vector'],b['period_vector'])),default=0.)
            words.append(a)
        cycles+=len(periods)+len(words)
        metrics=[s.metric(x) for x in (.3+.7j,2.7+1.3j,-.4+1.1j) if min(abs(x-a) for a,e in s.roots)>1e-5]
        surfaces.append({'name':name,'coefficients':f,'power':d,'geometry':s.packet['geometry'],
                         'circle_periods':periods,'word_periods':words,'metric_samples':metrics,
                         'branch_metric_charts':[s.branch_metric(i) for i in range(len(s.roots))],
                         'infinity_metric_chart':s.infinity_metric()})
    (out/'analytic_periods_and_metrics.json').write_text(json.dumps(surfaces,separators=(',',':'))+'\n')
    meshes=[];voronois=[]
    for name,f,d in surface_specs[:3]:
        for resolution in (5,6,8,10):
            try:mesh=hyperelliptic_mesh(f,resolution);break
            except ValueError:
                if resolution==10:raise
        mesh['name']=name
        cells=heat_voronoi(mesh,8);cells['name']=name
        assert abs(cells['area_partition_residual'])<1e-9
        meshes.append(mesh);voronois.append(cells)
    (out/'conformal_curve_meshes.json').write_text(json.dumps(meshes,separators=(',',':'))+'\n')
    (out/'higher_genus_intrinsic_voronoi.json').write_text(json.dumps(voronois,separators=(',',':'))+'\n')
    convergence=[]
    for resolution in (4,6,8):
        mesh=hyperelliptic_mesh(surface_specs[0][1],resolution)
        convergence.append({'resolution':resolution,'vertices':mesh['vertices'],'area':mesh['area'],
                            'gauss_bonnet_residual':mesh['gauss_bonnet_residual']})
    (out/'mesh_refinement.json').write_text(json.dumps({'rows':convergence,'scope':'refinement diagnostics, not a certified convergence rate'},indent=2)+'\n')
    summary={'legendre_tori':len(tori),'original_curve_site_inversions':sum(len(t['curve_sites']) for t in tori),
             'cyclic_surfaces':len(surfaces),'closed_period_contours_and_words':cycles,'higher_genus_meshes':len(meshes),
             'higher_genus_voronoi_sites':sum(len(v['sites']) for v in voronois),
             'maximum_curve_site_residual':max(p['relative_equation_residual'] for t in tori for p in t['curve_sites']),
             'maximum_period_replay_difference':max(p['maximum_replay_difference'] for s in surfaces for p in s['word_periods']),
             'numpy_version':numpy.__version__,'scipy_version':scipy.__version__,
             'scope':'rigorously enclosed Legendre lattice; floating torus cells; numerical general periods, conformal metrics and curve-derived heat Voronoi approximations',
             'new_lean_theorems':0}
    (out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');return summary
if __name__=='__main__':print(json.dumps(build(),indent=2))
