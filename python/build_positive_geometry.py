"""Rebuild the exact positive-geometry and degeneration release corpus."""
import argparse
import hashlib
import json
from itertools import combinations
from pathlib import Path
from perfectpower.connection_polytope import root_channel_graph, ConnectionGraph
from perfectpower.degeneration_atlas import (collision_atlas, associahedron, legendre,
    triangle_canonical, descartes_variations, ordered_branch_form, pentagon_collision_chart)
from perfectpower.descartes_orbits import reflect, parabolic_family, orbit_packet
from perfectpower.period_boundary import normalize_periods, residue_contract
from perfectpower.branched_geometry import profile, cell_surface
from perfectpower.core import mul, power


def build(output='receipts/positive_geometry', orbit_stop=10000):
    out=Path(output);out.mkdir(parents=True,exist_ok=True)
    files=[]
    def write(name,data):
        path=out/name
        path.write_text(json.dumps(data,separators=(',',':'),sort_keys=True)+'\n')
        files.append(path)
    collisions=[];patterns={};strata=0
    for d in range(2,9):
        for m in range(2,7):
            packet=collision_atlas([1]*m,d)
            collisions.append(packet);strata+=packet['stratum_count']
            for row in packet['strata']:
                labels=tuple(sorted(row['normalization']['multiplicities']))
                patterns[(d,labels)]=row['normalization']
    write('collision_strata.json',collisions)
    chambers=[associahedron(n) for n in range(4,10)]
    write('associahedra.json',chambers)
    write('canonical_branch_forms.json',{'ordered_examples':[ordered_branch_form(z) for z in (
        ['1/2'],['1/3','2/3'],['1/4','1/2','3/4'])],
        'pentagon_blowup':pentagon_collision_chart('2/5','3/7'),
        'formalized':False})
    metrics=[]
    for genus in range(8):
        model=cell_surface(genus)
        corners=[4]*6 if genus==0 else [3*model['faces']]
        from fractions import Fraction
        defects=[Fraction(2)-Fraction(q,3) for q in corners]
        if sum(defects)!=2*model['euler']:raise AssertionError('Descartes angle defect failed')
        metrics.append({'genus':genus,'vertices':model['vertices'],'edges':model['edges'],
            'faces':model['faces'],'corner_counts':corners,'defects_over_pi':list(map(str,defects)),
            'sum_defects_over_pi':str(sum(defects)),'euler':model['euler'],
            'dual_face_charge':model['dual_face_charge'],'harmonic_dimensions':model['harmonic_dimensions'],
            'scope':'equilateral quotient metric on the topological model; not the original curve metric'})
    write('polyhedral_metrics.json',metrics)
    connections=[]
    for (d,labels),expected in sorted(patterns.items()):
        graph=root_channel_graph(labels,d)
        p=graph.packet()
        if p['positive_support']['lift_components']!=expected['components']:
            raise AssertionError('collision topology and graph covering disagree')
        # Replay independently through the committed squarefree-polynomial module.
        f=(1,)
        for i,r in enumerate(labels):f=mul(f,power((-i,1),r))
        check=profile(f,d)
        if (check['components'],check['genus_per_component'],check['euler_total']) != (
            expected['components'],expected['genus_per_component'],expected['euler_total']):
            raise AssertionError('independent polynomial profile mismatch')
        costs=[1+(i*7)%11 for i in range(len(graph.edges))]
        connections.append({'multiplicities':list(labels),'normalization':expected,
                            'polynomial_profile_replay':{'coefficients':list(map(int,f)),
                                'components':check['components'],'genus_per_component':check['genus_per_component']},
                            'polytope':p,'minimum_cost_basis':graph.minimum_cost_basis(costs)})
    write('connection_polytopes.json',connections)
    source=Path('receipts/branched_geometry/quartic_topology.json')
    if not source.exists():raise FileNotFoundError('committed branched-geometry corpus required')
    source_data=json.loads(source.read_text())
    source_patterns={}
    for row in source_data['rows']:
        key=(row['power'],tuple(row['root_multiplicities']))
        source_patterns.setdefault(key,[]).append(row['curve_index'])
    corpus=[]
    for (d,labels),indices in sorted(source_patterns.items()):
        g=root_channel_graph(labels,d)
        corpus.append({'power':d,'multiplicities':list(labels),'curve_indices':indices,'polytope':g.packet()})
    write('quartic_corpus_connection_index.json',{'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
        'source_rows':len(source_data['rows']),'patterns':corpus,'formalized':False})
    write('legendre.json',[legendre(s,64) for s in ('0','1/7','1/2','6/7','1','2')])
    theta=ConnectionGraph(2,((0,1,0),(0,1,2),(0,1,1)),4)
    write('theta_example.json',{'polytope':theta.packet(),'canonical':triangle_canonical(1,1),
        'loss_cases':[{'weights':w,'packet':theta.packet(w)} for w in ([0,0,0],[1,0,0],[1,1,0],[1,1,1])],
        'minimum_cost':theta.minimum_cost_basis([9,3,2])})
    seeds={(-1,2,2,3)}
    for _ in range(2):seeds.update(reflect(seed,i) for seed in tuple(seeds) for i in range(4))
    families={}
    preferred=parabolic_family()
    families[tuple(preferred['polynomial'])]=((-1,2,2,3),(0,1))
    for seed in sorted(seeds):
        for fixed in combinations(range(4),2):
            f=parabolic_family(seed,fixed)
            families.setdefault(tuple(f['polynomial']),(seed,fixed))
    selected=list(families.items())[:24]
    orbits=[orbit_packet(seed,fixed,orbit_stop,(2,3,4,5,6)) for f,(seed,fixed) in selected]
    write('descartes_orbits.json',orbits)
    write('period_contracts.json',{'residue_examples':[residue_contract([1,-1],g) for g in (0,1,2,3)],
        'obstruction':residue_contract([1,1],2),
        'corrections':[normalize_periods([[1,0],[0,1]],[3,-2]),normalize_periods([[2,1],[1,1]],[3,-2],[1,4])],
        'formalized':False})
    write('root_signs.json',[descartes_variations([0,1,-3,2],a,b) for a,b in ((-1,0),(0,'1/4'),('1/4','3/4'),('3/4',2))])
    write('lean_handoff.json',{
        'schema':'pp-positive-geometry-lean/1','formalized':False,
        'existing_bridge':'PerfectPower/BranchedGeometry.lean supplies previously proved faithful-connection identities',
        'targets':[
            {'name':'descartes_reflection_involution','data':'descartes_orbits.json','statement':'reflect(reflect(b,i),i)=b'},
            {'name':'descartes_quadratic_orbit','data':'descartes_orbits.json','statement':'b_n=u+(v-u-s)*n+s*n^2'},
            {'name':'legendre_formal_period_recurrence','data':'legendre.json','statement':'(n+1)^2*a_(n+1)=(n+1/2)^2*a_n'},
            {'name':'interval_canonical_additivity','statement':'Omega_[a,b]=Omega_[a,c]+Omega_[c,b]'},
            {'name':'theta_determinant','data':'theta_example.json','statement':'det L=4*a*b+2*a*c+2*b*c'},
            {'name':'theta_canonical_jacobian','statement':'J_numerator=16*a*b*c^2*(4*a*b+2*a*c+2*b*c)'},
            {'name':'pentagon_collision_residue','data':'canonical_branch_forms.json','statement':'x=t*u,y=t gives Omega_5=du wedge dt/[u*(1-u)*t*(1-t)]'},
            {'name':'descartes_polyhedral_defect','data':'polyhedral_metrics.json','statement':'sum_v (2-corners_v/3)=2*(V-E+F)'},
            {'name':'association_face_euler','data':'associahedra.json','statement':'sum_k (-1)^k*f_k=1'},
            {'name':'period_correction','data':'period_contracts.json','statement':'M*c=target-candidate'},
            {'name':'cyclotomic_cauchy_binet','data':'connection_polytopes.json','statement':'det(B^*WB)=sum_I conjugate(det B_I)*det B_I*prod_(i in I)w_i'},
            {'name':'support_rank','statement':'rank B=vertices-number_of_balanced_components'},
            {'name':'basis_optimality','statement':'greedy full-rank subset minimizes nonnegative additive edge costs'}],
        'analytic_targets':['normalized-cover Riemann-Hurwitz','real chamber associahedral compactification',
                            'meromorphic residue ambiguity and period normalization','analytic Legendre period equation'],
        'conventions':{'coefficients':'low to high','voltage':'f_target-zeta^r*f_source',
                       'cyclotomic':'Q[z]/Phi_d(z)','stop':'exclusive, starts at index 0',
                       'face_vector':'increasing dimension, includes the full polytope'}})
    summary={'schema':'pp-positive-geometry-release/1','collision_families':len(collisions),
        'labelled_collision_strata':strata,'distinct_collision_patterns':len(connections),
        'connection_bases':sum(x['polytope']['basis_count'] for x in connections),
        'associahedra':len(chambers),'associahedron_faces':sum(len(x['faces']) for x in chambers),
        'chamber_f_vectors':{str(x['marked_points']):x['f_vector'] for x in chambers},
        'quartic_source_rows':len(source_data['rows']),'quartic_monodromy_patterns':len(corpus),
        'descartes_families':len(orbits),'orbit_stop_exclusive':orbit_stop,
        'bounded_curvatures':len(orbits)*orbit_stop,
        'bounded_power_tests':len(orbits)*orbit_stop*5,
        'bounded_power_hits':sum(len(h) for p in orbits for h in p['hits'].values()),
        'formalized_new_results':False,'scope':'exact finite computations and source-backed mathematical formulas'}
    write('summary.json',summary)
    write('manifest.json',{'files':[{'path':p.name,'bytes':p.stat().st_size,
        'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in files]})
    return summary


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',default='receipts/positive_geometry')
    parser.add_argument('--orbit-stop',type=int,default=10000)
    args=parser.parse_args()
    print(json.dumps(build(args.output,args.orbit_stop),indent=2))
