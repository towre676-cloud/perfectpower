"""Rebuild deeper monograph mechanisms against actual stored arithmetic/graphs.

Six arithmetic receipts plus five development receipts are deterministic.
Optional timing lives in a separate benchmark receipt.
"""
import argparse
import hashlib
import json
from fractions import Fraction as Q
from itertools import combinations
from math import comb
from pathlib import Path
from time import perf_counter
from enhance_machinery import build as build_arithmetic
from perfectpower import polyalg as P
from perfectpower.sturm_fibres import root_certificate,verify_roots,square_fibres,verify_square_fibres
from perfectpower.arithmetic_engine import ArithmeticEngine,verify_result
from perfectpower.compiler import PowerConstraint,compile_constraint
from perfectpower.connection_polytope import ConnectionGraph
from perfectpower.connection_measure import ConnectionMeasure,verify_measure,verify_conditioning
from perfectpower.deep_recovery_cli import exact_json
from perfectpower.operator_algebra import algebra_profile,verify_profile
from perfectpower.recurrence import Recurrence
from perfectpower.recurrence_identity import companion

ROOT=Path(__file__).resolve().parents[1]


def build(output,benchmark=False):
    out=Path(output);out.mkdir(parents=True,exist_ok=True);hashes={}
    def read(path):
        text=(ROOT/path).read_text();hashes[path]=hashlib.sha256(text.encode()).hexdigest();return json.loads(text)
    def write(name,value):
        (out/name).write_text(json.dumps(value,sort_keys=True,indent=2,default=exact_json)+'\n')
    started=perf_counter();arithmetic=build_arithmetic(out/'arithmetic');arithmetic_seconds=perf_counter()-started
    previous=read('receipts/enhanced_machinery/summary.json')
    assert arithmetic['queries']==previous['queries'] and arithmetic['point_counts']==previous['point_counts']
    assert arithmetic['surviving_root_checks']<previous['surviving_root_checks']
    n=10**100;f=[n,-n-1,1];fibres=square_fibres(f,1);assert verify_square_fibres(fibres)
    original=tuple(map(int,P.add(P.power(P.poly(f),2),P.ONE)))
    plan=compile_constraint(PowerConstraint(original,2));assert plan.all_hits()==[(1,[-1,1]),(n,[-1,1])]
    repeated=P.mul(P.power(P.poly([-n,1]),3),P.mul(P.poly([1,2]),P.poly([1,0,1])))
    roots=root_certificate(map(int,repeated));assert verify_roots(roots) and roots['roots']==[n]
    exceptional=ArithmeticEngine().solve([-100,1,0,0,1],strict=True);assert verify_result(exceptional)
    difficult=ArithmeticEngine().solve([-199,1,1,1,1],strict=True);assert verify_result(difficult)
    assert difficult['statistics']['interval_size']==85 and difficult['statistics']['candidates_checked']==2
    write('root_and_gap_examples.json',{'giant_square_fibres':fibres,'compiler_method':plan.method,
        'repeated_and_noninteger_roots':roots,'exceptional_fibre':exceptional,'difficult_quartic':difficult,
        'difficult_quartic_previous_interval_width':25587,'scope':'constructed stress cases, complete integer domains and independently replayed Python certificates'})
    old_graphs=read('receipts/positive_geometry/connection_polytopes.json');graphs=[];events=0;terms_checked=0
    started=perf_counter()
    for index,row in enumerate(old_graphs):
        p=row['polytope'];g=ConnectionGraph(p['vertices'],tuple(p['edges']),p['power']);m=ConnectionMeasure(g,p['weights']);receipt=m.receipt()
        assert verify_measure(receipt)
        decode=lambda xs:g.field.element([Q(x) for x in xs])
        assert m.z==decode(p['determinant']);conditioning=None
        if m.kernel is not None:
            assert [m.kernel[i][i] for i in range(len(g.edges))]==[decode(x) for x in p['edge_marginals']]
            terms=[];total=g.field.element(0)
            for term in p['terms']:
                value=decode(term['coefficient'])
                for i in term['edges']:value=value*m.weights[i]
                terms.append((set(term['edges']),value));total=total+value;terms_checked+=1
            assert total==m.z;inv=total.inverse()
            for i,j in combinations(range(len(g.edges)),2):
                for included,excluded in (((i,j),()),((i,),(j,)),((j,),(i,)),((),(i,j))):
                    expected=sum((v for edges,v in terms if set(included)<=edges and not set(excluded)&edges),g.field.element(0))*inv
                    assert m.event(included,excluded)==expected;events+=1
            first=next(i for i in range(len(g.edges)) if m.kernel[i][i]!=g.field.element(0))
            conditioning=m.conditional((first,));assert verify_conditioning(receipt,conditioning)
        graphs.append({'source_row':index,'multiplicities':row['multiplicities'],'measure':receipt,'conditioning':conditioning})
        if index and index%50==0:print(f'Completed {index+1}/{len(old_graphs)} stored connection graphs',flush=True)
    graph_seconds=perf_counter()-started
    write('connection_corpus.json',{'source_rows':len(graphs),'stored_basis_terms_checked':terms_checked,
        'mixed_events_checked_against_stored_basis_expansion':events,'rows':graphs,
        'scope':'all 196 stored exponent/multiplicity connection models; exact graph-basis probabilities, not integer-solution probabilities'})
    vertices=10
    edges=tuple((i,(i+1)%vertices,0) for i in range(vertices))+tuple((i,i,1) for i in range(vertices))+tuple((i,(i+3)%vertices,1) for i in range(vertices))+tuple((i,(i+1)%vertices,1) for i in range(vertices))
    large=ConnectionMeasure(ConnectionGraph(vertices,edges,2));receipt=large.receipt();assert verify_measure(receipt)
    conditioned=large.conditional((0,),(10,));assert verify_conditioning(receipt,conditioned)
    write('large_connection.json',{'measure':receipt,'conditioning':conditioned,'candidate_maximal_minor_subsets':comb(len(edges),vertices),
        'basis_enumerations':0,'scope':'constructed 10-vertex 40-edge stress graph; candidate subsets are not a counted number of nonzero bases'})
    models=read('receipts/sequence_recovery/results.json')['oeis_scan']['candidates'];operator_rows=[]
    for row in models:
        model=Recurrence(tuple(map(Q,row['coefficients'])),tuple(map(Q,row['initial'])))
        profile=algebra_profile([companion(model)]);assert verify_profile(profile)
        assert profile['algebra']['dimension']==row['order'] and profile['status']=='DOUBLE_COMMUTANT_CLOSED'
        operator_rows.append({'id':row['id'],'source_sha256':row['sha256'],'profile':profile})
    field=read('receipts/operator_recovery/field756.json');field_profile=algebra_profile([[[Q(x) for x in line] for line in a] for a in field['unit_matrices']])
    assert verify_profile(field_profile) and field_profile['algebra']['dimension']==3
    examples=[]
    for name,operators in [('full two-by-two matrix algebra',[[[0,1],[0,0]],[[0,0],[1,0]]]),
        ('upper triangular double-commutant obstruction',[[[1,0],[0,0]],[[0,1],[0,0]]]),
        ('square-zero algebra: double commutant closed, not semisimple',[[[0,1],[0,0]]])]:
        profile=algebra_profile(operators);assert verify_profile(profile);examples.append({'name':name,'profile':profile})
    write('operator_algebras.json',{'recurrence_models':len(operator_rows),'rows':operator_rows,'field756_unit_profile':field_profile,
        'examples':examples,'scope':'algebras of 135 supplied recurrence models and actual stored unit matrices; no OEIS-definition, semisimplicity, global exponent-bound or ring-isomorphism proof'})
    summary={'source_sha256':hashes,'arithmetic_queries':arithmetic['queries'],
        'point_counts':arithmetic['point_counts'],'previous_root_checks':previous['surviving_root_checks'],
        'new_root_checks':arithmetic['surviving_root_checks'],'previous_leaf_positions':previous['summed_leaf_interval_widths'],
        'new_leaf_positions':arithmetic['summed_leaf_interval_widths'],'giant_fibre_work':fibres['work_used'],
        'root_coordinate_digits':len(str(n)),'connection_corpus_rows':len(graphs),'stored_basis_terms_checked':terms_checked,
        'mixed_events_checked':events,'large_graph_candidate_subsets':comb(len(edges),vertices),'large_graph_basis_enumerations':0,
        'operator_algebra_models':len(operator_rows),'field756_generated_algebra_dimension':field_profile['algebra']['dimension'],
        'all_certificates_replayed':True,'new_lean_compilations':0,'execution_verified':False}
    write('summary.json',summary)
    if benchmark:write('benchmark.json',{'arithmetic_seconds':arithmetic_seconds,'connection_corpus_seconds':graph_seconds,
        'scope':'current-host end-to-end solving and replay; no independent industrial comparison'})
    return summary


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path,default=ROOT/'receipts/monograph_development');parser.add_argument('--benchmark',action='store_true')
    args=parser.parse_args();print(json.dumps(build(args.output,args.benchmark),sort_keys=True,indent=2))
