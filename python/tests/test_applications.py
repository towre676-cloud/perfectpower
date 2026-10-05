import io
import itertools
import json
from pathlib import Path
from fractions import Fraction as Q
import subprocess
import sys
import tempfile
import unittest
from perfectpower.application_objects import SequenceLibrary, InverseDesign, GraphEnsemble, GeometryWorkbench, CombinatorialDesign
from perfectpower.catalogue import Catalogue
from perfectpower.query_service import dispatch, serve
from perfectpower.populations import ExactPopulation
from perfectpower.configuration_tuning import tune, blocked_matmul
from perfectpower.task_protocol import heldout_tasks, public_tasks, evaluate_tasks
from perfectpower.divisor_square import WorkLimit


def domain(lo=1, hi=4, fields=None):
    return dict(kind='domain', predicate={'op':'and','args':[{'poly':[-lo,1],'relation':'>='},{'poly':[-hi,1],'relation':'<='}]}, fields=fields or {'n':[0,1]})


SEQUENCE = dict(operator=[[1,1],[1,0]], seed=[0,1], readouts={'fibonacci':[1,0], 'next':[1,1]})
GRAPH = dict(vertices=1, edges=[[0,0,1]]*3, power=2, weights=[1,2,3])
GEOMETRY = dict(coefficients=[0,-1,0,1], panels={'branch':dict(chart='branch', branch=0, box=['-1/4','1/4','-1/4','1/4'], lower_scale='99/100', upper_scale='103/100', reference_density=4, depth=2)})


class Applications(unittest.TestCase):
    def test_catalogue_restart_content_identity_and_cache(self):
        with tempfile.TemporaryDirectory() as d:
            path = str(Path(d)/'objects.sqlite')
            with Catalogue(path) as c:
                r=c.register('population',domain(), 'layout'); p=c.get('layout')
                self.assertIs(p,c.get(r['id'])); self.assertEqual(c.compilations,1)
                self.assertEqual(c.register('population',domain())['id'],r['id'])
            with Catalogue(path) as c:
                self.assertEqual(c.get('layout').count(),4)
                self.assertEqual(c.definition(r['id'])['kind'],'population')

    def test_alias_replacement_and_atomic_failure(self):
        with Catalogue(':memory:') as c:
            original=c.register('population',domain(),'x')
            with self.assertRaises(ValueError):c.register('population',domain(1,2),'x')
            self.assertEqual(len(c.list()),1)
            c.register('population',domain(1,2),'x',replace=True)
            self.assertEqual(c.get('x').count(),2)
            self.assertEqual(c.get(original['id']).count(),4)
            with self.assertRaises(ValueError):c.register('population',dict(kind='domain'), 'x')

    def test_joins_duplicate_projection_and_budgets(self):
        with Catalogue(':memory:') as c:
            c.register('population',domain(-2,2,{'square':[0,0,1]}),'a')
            c.register('population',domain(-1,1,{'square':[0,0,1]}),'b')
            self.assertEqual(len(c.join('a','b',mode='value',left_field='square',right_field='square')),5)
            self.assertEqual(len(c.join('a','b',start=1,size=10)),2)
            with self.assertRaises(WorkLimit):c.join('a','b',mode='value',row_limit=3)
            c.register('population',domain(1,3,{'constant':[1]}),'c')
            with self.assertRaises(WorkLimit):c.join('c','c',mode='value',left_field='constant',right_field='constant',row_limit=6)

    def test_jsonl_errors_do_not_abort_later_requests(self):
        requests=[dict(op='register',kind='population',specification=domain(),name='x'),
                  dict(op='call',object='x',method='select',args={'rank':2},request_id=3),
                  dict(op='call',object='x',method='__dict__'),dict(op='call',object='x',method='count')]
        source=io.StringIO('bad json\n'+'\n'.join(json.dumps(x) for x in requests)+'\n'); out=io.StringIO()
        with Catalogue(':memory:') as c:serve(c,source,out)
        rows=[json.loads(x) for x in out.getvalue().splitlines()]
        self.assertEqual([r['ok'] for r in rows],[False,True,True,False,True])
        self.assertEqual(rows[2]['request_id'],3);self.assertEqual(rows[2]['result']['parameter'],3)

    def test_oversized_lines_are_drained(self):
        out=io.StringIO()
        with Catalogue(':memory:') as c:serve(c,io.StringIO('x'*100+'\n'+json.dumps({'op':'list'})+'\n'),out,request_byte_limit=25)
        rows=[json.loads(x) for x in out.getvalue().splitlines()]
        self.assertEqual([r['ok'] for r in rows],[False,True])

    def test_service_cli_persistence(self):
        with tempfile.TemporaryDirectory() as d:
            cmd=[sys.executable,'-m','perfectpower','service','--database',str(Path(d)/'db')]
            r=subprocess.run(cmd,input=json.dumps(dict(op='register',kind='population',specification=domain(),name='x'))+'\n',text=True,capture_output=True,check=True)
            self.assertTrue(json.loads(r.stdout)['ok'])
            r=subprocess.run(cmd,input=json.dumps(dict(op='call',object='x',method='count'))+'\n',text=True,capture_output=True,check=True)
            self.assertEqual(json.loads(r.stdout)['result'],4)

    def test_restriction_registers_new_identity(self):
        with Catalogue(':memory:') as c:
            c.register('population',domain(),'x')
            r=dispatch(c,dict(op='restrict',object='x',predicate={'poly':[-2,1],'relation':'>='},name='y'))
            self.assertEqual(c.get(r['id']).count(),3);self.assertEqual(c.get('x').count(),4)

    def test_sequence_values_independent_iteration(self):
        s=SequenceLibrary(SEQUENCE);a,b=0,1
        for n in range(20):
            self.assertEqual(s.terms(n),dict(fibonacci=a,next=a+b))
            self.assertEqual(s.terms(n,modulus=6),dict(fibonacci=a%6,next=(a+b)%6))
            a,b=a+b,a
        a,b=0,1;orbit=[]
        while not orbit or (a,b)!=(0,1):
            orbit.append(a);a,b=(a+b)%17,a
        self.assertEqual(s.terms(10**15,modulus=17)['fibonacci'],orbit[10**15%len(orbit)])

    def test_sequence_laws_subsequence_and_experiments(self):
        from perfectpower.witness_resolvent import resolvent_value
        s=SequenceLibrary(SEQUENCE)
        self.assertEqual(s.compare(s,'fibonacci','fibonacci')['status'],'EQUAL_FOR_ALL_NONNEGATIVE_INDICES')
        self.assertEqual(s.compare(s,'fibonacci','next')['first_index'],0)
        r=s.subsequence(3,2)
        for n in range(12):self.assertEqual(resolvent_value(r,n),s.terms(3+2*n)['fibonacci'])
        result=s.experiment([0,1],[1,0],readout_costs=[8,1])
        self.assertEqual(result['left_value']-result['right_value'], -1)
        self.assertEqual(s.experiment([0,1],[0,1])['status'],'ALL_FUTURE_EQUAL')

    def test_inverse_design_all_ties_against_bruteforce(self):
        from perfectpower.closest_integer import verify_optimum
        design=InverseDesign(dict(matrix=[[1,1,1]],metric=[[2,0,0],[0,1,0],[0,0,3]]))
        for rhs,target in [(2,['1/2','1/2','1/2']),(0,[0,0,0]),(1,['1/3','1/3','1/3'])]:
            result=design.solve([rhs],target); target=list(map(Q,target))
            energy=lambda v:sum(w*(Q(x)-y)**2 for x,y,w in zip(v,target,[2,1,3]))
            points=[v for v in itertools.product(range(-4,5),repeat=3) if sum(v)==rhs];best=min(map(energy,points))
            self.assertEqual(set(result['minimizers']),{v for v in points if energy(v)==best})
            self.assertTrue(verify_optimum(result))
        self.assertEqual(design.optimizer.calls,3)

    def test_inverse_infeasible_integer_observation(self):
        result=InverseDesign(dict(matrix=[[2,4]])).solve([1],[0,0])
        self.assertNotEqual(result['status'],'OPTIMAL_INTEGER_LIFTS');self.assertTrue(result['complete'])

    def test_graph_all_random_draw_paths_exact_distribution(self):
        ensemble=GraphEnsemble(GRAPH)
        class NeedChoice(Exception):
            pass
        class Draws:
            def __init__(self,path):self.path=iter(path)
            def randrange(self,n):
                try:return next(self.path)
                except StopIteration:raise NeedChoice(n)
        masses={}
        def visit(path,weight):
            try:r=ensemble.sample(1,rng=Draws(path))['samples'][0]
            except NeedChoice as e:
                n=e.args[0]
                for choice in range(n):visit(path+[choice],weight/n)
                return
            key=tuple(r['edges']);masses[key]=masses.get(key,Q(0))+weight
        visit([],Q(1))
        self.assertEqual(masses,{(0,):Q(1,6),(1,):Q(2,6),(2,):Q(3,6)})

    def test_graph_conditioning_reweight_and_replay(self):
        from perfectpower.connection_updates import verify_reweight
        ensemble=GraphEnsemble(GRAPH)
        self.assertEqual(ensemble.event([1]),Q(1,3))
        r=ensemble.sample(10,seed=9,excluded=[0])
        self.assertEqual(r,ensemble.sample(10,seed=9,excluded=[0]))
        self.assertTrue(all(0 not in x['edges'] for x in r['samples']))
        derived,p=ensemble.with_weights([0,2,0]);self.assertTrue(verify_reweight(p))
        self.assertEqual(derived.sample(1)['samples'][0]['edges'],[1])
        with self.assertRaises(ValueError):ensemble.with_weights([0,0,0])
        self.assertEqual(ensemble.event([1]),Q(1,3))

    def test_graph_rational_orders_and_rejections(self):
        for order in (2,3,4,6):
            graph=GraphEnsemble(dict(GRAPH,power=order))
            self.assertEqual(graph.event([2]),Q(1,2))
            self.assertEqual(len(graph.sample(2)['samples']),2)
        with self.assertRaises(ValueError):GraphEnsemble(dict(GRAPH,power=5))
        with self.assertRaises(ValueError):GraphEnsemble(dict(GRAPH,edges=[[0,0,0]]*3))
        with self.assertRaises(ValueError):GraphEnsemble(GRAPH).sample(1,included=[0,1])
        with self.assertRaises(WorkLimit):GraphEnsemble(dict(vertices=1,edges=[[0,0,1]]*40,power=2)).sample(1)

    def test_multivertex_graph_against_independent_basis_sum(self):
        graph=GraphEnsemble(dict(vertices=2,edges=[[0,1,0],[0,1,1],[0,0,1],[1,1,1]],power=2,weights=[1,2,3,1]))
        g=graph.measure.graph;weights=graph.measure.weights;mass={}
        for edges in itertools.combinations(range(4),2):
            coefficient=graph._rational(g.forest_coefficient(edges))
            mass[edges]=coefficient*__import__('math').prod(weights[i] for i in edges)
        normal=sum(mass.values())
        for edge in range(4):self.assertEqual(graph.event([edge]),sum(v for k,v in mass.items() if edge in k)/normal)
        for r in graph.sample(20,seed=41)['samples']:
            self.assertEqual(Q(r['conditional_probability']),mass[tuple(r['edges'])]/normal)

    def test_geometry_grids_paths_and_html(self):
        g=GeometryWorkbench(GEOMETRY);grid=g.grid('branch',3)
        self.assertEqual(len(grid),9);self.assertEqual(grid[4]['density_interval'],['4','4'])
        self.assertEqual(g.segment('branch',[0,0],[0,0])['squared_path_length_interval'],['0','0'])
        with tempfile.TemporaryDirectory() as d:
            path=Path(d)/'workbench.html';g.write_html(path,3)
            html=path.read_text();payload=html.split('<script id="data" type="application/json">')[1].split('</script>')[0]
            self.assertEqual(len(json.loads(payload)['panels']['branch']['paths']),9)
        with self.assertRaises(ValueError):g.point('branch',[1,0])

    def test_combinatorial_size_workflow(self):
        g=CombinatorialDesign(dict(expression={'kind':'binomial','width':2}))
        r=g.sizes(100000)
        brute=[n for n in range(1,100001) if __import__('math').isqrt(n*(n+1)//2)**2==n*(n+1)//2]
        self.assertEqual(r['filtered_count'],len(brute))
        self.assertEqual([g.select_size(i)['point'][0] for i in range(len(brute))],brute)
        packet=g.gamma(interval=[0,20]);self.assertEqual(packet['bounded']['status'],'COMPLETE')

    def test_tuner_interleaving_reference_and_ties(self):
        p=ExactPopulation(domain());clock_values=iter([x for i in range(12) for x in (i*100,i*100+10)])
        r=tune(p,lambda values:42,42,repeats=2,warmups=1,clock=lambda:next(clock_values))
        self.assertEqual(len(r['winners']),4);self.assertEqual(len(r['ledger']),8)
        self.assertEqual({x['rank'] for x in r['ledger'] if x['round']==0},set(range(4)))
        with self.assertRaises(ValueError):tune(p,lambda values:0,42)
        with self.assertRaises(ValueError):tune(ExactPopulation(domain(1,100)),lambda values:42,42)

    def test_real_matrix_kernel_independent_reference(self):
        a=[[1,2,-3],[0,4,5]];b=[[1,2],[-1,0],[3,4]]
        expected=[[sum(a[i][k]*b[k][j] for k in range(3)) for j in range(2)] for i in range(2)]
        for r,c in itertools.product((1,2,8),(1,3,8)):
            self.assertEqual(blocked_matmul(a,b,r,c),expected)

    def test_task_grouping_no_answer_leak_and_evaluation(self):
        p=ExactPopulation(dict(kind='curve',left=[0,0,2],right=[0,0,0,3],predicate={'expr':'y-150','relation':'<='}))
        packet=heldout_tasks(p,p.cardinality,seed=18)
        seen={}
        for task in packet['tasks']:
            key=task['group_id']
            if key in seen:self.assertEqual(seen[key],task['split'])
            seen[key]=task['split']
        public=public_tasks(packet,'test')
        self.assertTrue(all('answer' not in x and 'record' not in x for x in public))
        predictions={t['task_id']:t['answer'] for t in packet['tasks'] if t['split']=='test'}
        self.assertEqual(evaluate_tasks(packet,predictions)['correct'],len(predictions))
        with self.assertRaises(ValueError):evaluate_tasks(packet,{'invented':{'rank':0}})

    def test_service_all_object_types(self):
        with Catalogue(':memory:') as c:
            for kind,spec,method,args in [('sequence',SEQUENCE,'terms',{'index':10}),
                ('inverse',{'matrix':[[1,1]]},'solve',{'observation':[2],'target':[0,0]}),
                ('graph',GRAPH,'sample',{'size':1}),('geometry',GEOMETRY,'point',{'panel':'branch','point':[0,0]}),
                ('combinatorial',{'expression':{'kind':'binomial','width':2}},'sizes',{'bound':100})]:
                c.register(kind,spec,kind)
                self.assertIsNotNone(dispatch(c,dict(op='call',object=kind,method=method,args=args)))


if __name__=='__main__':unittest.main()
