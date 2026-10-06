import copy
import itertools
import json
import math
import random
import shutil
import threading
import unittest
from fractions import Fraction as Q
from urllib.request import Request,urlopen
from urllib.error import HTTPError
from perfectpower.application_objects import GraphEnsemble,SequenceLibrary,InverseDesign,GeometryWorkbench
from perfectpower.cyclotomic_real import pi_interval,real_interval,exact_bernoulli,verify_decision
from perfectpower.bounded_inverse import closest_in_box,verify_bounded_design
from perfectpower.optimal_experiments import cheapest_experiment
from perfectpower.integral_machine import integral_machine
from perfectpower.chart_transitions import certify_transition,verify_transition,transport_point
from perfectpower.task_protocol import heldout_families,public_tasks,solve_public_tasks,evaluate_tasks
from perfectpower.compiled_tuning import CompiledMatmul,compatible_tiles
from perfectpower.flavor_identifiability import stationarity_space,allowed_linear_response
from perfectpower.http_service import QueryHTTPServer
from perfectpower.divisor_square import WorkLimit
from perfectpower.catalogue import encoded
from perfectpower.projected_populations import ProjectedPopulation,symbolic_join
from perfectpower.populations import ExactPopulation
from perfectpower.factorial_library import FactorialLibrary
from perfectpower.configuration_tuning import tune
from perfectpower.catalogue import Catalogue
from perfectpower.query_service import dispatch


class OpenContent(unittest.TestCase):
    def test_constant_projection_empty_domains_and_service_joins(self):
        spec=dict(kind='domain',predicate={'op':'and','args':[{'poly':[2,1],'relation':'>='},{'poly':[-2,1],'relation':'<='}]},fields={'square':[0,0,1],'constant':[5]})
        p=ProjectedPopulation(dict(source=spec,field='constant'))
        self.assertEqual(p.count(),1);self.assertEqual(p.multiplicity(5),5);self.assertEqual(p.select(0)['parameter'],-2)
        empty=ProjectedPopulation(dict(source=dict(spec,predicate=False),field='constant'))
        self.assertEqual(empty.count(),0);self.assertEqual(empty.multiplicity(5),0)
        with Catalogue(':memory:') as c:
            c.register('population',spec,'a');c.register('projected',dict(source=spec,field='square'),'p')
            dispatch(c,dict(op='symbolic_join',object='a',other='a',name='j',args=dict(left_field='square',right_field='square')))
            self.assertEqual(dispatch(c,dict(op='call',object='j',method='count')),9)
            self.assertEqual(dispatch(c,dict(op='call',object='p',method='count')),3)

    def test_factorial_constant_validates_all_inputs(self):
        p=FactorialLibrary(dict(families={'constant':dict(numerator=[],denominator=[])}))
        self.assertEqual(p.residues(10,7,2)['outputs']['constant']['value'],1)
        for index,prime,depth in [(True,7,2),(-1,7,2),(0,4,1),(0,7,0)]:
            with self.assertRaises(ValueError):p.residues(index,prime,depth)

    def test_interleaved_controls_verify_outputs_and_trial_counts(self):
        population=compatible_tiles(max_parameter=2);events=[];ticks=iter(range(100))
        def run(values):events.append('candidate');return 7
        def reference():events.append('baseline');return 7
        result=tune(population,run,7,repeats=3,warmups=1,clock=lambda:next(ticks),comparison=reference,controls={'untiled':reference})
        self.assertEqual(len(result['ledger']),12);self.assertEqual(len(result['comparison']['trials_ns']),3)
        self.assertEqual(len(result['controls']['untiled']['trials_ns']),3)
        self.assertEqual(len(events),16)
        with self.assertRaises(ValueError):tune(population,run,7,comparison=lambda:8)

    def test_factorial_library_true_residues_across_singular_denominators(self):
        library=FactorialLibrary(dict(families={'central':dict(numerator=[2],denominator=[1,1]),'multinomial':dict(numerator=[3],denominator=[1,1,1])}))
        for n in range(24):
            for prime,depth in ((2,4),(3,3),(7,2)):
                packet=library.residues(n,prime,depth)
                self.assertEqual(packet['outputs']['central']['value'],math.comb(2*n,n)%prime**depth)
                self.assertEqual(packet['outputs']['multinomial']['value'],math.factorial(3*n)//math.factorial(n)**3%prime**depth)
                self.assertEqual(packet['unique_factorials'],3)
        self.assertEqual(library.residues(10**100,7,2)['index'],10**100)

    def test_distinct_projection_against_asymmetric_and_modular_domains(self):
        for a,b,c in [(1,0,0),(-2,4,1),(3,1,-7),(0,2,1),(0,0,5)]:
            for lo,hi in [(-7,9),(-8,-1),(0,5)]:
                predicate={'op':'and','args':[{'poly':[-lo,1],'relation':'>='},{'poly':[-hi,1],'relation':'<='},{'poly':[0,1],'modulus':3,'relation':'!=','value':1}]}
                spec=dict(kind='domain',predicate=predicate,fields={'value':[c,b,a]})
                p=ProjectedPopulation(dict(source=spec,field='value'));original=[n for n in range(lo,hi+1) if n%3!=1]
                values={a*n*n+b*n+c for n in original}
                self.assertEqual(p.cardinality,len(values))
                self.assertEqual({r['values']['value'] for r in p.page(0,p.cardinality)},values)
                for value in values:
                    record=p.select(p.locate(value));self.assertEqual(record['parameter'],min(n for n in original if a*n*n+b*n+c==value))
                    self.assertEqual(p.multiplicity(value),sum(a*n*n+b*n+c==value for n in original))

    def test_huge_projection_and_symbolic_join(self):
        bound=10**50;spec=dict(kind='domain',predicate={'op':'and','args':[{'poly':[bound,1],'relation':'>='},{'poly':[-bound,1],'relation':'<='}]},fields={'square':[0,0,1]})
        source=ExactPopulation(spec);projected=ProjectedPopulation(dict(source=spec,field='square'))
        self.assertEqual(projected.count(),bound+1);self.assertEqual(projected.multiplicity(4),2)
        joined=symbolic_join(source,source,'square','square')
        self.assertEqual(joined.count(),4*bound+1)
        for r in joined.sample(20,seed=612):self.assertEqual(r['values']['x']**2,r['values']['y']**2)

    def test_pi_bounds_nested_and_independent_digits(self):
        reference=Q('3.14159265358979323846264338327950288419716939937510')
        old=(Q(3),Q(4))
        for bits in (16,32,64,96):
            lo,hi=pi_interval(bits)
            self.assertLess(lo,reference);self.assertGreater(hi,reference)
            self.assertLess(hi-lo,Q(1,1<<bits));self.assertTrue(old[0]<=lo<hi<=old[1]);old=(lo,hi)

    def test_algebraic_probability_known_sqrt5_embedding(self):
        g=GraphEnsemble(dict(vertices=1,edges=[[0,0,1],[0,0,2]],power=5))
        p=g.measure.event([0]);field=g.measure.field
        self.assertEqual(p*p-p+field.element(Q(1,5)),field.element(0))
        lo,hi=real_interval(p,5,80);scale=10**30;root=math.isqrt(5*scale*scale)
        self.assertLessEqual(lo,(5-Q(root+1,scale))/10)
        self.assertGreaterEqual(hi,(5-Q(root,scale))/10)
        for choice,expected in ((0,True),(1,False)):
            class Draw:
                def randrange(self,n):return choice
            take,receipt=exact_bernoulli(p,5,Draw())
            self.assertEqual(take,expected);self.assertTrue(verify_decision(receipt))
            tampered=copy.deepcopy(receipt);tampered['included']=not take;self.assertFalse(verify_decision(tampered))

    def test_graph_all_supported_orders_replay_decisions(self):
        for order in range(2,65):
            g=GraphEnsemble(dict(vertices=1,edges=[[0,0,1],[0,0,2],[0,0,3]],power=order,weights=[1,2,3]))
            packet=g.sample(2,seed=order)
            self.assertTrue(all(verify_decision(d['comparison']) for s in packet['samples'] for d in s['decisions']))
            self.assertTrue(all(len(s['edges'])==1 for s in packet['samples']))

    def test_algebraic_sampling_budget_returns_no_draw(self):
        g=GraphEnsemble(dict(vertices=1,edges=[[0,0,1],[0,0,2]],power=5))
        class Draw:
            def randrange(self,n):return 0
        with self.assertRaises(WorkLimit):exact_bernoulli(g.measure.event([0]),5,Draw(),bit_limit=1)

    def test_bounded_inverse_random_independent_search(self):
        rng=random.Random(677)
        for _ in range(25):
            target=[Q(rng.randrange(-6,7),2) for _ in range(3)];rhs=rng.randrange(-3,4)
            m=[[2,1,0],[1,3,1],[0,1,2]];constraints=[dict(coefficients=[1,-1,0],relation='>=',rhs=rng.randrange(-2,3))]
            packet=closest_in_box([[1,1,1]],[rhs],target,[-3]*3,[3]*3,m,constraints)
            candidates=[v for v in itertools.product(range(-3,4),repeat=3) if sum(v)==rhs and v[0]-v[1]>=constraints[0]['rhs']]
            def energy(v):
                delta=[Q(a)-b for a,b in zip(v,target)]
                return sum(delta[i]*m[i][j]*delta[j] for i in range(3) for j in range(3))
            best=min(map(energy,candidates)) if candidates else None
            self.assertEqual(packet['minimum_energy'],best)
            self.assertEqual(set(packet['minimizers']),{v for v in candidates if energy(v)==best})
            self.assertTrue(verify_bounded_design(json.loads(encoded(packet))))

    def test_bounded_infeasibility_and_budget(self):
        r=closest_in_box([[2,4]],[1],[0,0],[0,0],[10,10]);self.assertEqual(r['status'],'NO_FEASIBLE_DESIGN')
        with self.assertRaises(WorkLimit):closest_in_box([[1,1]],[50],[0,0],[0,0],[100,100],node_limit=1)

    def test_global_experiment_beats_certificate_witnesses(self):
        s=SequenceLibrary(dict(operator=[[1,1],[1,0]],seed=[0,1],readouts={'expensive':[1,0],'cheap':[0,1]}))
        old=s.witness_experiment([1,0],[0,0],readout_costs=[100,1]);new=s.experiment([1,0],[0,0],readout_costs=[100,1])
        self.assertEqual(old['cost'],100);self.assertEqual(new['cost'],2);self.assertEqual(new['word'],(0,))

    def test_multicontext_experiment_against_all_short_words(self):
        from perfectpower.observable_machine import _word,_apply
        ops=[[[1,1],[0,1]],[[0,1],[1,0]]];readouts=[[1,0],[0,1]]
        machine=integral_machine(ops,[1,0],readouts);left=[1,0];right=[0,0]
        result=cheapest_experiment(machine,left,right,[3,2],[100,1])
        options=[]
        for length in range(6):
            for word in itertools.product(range(2),repeat=length):
                values=_apply(readouts,_word(ops,left,word))
                for output,value in enumerate(values):
                    if value:options.append(sum([3,2][i] for i in word)+[100,1][output])
        self.assertEqual(result['cost'],min(options));self.assertEqual(result['cost'],3)
        with self.assertRaises(ValueError):cheapest_experiment(machine,left,right,[0,2],[100,1])

    def test_transition_boxes_maps_and_tamper(self):
        for chart,box,branch in [('branch',['3/2','8/5','-1/100','1/100'],0),('infinity',['3/5','13/20','-1/100','1/100'],None)]:
            p=certify_transition([0,-1,0,1],chart,box,[2,3,'-1/4','1/4'],branch)
            self.assertTrue(p['complete']);self.assertTrue(verify_transition(p))
            for x in (Q(box[0]),Q(box[1])):
                for y in (Q(-1,100),Q(0),Q(1,100)):
                    row=transport_point(p,[x,y]);z=complex(float(x),float(y));expected=z*z if chart=='branch' else z**-2
                    actual=list(map(Q,row['target_point']));self.assertAlmostEqual(float(actual[0]),expected.real,places=12);self.assertAlmostEqual(float(actual[1]),expected.imag,places=12)
            bad=copy.deepcopy(p);bad['data']['identity']['left'][0]='123';self.assertFalse(verify_transition(bad))

    def test_even_infinity_and_higher_genus_identities(self):
        for degree in (4,5,7,9):
            coeff=[-1]+[0]*(degree-1)+[1]
            p=certify_transition(coeff,'infinity',['3/5','13/20','-1/100','1/100'],[1,4,-1,1])
            self.assertTrue(verify_transition(p));self.assertTrue(p['complete'])

    def test_family_holdout_and_public_solver(self):
        def spec(p,q):
            return dict(kind='curve',left=[0]*p+[1],right=[0]*q+[1],predicate={'expr':'x*x+y*y-1000000','relation':'<='})
        families=[dict(family='2/3',split='train',specification=spec(2,3)),dict(family='2/5',split='test',specification=spec(2,5))]
        packet=heldout_families(families,size_per_family=12)
        result=solve_public_tasks(public_tasks(packet,'test'));self.assertEqual(evaluate_tasks(packet,result['predictions'])['accuracy'],'1')
        with self.assertRaises(ValueError):heldout_families(families+[dict(families[0],split='test')])
        with self.assertRaises(ValueError):heldout_families(families+[dict(family='alias',split='test',specification=spec(2,3))])

    @unittest.skipUnless(shutil.which('cc'),'C compiler unavailable')
    def test_compiled_kernel_independent_exact_outputs(self):
        from array import array
        a=[[1,2],[3,4]];b=[[5,6],[7,8]];expected=array('Q',[19,22,43,50]).tobytes()
        with CompiledMatmul(a,b) as k:
            self.assertEqual(k.conventional(),expected)
            self.assertEqual(k.untiled(),expected)
            for values in compatible_tiles().page():self.assertEqual(k.tiled(values['values']),expected)
            with self.assertRaises(ValueError):k.tiled({'row_block':0,'column_block':1})
        self.assertEqual(compatible_tiles(max_tile_bytes=8).count(),1)

    def test_http_roundtrip_errors_and_origin(self):
        server=QueryHTTPServer(':memory:');thread=threading.Thread(target=server.serve_forever,daemon=True);thread.start()
        base=f'http://127.0.0.1:{server.server_port}'
        try:
            self.assertTrue(json.load(urlopen(base+'/health'))['ok'])
            def post(value,headers=None):return urlopen(Request(base+'/query',data=json.dumps(value).encode(),headers=headers or {'Content-Type':'application/json'}))
            p=dict(kind='domain',predicate={'op':'and','args':[{'poly':[-1,1],'relation':'>='},{'poly':[-3,1],'relation':'<='}]})
            self.assertTrue(json.load(post(dict(op='register',kind='population',specification=p,name='x')))['ok'])
            self.assertEqual(json.load(post(dict(op='call',object='x',method='count')))['result'],3)
            with self.assertRaises(HTTPError) as error:post(dict(op='call',object='unknown',method='count'))
            self.assertEqual(error.exception.code,400)
            with self.assertRaises(HTTPError) as error:post(dict(op='list'),{'Content-Type':'application/json','Origin':'https://foreign.example'})
            self.assertEqual(error.exception.code,403)
            self.assertEqual(len(json.load(post(dict(op='list')))['result']),1)
        finally:server.shutdown();thread.join();server.server_close()

    def test_flavor_codimension_and_exact_response(self):
        from perfectpower import exact_linear as E
        r=stationarity_space();self.assertEqual((r['rank'],r['stationary_subspace_dimension']),(8,5))
        self.assertTrue(all(not any(E.apply(r['constraint_matrix'],v)) for v in r['kernel_basis']))
        response=allowed_linear_response();self.assertEqual(response['identities']['response_replay'],['0'])
        lo,hi=map(Q,response['coefficient']['interval']);self.assertTrue(Q(38,100)<lo<hi<Q(39,100))
        lo,hi=map(Q,response['golden_polynomial_response']['interval']);self.assertFalse(lo<=0<=hi)


if __name__=='__main__':unittest.main()
