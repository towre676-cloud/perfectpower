import copy
from fractions import Fraction as Q
from itertools import combinations,product
import random
import unittest
from perfectpower.semantic_fibres import ImplementationFamily,Transport,projection_transport,check_composition,polynomial_chart
from perfectpower.future_states import future_quotient,check_quotient,check_word,diagnosis_plan,distinguishing_words,compare_models
from perfectpower.populations import ExactPopulation
from perfectpower.divisor_square import WorkLimit


def run_word(spec,state,word):
    trace=[spec['observations'][state]]
    for i,a in enumerate(word):
        state=spec['actions'][a][state]
        if state is None:return trace+[('disabled',a,i)]
        trace.append(spec['observations'][state])
    return trace


class SOEBridgeTests(unittest.TestCase):
    def test_semantic_fibres_keep_identities_weights_and_ties(self):
        spec={'variables':['x','y'],'semantics':['x+y'],'rows':[{'id':'a','values':[1,3],'weight':'1/2'},{'id':'b','values':[2,2],'weight':'3/2'},{'id':'c','values':[3,1]},{'id':'d','values':[1,3]}]}
        family=ImplementationFamily(spec);spec['rows'][0]['values'][0]=100
        result=family.query(semantic_value=[4],objectives=['x','y'])
        self.assertEqual(result['count'],4);self.assertEqual(result['mass'],'4');self.assertEqual(result['pareto_ids'],['a','b','c','d'])
        result=family.query(constraints=[{'expression':'x','relation':'ge','value':2}],objectives=['y'])
        self.assertEqual(result['pareto_ids'],['c']);self.assertEqual(result['minimum'],'1')
        p=projection_transport(family,mode='mass');self.assertTrue(p.mass_preserving()['preserving'])
        self.assertEqual(list(p.apply({r[0]:r[2] for r in family.rows}).values()),['4'])
        with self.assertRaises(WorkLimit):family.query(objectives=['x','y'],work_limit=1)

    def test_existing_population_signed_orbits_and_empty_family(self):
        population=ExactPopulation({'kind':'domain','fields':{'n':[0,1]},'predicate':{'op':'and','args':[{'poly':[3,1],'relation':'>='},{'poly':[-3,1],'relation':'<='}]}})
        family=ImplementationFamily.from_population(population,['n^2']);query=family.query()
        self.assertEqual(query['count'],7);self.assertEqual(sorted(f['count'] for f in query['fibres']),[1,2,2,2])
        self.assertEqual(family.query(semantic_value=[4],objectives=['n'])['pareto_ids'],['-2'])
        empty=ImplementationFamily({'variables':['x'],'semantics':['x'],'rows':[]})
        self.assertEqual(empty.query()['count'],0);self.assertEqual(projection_transport(empty).packet()['entries'],[])

    def test_all_transport_semirings_paths_and_associativity(self):
        for mode in Transport.MODES:
            a=Transport(['s'],['a','b'],[['s','a',2],['s','b',3]],mode=mode)
            b=Transport(['a','b'],['t'],[['a','t',5],['b','t',7]],mode=mode)
            c=Transport(['t'],['u'],[['t','u',11]],mode=mode)
            ab=a.compose(b);check_composition(ab.packet(),a,b)
            expected='7' if mode=='minplus' else '31'
            self.assertEqual(ab.packet()['entries'][0][2],expected)
            self.assertEqual(ab.compose(c).packet(),a.compose(b.compose(c)).packet())
            bad=ab.packet();bad['entries'][0][2]='999'
            with self.assertRaises(ValueError):check_composition(bad,a,b)
        with self.assertRaises(ValueError):a.compose(Transport(['t'],['u'],[['t','u',1]],mode='mass'))
        with self.assertRaises(ValueError):Transport(['x'],['y'],[['x','y','1/2']],mode='count')

    def test_mass_duality_stochasticity_and_original_lifts(self):
        t=Transport(['a','b'],['x','y'],[['a','x','1/3'],['a','y','2/3'],['b','y',1]],mode='mass')
        w={'a':2,'b':3};v={'x':5,'y':7}
        pushed=t.apply(w);pulled=t.apply(v,backward=True)
        self.assertEqual(sum(Q(pushed[k])*v[k] for k in v),sum(w[k]*Q(pulled[k]) for k in w))
        self.assertTrue(t.mass_preserving()['preserving']);self.assertEqual(sum(map(Q,pushed.values())),5)
        self.assertFalse(Transport(['a'],['x'],[['a','x',2]],mode='mass').mass_preserving()['preserving'])

    def test_temporal_alias_and_partial_action_legality(self):
        model={'observations':[0,1,0,1],'actions':{'tick':[1,0,3,2],'reset':[0,0,3,3]}}
        packet=future_quotient(model);self.assertTrue(check_quotient(packet,model));self.assertEqual(len(packet['blocks']),4)
        witness=next(w for w in packet['distinguishing_witnesses'] if (w['first'],w['second'])==(0,2))
        self.assertEqual(witness['word'],['reset'])
        model={'observations':[0,0,0],'actions':{'a':[1,0,None]}}
        packet=future_quotient(model);self.assertEqual(packet['blocks'],[[0,1],[2]])
        self.assertEqual(packet['distinguishing_witnesses'][0]['reason'],'legality')

    def test_random_future_equivalence_against_all_short_words(self):
        rng=random.Random(47017)
        for _ in range(80):
            n=3;spec={'observations':[rng.randrange(2) for _ in range(n)],'actions':{a:[rng.choice([None,*range(n)]) for i in range(n)] for a in ('a','b')}}
            packet=future_quotient(spec);self.assertTrue(check_quotient(packet,spec));all_witnesses=distinguishing_words(spec)
            words=[word for k in range(n*n+1) for word in product(spec['actions'],repeat=k)]
            for i,j in combinations(range(n),2):
                first=next((w for w in words if run_word(spec,i,w)!=run_word(spec,j,w)),None)
                self.assertEqual(packet['projection'][i]==packet['projection'][j],first is None)
                if first is not None:
                    witness=all_witnesses[i,j]
                    self.assertEqual(len(witness['word']),len(first));self.assertTrue(check_word(spec,i,j,witness))

    def test_packet_tampering_and_source_binding(self):
        model={'observations':[0,0,1],'actions':{'a':[1,2,0]}};p=future_quotient(model)
        for key in ('projection','quotient','distinguishing_witnesses'):
            bad=copy.deepcopy(p)
            if key=='projection':bad[key][0]=2
            elif key=='quotient':bad[key]['actions']['a'][0]=None
            else:bad[key]=[]
            with self.assertRaises(ValueError):check_quotient(bad,model)
        changed=copy.deepcopy(model);changed['actions']['a'][0]=0
        with self.assertRaises(ValueError):check_quotient(p,changed)

    def test_optimal_diagnosis_and_insufficient_menu(self):
        model={'observations':[0,0,1,1],'actions':{'cheap':[2,0,2,3],'costly':[0,2,2,3]}}
        probes=[{'name':'cheap','word':['cheap'],'cost':2},{'name':'costly','word':['costly'],'cost':9}]
        result=diagnosis_plan(model,probes);self.assertEqual(result['worst_case_cost'],'2')
        self.assertEqual(result['policy']['0']['probe'],'cheap')
        with self.assertRaises(WorkLimit):diagnosis_plan(model,probes,work_limit=1)
        model={'observations':[0,0,0,1],'actions':{'a':[0,1,3,3],'b':[0,3,2,3]}}
        result=diagnosis_plan(model,[{'name':'a','word':['a'],'cost':1}]);self.assertEqual(result['status'],'menu_insufficient');self.assertEqual(result['obstructions'][0]['states'],[0,1])
        result=diagnosis_plan(model,[{'name':a,'word':[a],'cost':1} for a in ('a','b')]);self.assertEqual(result['worst_case_cost'],'2')

    def test_adaptive_policy_beats_every_fixed_two_probe_schedule(self):
        model={'observations':[0,0,0,0,1,2],'actions':{'a':[4,4,5,5,4,5],'b':[4,5,4,4,4,5],'c':[4,4,4,5,4,5]}}
        probes=[{'name':a,'word':[a],'cost':1} for a in model['actions']]
        result=diagnosis_plan(model,probes);self.assertEqual(result['worst_case_cost'],'2')
        for pair in combinations(model['actions'],2):
            signatures=[tuple(str(run_word(model,s,[a])) for a in pair) for s in range(4)]
            self.assertLess(len(set(signatures)),4)
        signatures=[tuple(str(run_word(model,s,[a])) for a in model['actions']) for s in range(4)]
        self.assertEqual(len(set(signatures)),4)

    def test_global_nonlinear_chart_and_integer_image_restrictions(self):
        chart=polynomial_chart(['x','y'],['x+y^2','y'],['x-y^2','y'],['x+y^2','x+y^2+y'],['x','x+y'])
        self.assertTrue(chart['integer_lattice_equivalence'])
        chart=polynomial_chart(['x'],['2*x+1'],['(x-1)/2'],['(2*x+1)^2'],['x^2'])
        self.assertFalse(chart['integer_lattice_equivalence'])
        with self.assertRaises(ValueError):polynomial_chart(['x'],['x^2'],['x'],['x^2'],['x'])
        with self.assertRaises(ValueError):polynomial_chart(['x'],['x+1'],['x-1'],['x'],['x'])

    def test_cross_model_equivalence_and_shortest_counterexample(self):
        left={'observations':[0,1,0,1],'actions':{'tick':[1,0,3,2]}}
        right={'observations':[0,1],'actions':{'tick':[1,0]}}
        result=compare_models(left,right);self.assertTrue(result['equivalent'])
        self.assertEqual(len(result['common_quotient']['blocks']),2)
        right['actions']['tick'][0]=0
        result=compare_models(left,right);self.assertFalse(result['equivalent'])
        self.assertEqual(result['shortest_counterexample']['word'],['tick'])
        right={'observations':[0],'actions':{'tick':[None]}}
        self.assertEqual(compare_models(left,right)['shortest_counterexample']['reason'],'legality')

    def test_legality_trace_cannot_collide_with_user_observation(self):
        marker={'disabled_action':'a','position':0}
        model={'observations':[0,0,marker],'actions':{'a':[None,2,2]}}
        plan=diagnosis_plan(model,[{'name':'a','word':['a'],'cost':1}])
        self.assertEqual(plan['status'],'optimal')
        self.assertEqual(plan['worst_case_cost'],'1')

    def test_invalid_exact_inputs(self):
        for value in (0.5,True):
            with self.assertRaises(ValueError):Transport(['a'],['b'],[['a','b',value]],mode='mass')
        with self.assertRaises(ValueError):future_quotient({'observations':[0.1],'actions':{'a':[0]}})
        with self.assertRaises(ValueError):future_quotient({'observations':[0],'actions':{'a':[True]}})
        with self.assertRaises(ValueError):diagnosis_plan({'observations':[0],'actions':{'a':[0]}},[{'name':'a','word':['a'],'cost':0}])


if __name__=='__main__':unittest.main()
