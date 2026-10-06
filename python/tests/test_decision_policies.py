import copy
import itertools
import random
import unittest
from fractions import Fraction as Q
from functools import lru_cache
from perfectpower import exact_linear as E,polyalg as P
from perfectpower.decision_regions import CalibrationPolicy,clip
from perfectpower.diagnostic_programs import DiagnosticPolicy
from perfectpower.collision_geometry import cubic_collisions
from perfectpower.projected_populations import ProjectedPopulation
from perfectpower.divisor_square import WorkLimit
from perfectpower.catalogue import Catalogue,encoded
from perfectpower.query_service import dispatch


def source(f,lo=-20,hi=20,extra=True):
    return dict(kind='domain',predicate={'op':'and','args':[{'poly':[-lo,1],'relation':'>='},{'poly':[-hi,1],'relation':'<='},extra]},fields={'f':f})


def energy(v,t,m):
    return sum((Q(v[i])-t[i])*m[i][j]*(Q(v[j])-t[j]) for i in range(len(v)) for j in range(len(v)))


class DecisionPolicies(unittest.TestCase):
    def test_cubic_collision_equation_exhaustive_coefficients(self):
        for a,b,c in itertools.product([-2,-1,1,2],range(-3,4),range(-5,6)):
            f=[3,c,b,a];packet=cubic_collisions(f)
            expected=[(x,y) for x in range(-20,21) for y in range(x+1,21) if P.evaluate(f,x)==P.evaluate(f,y)]
            self.assertEqual(packet['pairs'],expected)
            for x,y in packet['pairs']:self.assertEqual((3*a*(x+y)+2*b)**2+3*a*a*(x-y)**2,packet['radius'])
        with self.assertRaises(WorkLimit):cubic_collisions([0,-10**20,0,1],work_limit=10)
        with self.assertRaises(ValueError):cubic_collisions([0,-1,0,1.0])

    def test_cubic_domain_owners_and_multiplicities(self):
        for f in ([0,-1,0,1],[5,-6,0,1],[-2,-5,3,-2],[7,4,2,1]):
            for extra in (True,{'poly':[0,1],'modulus':3,'value':1,'relation':'!='}):
                p=ProjectedPopulation(dict(source=source(f,extra=extra),field='f'))
                values={}
                for n in range(-20,21):
                    if extra is not True and n%3==1:continue
                    values.setdefault(int(P.evaluate(f,n)),[]).append(n)
                self.assertEqual(p.count(),len(values))
                for value,owners in values.items():
                    self.assertEqual(p.multiplicity(value),len(owners));self.assertEqual(p.select(p.locate(value))['parameter'],min(owners))

    def test_huge_translated_cubic_and_monotone_fifth(self):
        shift=10**50;f=[-shift**3+shift,3*shift**2-1,-3*shift,1]
        p=ProjectedPopulation(dict(source=source(f,shift-10**50,shift+10**50),field='f'))
        self.assertEqual(p.count(),2*10**50-1);self.assertEqual(p.multiplicity(0),3)
        self.assertEqual(p.select(p.locate(0))['parameter'],shift-1)
        p=ProjectedPopulation(dict(source=source([0,1,0,0,0,1],-10**50,10**50),field='f'))
        self.assertEqual(p.count(),2*10**50+1);self.assertEqual(p.multiplicity(0),1)
        self.assertEqual(p.evidence()['collision_geometry']['direction'],'increasing')
        with self.assertRaises(ValueError):ProjectedPopulation(dict(source=source([0,0,-3,0,1]),field='f'))

    def test_one_dimensional_regions_all_boundaries(self):
        p=CalibrationPolicy(dict(matrix=[[1,1]],observation=[4],lower=[0,0],upper=[4,4],target_origin=[0,4],target_basis=[[1],[-1]],target_box=[0,4]))
        self.assertEqual(p.summary()['cells'],5)
        for k in range(17):
            x=Q(k,4);candidates=[(i,4-i) for i in range(5)];costs=[energy(v,(x,4-x),[[1,0],[0,1]]) for v in candidates]
            self.assertEqual(p.decide([x])['minimizers'],[v for v,c in zip(candidates,costs) if c==min(costs)])
        self.assertEqual(p.decide(['1/2'])['minimizers'],[(0,4),(1,3)])
        with self.assertRaises(ValueError):p.decide([5])

    def test_two_dimensional_oracle_policy_independent_all_settings(self):
        rng=random.Random(944)
        for _ in range(6):
            m=[[2,1,0],[1,3,1],[0,1,2]];origin=[Q(rng.randrange(-2,3),2),0,3]
            basis=[[1,0],[0,1],[-1,-1]]
            p=CalibrationPolicy(dict(matrix=[[1,1,1]],observation=[3],lower=[0]*3,upper=[3]*3,metric=m,target_origin=origin,target_basis=basis,target_box=[-1,4,-1,4],inequalities=[dict(coefficients=[1,-1,0],relation='<=',rhs=2)]))
            candidates=[v for v in itertools.product(range(4),repeat=3) if sum(v)==3 and v[0]-v[1]<=2]
            points={tuple(v) for cell in p.packet['cells'] for v in cell['vertices']}
            points.update(itertools.product([Q(k,2) for k in range(-2,9)],repeat=2))
            for point in points:
                target=tuple(a+b for a,b in zip(origin,E.apply(basis,point)));costs=[energy(v,target,m) for v in candidates]
                expected=sorted(v for v,c in zip(candidates,costs) if c==min(costs))
                self.assertEqual(p.decide(point)['minimizers'],expected)
            for contact in p.packet['contacts']:
                for v in contact['vertices']:self.assertTrue(set(contact['settings'])<=set(p.decide(v)['minimizers']))

    def test_lower_dimensional_cells_and_identical_costs(self):
        # Three integer settings; both variable directions affect only coordinates 2/3.
        p=CalibrationPolicy(dict(matrix=[[1,0,0],[0,1,0],[0,0,1]],observation=[0,0,0],lower=[0]*3,upper=[1]*3,target_origin=[0,0,0],target_basis=[[1,0],[0,1],[0,0]],target_box=[-1,1,-1,1]))
        self.assertEqual(p.summary()['cells'],1)
        self.assertEqual(clip([(Q(0),Q(0)),(Q(1),Q(0)),(Q(1),Q(1)),(Q(0),Q(1))],[1,0],0),[(Q(0),Q(0)),(Q(0),Q(1))])
        self.assertEqual(clip([(Q(0),Q(0)),(Q(0),Q(1))],[0,1],0),[(Q(0),Q(0))])

    def test_boundary_only_cells_and_permanent_ties(self):
        p=CalibrationPolicy(dict(matrix=[[0,0]],observation=[0],lower=[0,0],upper=[2,2],target_origin=[0,0],target_basis=[[1,0],[0,1]],target_box=['1/2','3/2','1/2','3/2']))
        from collections import Counter
        self.assertEqual(Counter(c['dimension'] for c in p.packet['cells']),{0:4,1:4,2:1})
        self.assertEqual(len(p.decide(['1/2','1/2'])['minimizers']),4)
        p=CalibrationPolicy(dict(matrix=[[1,1,0]],observation=[1],lower=[0,0,0],upper=[1,1,1],target_origin=['1/2','1/2',0],target_basis=[[1,0],[1,0],[0,1]],target_box=[-1,1,0,1]))
        self.assertEqual(len(p.decide([0,'1/2'])['minimizers']),4)
        self.assertEqual(len(p.decide([0,0])['minimizers']),2)

    def test_infeasible_and_policy_work_budgets(self):
        spec=dict(matrix=[[2,4]],observation=[1],lower=[0,0],upper=[4,4],target_origin=[0,0],target_basis=[[1,0],[0,1]],target_box=[0,1,0,1])
        p=CalibrationPolicy(spec);self.assertEqual(p.summary()['status'],'NO_FEASIBLE_DESIGN');self.assertEqual(p.decide([0,0])['minimizers'],[])
        for extra in (dict(query_limit=1),dict(node_limit=1)):
            with self.assertRaises(WorkLimit):CalibrationPolicy(dict(spec,observation=[4],**extra))

    def test_diagnostic_uses_full_hypothesis_space_and_reset(self):
        s=dict(operators=[[[1,0],[0,1]]],seed=[1,0],readouts={'x':[1,0],'y':[0,1],'combined':[1,2]},readout_costs={'x':1,'y':1,'combined':4},hypotheses={str((x,y)):[x,y] for x in (0,1) for y in (0,1)})
        p=DiagnosticPolicy(s);self.assertEqual(p.packet['worst_case_cost'],2)
        for name in p.names:self.assertEqual((p.run(name)['identified'],p.run(name)['total_cost']),(name,2))
        with self.assertRaises(ValueError):p.step(0,999)
        with self.assertRaises(ValueError):p.step(0,True)

    def test_diagnostic_optimum_against_independent_word_subset_enumeration(self):
        rng=random.Random(191)
        for _ in range(8):
            s=dict(operators=[[[1,1],[0,1]],[[0,1],[1,0]]],readouts={'x':[1,0],'y':[0,1]},operator_costs=[1,2],readout_costs=[1,2],hypotheses={str(i):v for i,v in enumerate(rng.sample(list(itertools.product(range(3),repeat=2)),4))})
            p=DiagnosticPolicy(s);upper=p.packet['incumbent_cost'];states=list(s['hypotheses'].values());experiments=[]
            def words(word=(),cost=0):
                if cost+1>upper:return
                transformed=states
                for letter in word:transformed=[E.apply(s['operators'][letter],v) for v in transformed]
                for row,price in zip(s['readouts'].values(),s['readout_costs']):
                    if cost+price<=upper:experiments.append((cost+price,tuple(sum(a*b for a,b in zip(row,v)) for v in transformed)))
                for letter,price in enumerate(s['operator_costs']):words(word+(letter,),cost+price)
            words()
            @lru_cache(None)
            def solve(indices):
                if len(indices)==1:return 0
                choices=[]
                for price,answers in experiments:
                    groups={}
                    for i in indices:groups.setdefault(answers[i],[]).append(i)
                    if len(groups)>1:choices.append(price+max(solve(tuple(g)) for g in groups.values()))
                return min(choices)
            self.assertEqual(p.packet['worst_case_cost'],solve(tuple(range(4))))
            results=[p.run(name) for name in p.names]
            self.assertTrue(all(r['identified']==r['hypothesis'] for r in results));self.assertEqual(max(r['total_cost'] for r in results),p.packet['worst_case_cost'])

    def test_indistinguishable_zero_cost_singleton_and_budgets(self):
        s=dict(operators=[[[1,0],[0,1]]],readouts={'x':[1,0]},hypotheses={'a':[1,0],'b':[1,1]})
        self.assertEqual(DiagnosticPolicy(s).summary()['status'],'INDISTINGUISHABLE_HYPOTHESES')
        p=DiagnosticPolicy(dict(s,hypotheses={'a':[1,0]}));self.assertEqual(p.run('a')['total_cost'],0)
        p=DiagnosticPolicy(dict(s,hypotheses={'a':[0,0],'b':[1,0]},readout_costs=[0]));self.assertEqual(p.packet['worst_case_cost'],0)
        with self.assertRaises(ValueError):DiagnosticPolicy(dict(s,operator_costs=[0]))
        s=dict(s,operators=[[[1,1],[0,1]]],hypotheses={'a':[0,0],'b':[0,1]},state_limit=1)
        with self.assertRaises(WorkLimit):DiagnosticPolicy(s)

    def test_service_persistence_and_policy_allowlists(self):
        from perfectpower.application_objects import SequenceLibrary
        library=SequenceLibrary(dict(operator=[[1]],seed=[0],readouts={'x':[1]}))
        with self.assertRaises(ValueError):library.diagnostic({'a':[0],'b':[1]},readout_costs=[1,2])
        from tempfile import TemporaryDirectory
        from pathlib import Path
        with TemporaryDirectory() as directory:
            path=str(Path(directory)/'policies.sqlite')
            with Catalogue(path) as c:
                spec=dict(matrix=[[1,1]],observation=[2],lower=[0,0],upper=[2,2],target_origin=[0,2],target_basis=[[1],[-1]],target_box=[0,2])
                c.register('calibration_policy',spec,'p')
                result=dispatch(c,dict(op='call',object='p',method='decide',args=dict(parameter=['1/2'])))
                self.assertEqual(result['minimizers'],[(0,2),(1,1)])
                c.register('diagnostic_policy',dict(operators=[[[1]]],readouts={'x':[1]},hypotheses={'a':[0],'b':[1]}),'d')
            with Catalogue(path) as c:
                self.assertEqual(dispatch(c,dict(op='call',object='d',method='run',args=dict(hypothesis='b')))['identified'],'b')
                self.assertEqual(c.get('p').summary()['cells'],3)
                with self.assertRaises(ValueError):dispatch(c,dict(op='call',object='p',method='__dict__'))


if __name__=='__main__':unittest.main()
