import random
import unittest
from fractions import Fraction
from itertools import combinations
from perfectpower.information import (Observation, InformationProblem, PlanningLimit,
    AffineTransport, push_counts, transport_defect, compile_square_query,
    polynomial_information)


class InformationTests(unittest.TestCase):
    def test_lost_lift_and_separating_refinement(self):
        p = InformationProblem(range(4),lambda x:x % 4,
            [Observation('shadow',lambda x:x % 2),Observation('lift',lambda x:x % 4,3)],
            scope='Z/4Z')
        a=p.ambiguity(['shadow'])
        self.assertEqual((a['left'],a['right']),(0,2))
        self.assertEqual(a['separators'],['lift'])
        r=p.compile(['shadow'])
        self.assertEqual(r['added'],['lift'])
        self.assertEqual(r['cost'],3)

    def test_target_not_reconstruction_and_zero_cost(self):
        p=InformationProblem(range(20),lambda x:x % 2,
            [Observation('identity',lambda x:x,10),Observation('parity',lambda x:x % 2,0)],
            scope='finite integers 0..19')
        r=p.compile()
        self.assertEqual(r['added'],['parity'])
        self.assertEqual(len(r['decoder']),2)
        self.assertEqual(p.compile(['parity'],subset_limit=1)['added'],[])

    def test_unseparable_returns_actual_collision(self):
        p=InformationProblem([0,2],lambda x:x,
            [Observation('parity',lambda x:x % 2)],scope='two integers')
        r=p.compile()
        self.assertEqual(r['status'],'UNSEPARABLE')
        self.assertEqual(r['ambiguity']['separators'],[])

    def test_exhaustive_optimum_vs_independent_partition_search(self):
        rng=random.Random(501)
        for _ in range(80):
            labels=[rng.randrange(3) for i in range(7)]
            rows=[[rng.randrange(3) for i in range(7)] for j in range(5)]
            costs=[rng.randrange(5) for j in rows]
            p=InformationProblem(range(7),lambda x:labels[x],
                [Observation(str(j),lambda x,j=j:rows[j][x],costs[j]) for j in range(5)],
                scope='random finite differential fixture')
            candidates=[]
            for n in range(6):
                for js in combinations(range(5),n):
                    groups={}
                    for i in range(7):
                        groups.setdefault(tuple(rows[j][i] for j in js),set()).add(labels[i])
                    if all(len(g)==1 for g in groups.values()):
                        candidates.append((sum(costs[j] for j in js),n,js))
            r=p.compile()
            if candidates:
                want=min(candidates)
                self.assertEqual((r['cost'],len(r['added']),tuple(map(int,r['added']))),want)
            else:
                self.assertEqual(r['status'],'UNSEPARABLE')

    def test_budget_never_claims_optimum(self):
        p=InformationProblem(range(4),lambda x:x,
            [Observation('full',lambda x:x)],scope='four points')
        with self.assertRaises(PlanningLimit): p.compile(subset_limit=1)
        with self.assertRaises(PlanningLimit):
            InformationProblem(range(5),lambda x:x,[],scope='five',pair_limit=1)

    def test_empty_constant_and_input_validation(self):
        for states in ([],[1,2,3]):
            p=InformationProblem(states,lambda x:True,[],scope='explicit domain')
            self.assertEqual(p.compile()['added'],[])
        with self.assertRaises(ValueError): InformationProblem([1,1],lambda x:x,[],scope='duplicate')
        with self.assertRaises(ValueError): InformationProblem([],lambda x:x,[],scope='')
        with self.assertRaises(ValueError): Observation('bad',lambda x:x,-1)
        p=InformationProblem([1],lambda x:x,[],scope='one')
        with self.assertRaises(ValueError): p.compile(['unknown'])

    def test_composition_order_and_integral_intermediate(self):
        first=AffineTransport((2,),(1,))
        after=AffineTransport((3,),(-4,))
        for x in range(-10,11):
            self.assertEqual(first.then(after).forward((x,)),after.forward(first.forward((x,))))
        self.assertNotEqual(first.then(after).forward((2,)),after.then(first).forward((2,)))
        half=AffineTransport((Fraction(1,2),),(0,))
        double=AffineTransport((2,),(0,))
        self.assertEqual(half.then(double).pullback((1,)),(1,))
        self.assertIsNone(half.pullback_chain((1,),double))
        self.assertEqual(half.pullback_chain((2,),double),(2,))
        self.assertIsNone(first.pullback((2,)))

    def test_twist_preserves_exact_inverse_restrictions(self):
        twist=AffineTransport((4,8),(0,0))
        self.assertEqual(twist.pullback((12,40)),(3,5))
        self.assertIsNone(twist.pullback((3,5)))
        with self.assertRaises(ValueError):twist.forward((1,))

    def test_multiplicity_cocycle_with_merging_and_signed_defects(self):
        source={0:2,1:3,2:1};middle={0:1,1:1};target={0:4}
        f=lambda x:x % 2;g=lambda x:0
        d1=transport_defect(source,middle,f)
        d2=transport_defect(middle,target,g)
        composed=transport_defect(source,target,lambda x:g(f(x)))
        pushed=push_counts(d1,g)
        for x in set(composed)|set(pushed)|set(d2):
            self.assertEqual(composed.get(x,0),pushed.get(x,0)+d2.get(x,0))
        self.assertEqual(composed,{0:2})
        with self.assertRaises(ValueError):transport_defect({0:-1},{},f)

    def test_square_consumer_preserves_unknown(self):
        self.assertEqual(compile_square_query([-1,0,1],1,lambda p:p[0]==1)['status'],'SAT')
        self.assertEqual(compile_square_query([-1,0,1],1,lambda p:p[0]==20)['status'],'UNSAT')
        r=compile_square_query([1_000_000,1],1,lambda p:True,fibre_work_limit=10)
        self.assertEqual(r['status'],'UNRESOLVED')
        self.assertTrue(r['residual_parameters'])

    def test_signed_unit_integration_matches_existing_sieve(self):
        from orbit_lattice import allowed, information_plan
        args=(9,6,[(-1,-3,1),(-1,0,2)],(-3,-3,1),9,-3)
        table=allowed(*args,plane=(0,1,0))
        result=information_plan(*args,plane=(0,1,0),scope='D72 mod9')
        self.assertEqual(result['periods'],table['periods'])
        self.assertEqual(result['allowed_residue_count'],len(table['allowed_residues']))
        self.assertEqual(result['added'],['plane'])
        self.assertFalse(result['global_exponent_bound'])
        self.assertEqual(result['decoder'],[{'readout':(False,),'target':False},
                                            {'readout':(True,),'target':True}])

    def test_random_rational_transports_against_sequential_execution(self):
        rng=random.Random(207)
        for _ in range(100):
            a,b=[rng.choice([-3,-2,-1,1,2,3]) for i in range(2)]
            first=AffineTransport((Fraction(a,rng.randrange(1,5)),),(rng.randrange(-4,5),))
            after=AffineTransport((Fraction(b,rng.randrange(1,5)),),(rng.randrange(-4,5),))
            for x in range(-5,6):
                y=after.forward(first.forward((x,)))
                self.assertEqual(first.then(after).forward((x,)),y)
                self.assertEqual(first.then(after).pullback(y),(x,))
                if first.forward((x,))[0].denominator==1:
                    self.assertEqual(first.pullback_chain(y,after),(x,))
                else:
                    self.assertIsNone(first.pullback_chain(y,after))

    def test_polynomial_interval_decoder_matches_roots(self):
        p=polynomial_information([-2,0,0,1],2,-10,11,[2,3,5,7,11])
        r=p.compile()
        self.assertEqual(r['status'],'SUFFICIENT_ON_FINITE_DOMAIN')
        names=r['existing']+r['added']; indices=p._indices(names)
        decoder={tuple(row['readout']):row['target'] for row in r['decoder']}
        for j in range(len(p.states)):
            self.assertEqual(decoder[tuple(p.values[i][j] for i in indices)],p.labels[j])


if __name__=='__main__':unittest.main()
