import copy
import json
import unittest
from unittest.mock import patch
from perfectpower.elliptic_arithmetic import EllipticCurve
from perfectpower.elliptic_saturation_verifier import verify_saturation
from perfectpower.elliptic_saturation import MembershipSearch
from perfectpower.divisor_square import WorkLimit


class SaturationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.E=EllipticCurve([0,-2]);cls.P=cls.E.checked([3,5])
        cls.packet=cls.E.bounded_saturation([cls.E.mul(cls.P,6)])

    def test_repeated_enlargement_and_joint_closure(self):
        c=self.packet
        self.assertEqual(c['status'],'closed');self.assertEqual(c['closed_primes'],[2,3])
        self.assertEqual(c['generators'],[['3','5']]);self.assertEqual(len(c['stages']),5)
        self.assertTrue(verify_saturation(json.loads(json.dumps(c))))
        self.assertIsNone(c['stages'][0]['closure_witnesses'])
        self.assertIsNone(c['stages'][2]['closure_witnesses'])
        self.assertEqual(c['stages'][3]['preimage']['prime'],2)

    def test_all_residue_lines_retained(self):
        E=EllipticCurve([-4,1]);P=E.checked([0,1]);Q=E.checked([2,1])
        c=E.bounded_saturation([E.add(P,Q),E.add(P,E.neg(Q))],max_steps=1)
        self.assertEqual(len(c['stages'][0]['preimage']['projective_fibres']),3)
        self.assertEqual(c['stages'][0]['preimage']['relation_basis'],[[1,1]])
        self.assertTrue(verify_saturation(c));self.assertEqual(c['status'],'step-limit')

    def test_torsion_compression_and_closure(self):
        c=EllipticCurve([0,1]).bounded_saturation([])
        self.assertEqual(c['status'],'closed');self.assertEqual(len(c['generators']),2)
        self.assertTrue(any(s['reductions'] for s in c['stages']))
        self.assertTrue(verify_saturation(c))

    def test_dependent_presentation_and_infinity(self):
        c=self.E.bounded_saturation([None,self.P,self.P,self.E.neg(self.P)])
        self.assertEqual(c['generators'],[['3','-5']]);self.assertEqual(c['status'],'closed')
        self.assertEqual(len(c['initial_reductions']),3);self.assertTrue(verify_saturation(c))

    def test_failed_membership_is_not_nonmembership(self):
        c=self.E.bounded_saturation([self.P],coefficient_bound=0,max_steps=2)
        self.assertEqual(c['status'],'step-limit');self.assertEqual(c['closed_primes'],[])
        self.assertTrue(verify_saturation(c))
        c=self.E.bounded_saturation([self.P],membership_limit=1)
        self.assertEqual(c['status'],'closed');self.assertTrue(verify_saturation(c))
        search=MembershipSearch(self.E,2,100)
        with patch.object(self.E,'mul',side_effect=WorkLimit('bit budget')):
            self.assertIsNone(search.witness([self.P],self.P))

    def test_width_limit_returns_complete_last_preimage(self):
        E=EllipticCurve([-36,0]);P=E.checked([12,36])
        c=E.bounded_saturation([E.mul(P,n) for n in [1,2,3,4]],coefficient_bound=0,max_steps=1)
        self.assertEqual(c['status'],'width-limit');self.assertEqual(len(c['generators']),6)
        self.assertTrue(verify_saturation(c))

    def test_discovery_free_replay(self):
        with patch('perfectpower.elliptic_saturation.MembershipSearch.witness',side_effect=AssertionError('discovery called')):
            self.assertTrue(verify_saturation(self.packet))

    def test_corruptions_rejected(self):
        variants=[]
        for path,value in [(('status',),'step-limit'),(('closed_primes',),[2]),
                           (('root_nodes',),True),(('execution_verified',),True),
                           (('complete_mordell_weil_group',),True),(('max_steps',),True)]:
            c=copy.deepcopy(self.packet);c[path[0]]=value;variants.append(c)
        c=copy.deepcopy(self.packet);c['stages'][0]['preimage']['projective_fibres'].pop();variants.append(c)
        c=copy.deepcopy(self.packet);c['stages'][0]['closure_witnesses']=[[1]];variants.append(c)
        c=copy.deepcopy(self.packet);c['stages'][-1]['closure_witnesses'][0]=[True];variants.append(c)
        c=copy.deepcopy(self.packet);c['stages'][1]['preimage']['source_points']=[];variants.append(c)
        c=copy.deepcopy(self.packet);c['stages'].pop();variants.append(c)
        c=copy.deepcopy(self.packet);c['stages'][0]['generators']=[];variants.append(c)
        for c in variants:self.assertFalse(verify_saturation(c))
        c=self.E.bounded_saturation([None,self.P])
        c['initial_reductions'][0]['coefficients']=[1]
        self.assertFalse(verify_saturation(c))

    def test_controls_and_shared_budgets(self):
        for args in [dict(primes=[]),dict(primes=[3,2]),dict(primes=[2,2]),dict(primes=[True]),
                     dict(primes=[11]),dict(max_steps=True),dict(max_steps=17),
                     dict(coefficient_bound=-1),dict(membership_limit=0)]:
            with self.assertRaises(ValueError):self.E.bounded_saturation([self.P],**args)
        with self.assertRaises(WorkLimit):self.E.bounded_saturation([self.P],node_limit=1)
        self.assertFalse(verify_saturation(self.packet,node_limit=1))
        self.assertFalse(verify_saturation(self.packet,work_limit=1))


if __name__=='__main__':unittest.main()
