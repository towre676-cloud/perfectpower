import copy
import json
import tempfile
import unittest
from itertools import product
from pathlib import Path
from unittest.mock import patch
from perfectpower.elliptic_arithmetic import EllipticCurve,encode_point
from perfectpower.elliptic_subgroups import row_basis,lines
from perfectpower.elliptic_subgroup_verifier import verify_subgroup_preimage
from perfectpower.divisor_square import WorkLimit
from perfectpower.catalogue import Catalogue
from perfectpower.query_service import dispatch


class SubgroupPreimageTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.E=EllipticCurve([-4,1]);cls.P=cls.E.checked([0,1]);cls.Q=cls.E.checked([2,1])
        E,P,Q=cls.E,cls.P,cls.Q
        cls.two_source=[E.add(P,Q),E.add(P,E.neg(Q))]
        cls.three_source=[E.add(E.mul(P,2),Q),E.add(P,E.mul(Q,2))]
        cls.two=E.subgroup_preimage(cls.two_source,2)
        cls.three=E.subgroup_preimage(cls.three_source,3)

    def test_hidden_two_division_relation_and_recovery(self):
        E=self.E
        for p in self.two_source:self.assertEqual(E.rational_halves(p)['points'],[])
        self.assertEqual(self.two['relation_basis'],[[1,1]])
        new=[E.checked(p) for p in self.two['replacement_points']]
        self.assertEqual(new[0],self.P);self.assertEqual(E.add(new[0],E.neg(new[1])),self.Q)
        self.assertTrue(verify_subgroup_preimage(self.two))

    def test_hidden_three_division_relation_and_recovery(self):
        E=self.E
        for p in self.three_source:self.assertEqual(E.rational_thirds(p)['points'],[])
        self.assertEqual(self.three['relation_basis'],[[1,1]])
        new=[E.checked(p) for p in self.three['replacement_points']]
        self.assertEqual(new[0],E.add(self.P,self.Q))
        self.assertEqual(E.add(E.mul(new[0],2),E.neg(new[1])),self.P)
        self.assertEqual(E.add(new[1],E.neg(new[0])),self.Q)
        self.assertTrue(verify_subgroup_preimage(self.three))

    def test_source_group_containment_equations(self):
        for cert in (self.two,self.three):
            source=[self.E.checked(h) for h in cert['source_points']]
            replacement=[self.E.checked(h) for h in cert['replacement_points']]
            for equation in cert['replacement_equations']:
                pivot=equation['pivot'];out=self.E.mul(replacement[pivot],cert['prime'])
                for j,c in enumerate(equation['coefficients']):
                    if j!=pivot:out=self.E.add(out,self.E.neg(self.E.mul(replacement[j],c)))
                self.assertEqual(out,source[pivot])

    def test_no_relation_and_empty_input(self):
        E=EllipticCurve([0,-2])
        for prime in (2,3):
            c=E.subgroup_preimage([[3,5]],prime)
            self.assertEqual(c['relation_basis'],[]);self.assertEqual(c['generators'],[['3','5']])
            self.assertTrue(verify_subgroup_preimage(c))
            c=E.subgroup_preimage([],prime)
            self.assertEqual(c['generators'],[]);self.assertTrue(verify_subgroup_preimage(c))
        c=EllipticCurve([0,1]).subgroup_preimage([],3)
        self.assertEqual(c['generators'],[['0','-1'],['0','1']]);self.assertTrue(verify_subgroup_preimage(c))

    def test_dependent_and_identity_generators(self):
        E=EllipticCurve([0,-2]);p=[3,5]
        for points,prime in (([p,p],2),([p,p],3),([None,None,None,None],3)):
            c=E.subgroup_preimage(points,prime);self.assertTrue(verify_subgroup_preimage(c))
            if points[0] is None:
                self.assertEqual(c['relation_dimension'],4);self.assertEqual(c['generators'],[])
            else:self.assertEqual(c['relation_dimension'],1)
        # Relation dimension cannot be equated to an index when sources depend.
        c=E.subgroup_preimage([p,p],2);self.assertEqual(c['generators'],[['3','5']])

    def test_torsion_lifting_to_order_nine(self):
        E=EllipticCurve([-3,-12,-12,0,0]);p=E.checked([0,0]);T=E.mul(p,3)
        c=E.subgroup_preimage([T],3);self.assertTrue(verify_subgroup_preimage(c))
        self.assertEqual(c['relation_basis'],[[1]])
        H=E.checked(c['replacement_points'][0]);self.assertIsNone(E.mul(H,9));self.assertIsNotNone(E.mul(H,3))
        generated={None}
        for g in c['generators']:
            generated={E.add(h,E.mul(g,k)) for h in generated for k in range(9)}
        self.assertEqual(generated,{E.mul(p,k) for k in range(9)})

    def test_generalized_model_and_json_replay(self):
        E=EllipticCurve([1,'-1/4',1,'-1/2','-9/4']);p=E.checked([3,3])
        for prime in (2,3):
            c=E.subgroup_preimage([E.mul(p,prime)],prime)
            self.assertEqual(c['replacement_points'],[['3','3']]);self.assertTrue(verify_subgroup_preimage(json.loads(json.dumps(c))))

    def test_projective_enumeration_and_rref_span(self):
        for prime in (2,3):
            for width in range(5):
                ls=lines(prime,width);self.assertEqual(len(ls),(prime**width-1)//(prime-1))
                expanded={tuple(c*x%prime for x in v) for v in ls for c in range(1,prime)}
                self.assertEqual(expanded,set(product(range(prime),repeat=width))-{(0,)*width})
        for prime,rows in ((2,[[1,1,0],[0,1,1],[1,0,1]]),(3,[[1,2,0],[2,1,1],[1,1,1]])):
            basis=row_basis(rows,prime,3)
            def span(rs):return {tuple(sum(c*v[i] for c,v in zip(cs,rs))%prime for i in range(3)) for cs in product(range(prime),repeat=len(rs))}
            self.assertEqual(span(rows),span(basis))

    def test_every_small_residue_combination_is_classified(self):
        for cert in (self.two,self.three):
            p=cert['prime'];source=[self.E.checked(h) for h in cert['source_points']]
            basis=cert['relation_basis']
            relation_space={tuple(sum(c*v[j] for c,v in zip(cs,basis))%p for j in range(2)) for cs in product(range(p),repeat=len(basis))}
            for v in product(range(p),repeat=2):
                target=self.E.add(self.E.mul(source[0],v[0]),self.E.mul(source[1],v[1]))
                fibre=self.E.rational_halves(target) if p==2 else self.E.rational_thirds(target)
                self.assertEqual(bool(fibre['points']),v in relation_space)

    def test_discovery_free_replay(self):
        with patch('perfectpower.elliptic_subgroups.row_basis',side_effect=AssertionError('producer elimination')),patch('perfectpower.elliptic_subgroups.subgroup_preimage',side_effect=AssertionError('producer')),patch('perfectpower.elliptic_arithmetic.rational_root_certificate',side_effect=AssertionError('search')):
            self.assertTrue(verify_subgroup_preimage(self.two));self.assertTrue(verify_subgroup_preimage(self.three))

    def test_corruptions_missing_lines_and_false_group_claims(self):
        for field,value in (('prime',True),('relation_dimension',True),('relation_dimension',0),('relation_basis',[]),('complete',1),('complete_mordell_weil_group',True),('scope','complete global group'),('root_nodes',0),('generators',[]),('replacement_points',self.three['source_points'])):
            c=copy.deepcopy(self.three);c[field]=value;self.assertFalse(verify_subgroup_preimage(c))
        for mutate in (
            lambda c:c['projective_fibres'].pop(),
            lambda c:c['projective_fibres'].reverse(),
            lambda c:c['projective_fibres'][0]['coefficients'].__setitem__(0,True),
            lambda c:c['projective_fibres'][0]['fibre'].__setitem__('node_limit',100000),
            lambda c:c['replacement_equations'][0].__setitem__('pivot',True),
            lambda c:c['relation_basis'][0].__setitem__(1,2),
            lambda c:c['kernel_fibre'].__setitem__('points',[])):
            c=copy.deepcopy(self.three);mutate(c);self.assertFalse(verify_subgroup_preimage(c))

    def test_budget_failure_and_invalid_contracts(self):
        E=self.E
        for prime in (0,1,4,6,11,True,'2'):
            with self.assertRaises(ValueError):E.subgroup_preimage([],prime)
        with self.assertRaises(ValueError):E.subgroup_preimage([None]*5)
        with self.assertRaises(WorkLimit):E.subgroup_preimage(self.three_source,3,node_limit=self.three['root_nodes']-1)
        self.assertFalse(verify_subgroup_preimage(self.three,node_limit=self.three['root_nodes']-1))
        self.assertFalse(verify_subgroup_preimage(self.three,work_limit=1))

    def test_cold_service_registration_and_operation(self):
        with tempfile.TemporaryDirectory() as tmp:
            db=Path(tmp)/'objects.sqlite'
            with Catalogue(db) as cat:cat.register('elliptic_curve',self.E.specification,'E')
            with Catalogue(db) as cat:
                c=dispatch(cat,dict(op='call',object='E',method='subgroup_preimage',args=dict(points=[encode_point(h) for h in self.three_source],prime=3)))
            with Catalogue(db) as cat:
                answer=dispatch(cat,dict(op='verify_elliptic_subgroup_preimage',args=dict(cert=c)))
            self.assertTrue(answer['valid']);self.assertFalse(answer['execution_verified'])


if __name__=='__main__':unittest.main()
