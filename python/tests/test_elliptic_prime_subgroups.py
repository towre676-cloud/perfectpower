import copy,json,tempfile,unittest
from pathlib import Path
from unittest.mock import patch
from perfectpower.elliptic_arithmetic import EllipticCurve,encode_point
from perfectpower.elliptic_lattice_verifier import verify_subgroup_presentation,verify_saturation_presentation
from perfectpower.elliptic_subgroup_verifier import verify_subgroup_preimage
from perfectpower.elliptic_saturation_verifier import verify_saturation
from perfectpower.elliptic_prime_division import rational_prime_division
from perfectpower.elliptic_prime_division_verifier import verify_prime_division
from perfectpower.catalogue import Catalogue
from perfectpower.query_service import dispatch
from perfectpower.divisor_square import WorkLimit

class PrimeSubgroups(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.E=EllipticCurve([-4,1]);cls.P=cls.E.checked([0,1]);cls.Q=cls.E.checked([2,1])
        cls.hidden={}
        for p in (5,7):
            points=[cls.E.add(cls.P,cls.Q),cls.E.add(cls.E.mul(cls.P,p-1),cls.E.neg(cls.Q))]
            cls.hidden[p]=cls.E.subgroup_presentation(points,p)
        cls.rank1=EllipticCurve([0,0,1,-1,0]);cls.A=cls.rank1.checked([0,0])
        cls.saturation=cls.rank1.saturation_presentation([cls.rank1.mul(cls.A,35)])

    def test_hidden_relations_and_all_projective_lines(self):
        for p,c in self.hidden.items():
            core=c['preimage'];self.assertEqual(len(core['projective_fibres']),p+1)
            self.assertEqual(core['relation_basis'],[[1,1]])
            for row in core['projective_fibres']:
                self.assertEqual(bool(row['fibre']['points']),row['coefficients']==[1,1])
            self.assertEqual(core['replacement_points'][0],encode_point(self.P))
            self.assertTrue(verify_subgroup_preimage(core));self.assertTrue(verify_subgroup_presentation(c))

    def test_normal_forms_and_original_containment(self):
        for p,c in self.hidden.items():
            a=c['lattice'];self.assertEqual(a['row_hermite'],[[1,1],[0,p]])
            self.assertEqual(a['smith_diagonal'],[1,p]);self.assertEqual(a['source_inclusion'],[[p,-1],[0,1]])
            self.assertEqual(a['coefficient_lattice_index'],p);self.assertEqual(a['residue_relation_cardinality'],p)
            self.assertIsNone(c['actual_subgroup_index'])

    def test_mixed_saturation_and_joint_reclosure(self):
        c=self.saturation;s=c['saturation'];self.assertEqual(s['status'],'closed')
        self.assertEqual(s['closed_primes'],[5,7]);self.assertEqual(s['generators'],[['0','0']])
        self.assertEqual([a['preimage']['prime'] for a in s['stages']],[5,5,7,5,7])
        self.assertTrue(verify_saturation(s));self.assertTrue(verify_saturation_presentation(json.loads(json.dumps(c))))
        self.assertIsNone(c['actual_subgroup_indices'])

    def test_dependent_points_do_not_forge_group_index(self):
        for p in (5,7):
            c=self.rank1.subgroup_presentation([self.A,self.A],p)
            self.assertEqual(c['preimage']['relation_dimension'],1)
            self.assertEqual(c['preimage']['generators'],[['0','0']])
            self.assertEqual(c['lattice']['residue_relation_cardinality'],p)
            self.assertIsNone(c['actual_subgroup_index']);self.assertTrue(verify_subgroup_presentation(c))

    def test_empty_input_and_rational_five_seven_torsion(self):
        for E,p,count in ((EllipticCurve([0,-1,1,0,0]),5,5),(EllipticCurve([1,-1,1,-3,3]),7,7)):
            c=E.subgroup_presentation([],p)
            self.assertEqual(len(c['preimage']['kernel_fibre']['points']),count)
            self.assertEqual(len(c['preimage']['generators']),count-1)
            self.assertEqual(c['lattice']['row_hermite'],[]);self.assertTrue(verify_subgroup_presentation(c))
            s=E.saturation_presentation([],primes=[p],coefficient_bound=4)
            self.assertEqual(s['saturation']['status'],'closed');self.assertTrue(verify_saturation_presentation(s))

    def test_identity_generators_and_old_primes(self):
        for p in (2,3,5,7):
            c=self.rank1.subgroup_presentation([None,None],p)
            self.assertEqual(c['lattice']['smith_diagonal'],[1,1])
            self.assertEqual(c['preimage']['generators'],[]);self.assertTrue(verify_subgroup_presentation(c))

    def test_step_limits_and_inconclusive_membership(self):
        c=self.rank1.saturation_presentation([self.rank1.mul(self.A,35)],max_steps=1)
        self.assertEqual(c['saturation']['status'],'step-limit');self.assertTrue(verify_saturation_presentation(c))
        c=self.rank1.saturation_presentation([self.A],max_steps=1,coefficient_bound=0)
        self.assertEqual(c['saturation']['status'],'step-limit');self.assertEqual(c['saturation']['closed_primes'],[])
        self.assertTrue(verify_saturation_presentation(c))

    def test_local_obstructions_replayed_without_discovery(self):
        for bad in (None,[],7):self.assertFalse(verify_prime_division(bad))
        c=rational_prime_division(self.E,self.hidden[7]['preimage']['source_points'][0],7)
        self.assertEqual(c['method'],'local_root_obstruction')
        with patch('perfectpower.elliptic_prime_division.local_root_obstruction',side_effect=AssertionError('discovery')):
            self.assertTrue(verify_prime_division(c))
        q=copy.deepcopy(c);q['local_obstruction']['prime']=True;self.assertFalse(verify_prime_division(q))
        q=copy.deepcopy(c);q['local_obstruction']['root_residues'].append(0);self.assertFalse(verify_prime_division(q))
        q=copy.deepcopy(c);q['local_obstruction']['extra']=0;self.assertFalse(verify_prime_division(q))

    def test_discovery_free_presentations(self):
        with patch('perfectpower.elliptic_lattice_presentation.lattice_data',side_effect=AssertionError('producer')), patch('perfectpower.elliptic_subgroups.row_basis',side_effect=AssertionError('producer')):
            self.assertTrue(verify_subgroup_presentation(self.hidden[7]))
            self.assertTrue(verify_saturation_presentation(self.saturation))

    def test_lattice_corruptions_rejected(self):
        mutations=[lambda c:c['lattice']['row_hermite'][0].__setitem__(1,2),
                   lambda c:c['lattice']['smith_left'][0].__setitem__(0,2),
                   lambda c:c['lattice']['smith_right'][0].__setitem__(1,0),
                   lambda c:c['lattice']['smith_diagonal'].__setitem__(0,True),
                   lambda c:c['lattice']['source_inclusion'][0].__setitem__(1,1),
                   lambda c:c.__setitem__('actual_subgroup_index',7),
                   lambda c:c['preimage']['projective_fibres'].pop()]
        for f in mutations:
            c=copy.deepcopy(self.hidden[7]);f(c);self.assertFalse(verify_subgroup_presentation(c))
        c=copy.deepcopy(self.saturation);c['stage_lattices'].pop();self.assertFalse(verify_saturation_presentation(c))

    def test_service_and_cold_reload(self):
        with tempfile.TemporaryDirectory() as tmp:
            with Catalogue(Path(tmp)/'objects.sqlite') as cat:cat.register('elliptic_curve',self.rank1.specification,'E')
            with Catalogue(Path(tmp)/'objects.sqlite') as cat:
                c=dispatch(cat,{'op':'call','object':'E','method':'subgroup_presentation','args':{'points':[encode_point(self.rank1.mul(self.A,7))],'prime':7}})
                a=dispatch(cat,{'op':'verify_elliptic_subgroup_presentation','args':{'cert':c}})
            self.assertTrue(a['valid']);self.assertFalse(a['execution_verified'])

    def test_actual_indices_require_independence_and_coordinates(self):
        from perfectpower.elliptic_lattice_presentation import subgroup_index
        from perfectpower.elliptic_lattice_verifier import verify_subgroup_index
        for p,c in self.hidden.items():
            q=subgroup_index(c,[self.P,self.Q],[[1,1],[p-1,-1]],[[1,0],[p-1,-1]])
            self.assertEqual(q['actual_subgroup_index'],p);self.assertTrue(verify_subgroup_index(q))
            bad=copy.deepcopy(q);bad['actual_subgroup_index']=1;self.assertFalse(verify_subgroup_index(bad))
            bad=copy.deepcopy(q);bad['source_coordinates'][0][0]=2;self.assertFalse(verify_subgroup_index(bad))
            bad=copy.deepcopy(q);bad['independence']['independent']=True;bad['basis'].reverse();self.assertFalse(verify_subgroup_index(bad))
        with self.assertRaises(ValueError):
            subgroup_index(self.hidden[5],[self.P,self.P],[[1,1],[4,-1]],[[1,0],[4,-1]])

    def test_actual_index_at_every_joint_saturation_stage(self):
        from perfectpower.elliptic_lattice_presentation import subgroup_index,from_preimage
        indices=[];coordinates=[(35,7),(7,7),(7,1),(1,1),(1,1)]
        for stage,(a,b) in zip(self.saturation['saturation']['stages'],coordinates):
            cert=subgroup_index(from_preimage(stage['preimage']),[self.A],[[a]],[[b]])
            indices.append(cert['actual_subgroup_index'])
        self.assertEqual(indices,[5,1,7,1,1])

    def test_invalid_primes_and_shared_budgets(self):
        for p in (4,6,11,True):
            with self.assertRaises(ValueError):self.rank1.subgroup_presentation([],p)
        with self.assertRaises(WorkLimit):self.rank1.subgroup_presentation([self.A],7,node_limit=1)
        self.assertFalse(verify_subgroup_presentation(self.hidden[7],node_limit=1))
        self.assertFalse(verify_saturation_presentation(self.saturation,work_limit=1))
        c=copy.deepcopy(self.hidden[7]);c['preimage']['prime']=5;self.assertFalse(verify_subgroup_presentation(c))

if __name__=='__main__':unittest.main()
