import copy,json,unittest
from pathlib import Path
from unittest.mock import patch
from perfectpower.elliptic_arithmetic import EllipticCurve,encode_point
from perfectpower.elliptic_prime_division import rational_prime_division,rational_division_general,odd_division_polynomials,division_equation
from perfectpower.elliptic_prime_division_verifier import verify_prime_division,verify_general_division,silverman_division
from perfectpower.elliptic_lattice_verifier import verify_subgroup_presentation,verify_saturation_presentation,verify_subgroup_index
from perfectpower.elliptic_lattice_presentation import subgroup_index
from perfectpower.divisor_square import WorkLimit
from perfectpower import polyalg as A

ROOT=Path(__file__).resolve().parents[2]

class ElevenThirteen(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.E=EllipticCurve([0,0,1,-1,0]);cls.P=cls.E.checked([0,0]);cls.division={}
        for p in (11,13):cls.division[p]=rational_prime_division(cls.E,cls.E.mul(cls.P,p),p)
        cls.saturation=cls.E.saturation_presentation([cls.E.mul(cls.P,143)],primes=[11,13])

    def test_complete_single_fibres_and_independent_recurrence(self):
        for p,c in self.division.items():
            self.assertEqual(c['points'],[['0','0']]);self.assertTrue(verify_prime_division(json.loads(json.dumps(c))))
            psi,phi=odd_division_polynomials(self.E,p)
            self.assertEqual(A.degree(psi),(p*p-1)//2)
            self.assertEqual(A.degree(division_equation(self.E,p,self.E.mul(self.P,p))),p*p)
            self.assertEqual((psi,phi),silverman_division(self.E,p))
        for E in (EllipticCurve([-4,1]),EllipticCurve([1,0,1,4,-6])):
            for p in (11,13):
                psi,phi=odd_division_polynomials(E,p)
                corrected=A.add(phi,A.scale(A.power(psi,2),-E.cubic[2]/3))
                self.assertEqual((psi,corrected),silverman_division(E,p))

    def test_composed_fibre_and_six_prime_joint_closure(self):
        c=rational_division_general(self.E,self.E.mul(self.P,143),143)
        self.assertEqual(c['factors'],[11,13]);self.assertEqual(c['points'],[['0','0']]);self.assertTrue(verify_general_division(c))
        s=self.saturation['saturation'];self.assertEqual(s['status'],'closed');self.assertEqual(s['closed_primes'],[11,13]);self.assertEqual(s['generators'],[['0','0']])
        self.assertEqual([c['preimage']['prime'] for c in s['stages']],[11,11,13,11,13]);self.assertTrue(verify_saturation_presentation(self.saturation))
        all_primes=self.E.saturation_presentation([self.P],primes=[2,3,5,7,11,13])
        self.assertEqual(all_primes['saturation']['closed_primes'],[2,3,5,7,11,13]);self.assertTrue(verify_saturation_presentation(all_primes))

    def test_hidden_mixed_relation_and_actual_index(self):
        # Small determinant-p matrices hide divisibility in a mixed row.
        E=EllipticCurve([-4,1]);P=E.checked([0,1]);Q=E.checked([2,1])
        for p,source,relation,anchor in ((11,[[3,1],[1,4]],[[1,8]],[1,3]),
                                       (13,[[3,1],[-1,4]],[[1,3]],[0,1])):
            point=lambda row:E.add(E.mul(P,row[0]),E.mul(Q,row[1]))
            # Supply a known candidate only; exact multiplication and the
            # complete torsion certificate still establish the whole fibre.
            candidate=point(anchor)[0]
            hint=lambda polynomial: [candidate] if A.evaluate(polynomial,candidate)==0 else []
            with patch('perfectpower.elliptic_prime_division.discovered_roots',side_effect=hint):
                C=E.subgroup_presentation([point(row) for row in source],p)
            core=C['preimage'];self.assertEqual(len(core['projective_fibres']),p+1)
            self.assertEqual(core['relation_basis'],relation)
            self.assertEqual(core['replacement_points'][0],encode_point(point(anchor)))
            self.assertTrue(verify_subgroup_presentation(C))
            D=subgroup_index(C,[P,Q],source,[anchor,source[1]])
            self.assertEqual(D['actual_subgroup_index'],p);self.assertTrue(verify_subgroup_index(D))

    def test_no_discovery_in_replay_and_corruptions(self):
        with patch('perfectpower.elliptic_prime_division.discovered_roots',side_effect=AssertionError):
            for c in self.division.values():self.assertTrue(verify_prime_division(c))
        for c in self.division.values():
            for key,value in [('prime',17),('anchor',None),('root_nodes',0),('points',[]),('complete',False)]:
                b=copy.deepcopy(c);b[key]=value;self.assertFalse(verify_prime_division(b))
        for p in (17,15,True):
            with self.assertRaises(ValueError):rational_prime_division(self.E,None,p)
        with self.assertRaises(WorkLimit):rational_prime_division(self.E,self.E.mul(self.P,13),13,node_limit=1)

    def test_empty_fibre_and_finite_group_obstruction(self):
        for p in (11,13):
            c=rational_prime_division(self.E,self.P,p,local_obstructions=True)
            self.assertEqual(c['points'],[]);self.assertTrue(verify_prime_division(c))
            self.assertEqual(c['method'],'good_reduction_obstruction')

    def test_good_reduction_kernel_and_corruptions(self):
        for p in (11,13):
            c=rational_prime_division(self.E,None,p,local_obstructions=True)
            self.assertEqual(c['points'],[None]);self.assertEqual(c['root_nodes'],0)
            self.assertEqual(c['torsion_certificate']['schema'],'pp-prime-kernel-good-reduction/1')
            self.assertTrue(verify_prime_division(c))
            for key,value in [('prime',p),('group_order',0),('schema','unsupported')]:
                b=copy.deepcopy(c);b['torsion_certificate'][key]=value;self.assertFalse(verify_prime_division(b))
        from perfectpower.elliptic_reduction import trivial_prime_kernel
        self.assertIsNone(trivial_prime_kernel(EllipticCurve([0,-1,1,-10,-20]),5))

    def test_rank_intervals_and_point_witnesses_are_distinct(self):
        c=json.loads((ROOT/'receipts/mordell_frontier.json').read_text())
        self.assertEqual(c['ranks_determined_by_backend_bounds'],457)
        self.assertEqual(c['ranks_with_matching_point_witnesses'],457)
        self.assertEqual(len(c['backend_census_rank_corrections']),12)
        row=next(r for r in c['rank_witness_frontier'] if r['k']==-9257)
        self.assertEqual((row['rank_lower_bound'],row['backend_rank_lower_bound'],row['rank_upper_bound']),(2,2,2))
        self.assertTrue(row['rank_proved']);self.assertTrue(row['backend_rank_determined']);self.assertTrue(row['witness_rank_determined'])
        self.assertFalse(row['lean_rank_proved'])
        self.assertEqual(c['remaining_count'],0)
        closure=next(r for r in c['external_computation_list_closures'] if r['k']==-9257)
        self.assertTrue(closure['complete_basis_by_backend'])
        self.assertTrue(closure['integral_list_complete_by_backend'])
        self.assertFalse(closure['lean_integral_list_proved'])


class SturmDegreeAndCache(unittest.TestCase):
    def test_modular_horner_matches_exact_evaluation(self):
        from perfectpower.elliptic_arithmetic import _evaluate_mod
        import random
        r=random.Random(11013)
        for _ in range(100):
            coefficients=[r.randrange(-100000,100000) for i in range(r.randrange(1,85))]
            x=r.randrange(-1000,1000);modulus=r.randrange(2,10000)
            self.assertEqual(_evaluate_mod(coefficients,x,modulus),int(A.evaluate(coefficients,x))%modulus)

    def test_discovery_keeps_nonintegral_rational_roots(self):
        from perfectpower.elliptic_arithmetic import discovered_roots
        from fractions import Fraction
        for polynomial,expected in (([-1,2],Fraction(1,2)),([0,3],Fraction(0)),([-3,2],Fraction(3,2)),([2,3],Fraction(-2,3))):
            self.assertIn(expected,list(discovered_roots(polynomial)))

    def test_degree_84_and_169_complete_real_root_packets(self):
        from perfectpower.sturm_fibres import root_certificate,verify_roots
        for degree,want in ((84,[-1,1]),(169,[1])):
            c=root_certificate([-1]+[0]*(degree-1)+[1])
            self.assertEqual(c['roots'],want);self.assertTrue(verify_roots(c))
            c['roots']=[];self.assertFalse(verify_roots(c))

    def test_residue_atlas_default_degree_limit_preserved(self):
        from perfectpower.residue_cover import integer_polynomial
        with self.assertRaises(ValueError):integer_polynomial([0]*65+[1])
        self.assertEqual(len(integer_polynomial([0]*84+[1],degree_limit=256)),85)

    def test_cached_complete_root_proof_is_fresh_and_budgeted(self):
        from perfectpower.elliptic_prime_division import _torsion_root_json
        from perfectpower.elliptic_arithmetic import q
        f=tuple(map(q,[-1,0,1]));c=json.loads(_torsion_root_json(f,100000))
        c['roots']=[]
        self.assertEqual(json.loads(_torsion_root_json(f,100000))['roots'],['-1','1'])
        with self.assertRaises(WorkLimit):_torsion_root_json(f,1)

if __name__=='__main__':unittest.main()
