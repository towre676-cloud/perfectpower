import copy,unittest
from perfectpower.residue_atlas_product import *
from perfectpower.query_service import dispatch

PARABOLA=[[1,0,1],[-1,2,0]]


class ProductTests(unittest.TestCase):
    def packet(self,limit=4096):return product_packet(PARABOLA,[[2,2],[3,2]],explicit_limit=limit)

    def test_canonical_complete_roots(self):
        p=self.packet();m=p['modulus'];expected=[[x,y] for x in range(m) for y in range(m) if (y-x*x)%m==0]
        self.assertEqual(p['roots'],expected);self.assertEqual(len(expected),p['combination_count']);self.assertTrue(verify_product(p))

    def test_factored_representation_retains_every_combination(self):
        p=self.packet(1);self.assertIsNone(p['roots']);self.assertEqual(p['representation'],'factored');self.assertEqual(p['combination_count'],36);self.assertTrue(verify_product(p))

    def test_explicit_and_factored_populations_equal(self):
        b=[[-19,21],[-22,17]];self.assertEqual(product_population(self.packet(),b)['count'],product_population(self.packet(1),b)['count'])
        self.assertEqual(product_scan(self.packet(),b),product_scan(self.packet(1),b))

    def test_large_factored_pruning(self):
        p=product_packet(PARABOLA,[[q,1] for q in [2,3,5,7,11,13,17,19]],explicit_limit=1)
        self.assertEqual(p['combination_count'],9699690)
        self.assertEqual(product_population(p,[[-10,10],[-10,10]],work_limit=1000)['count'],7)
        self.assertEqual(len(product_scan(p,[[-10,10],[-10,10]],work_limit=1000)['points']),7)

    def test_empty_last_factor_short_circuit(self):
        p=product_packet([[510510,0,0]],[[q,1] for q in [2,3,5,7,11,13,17,19]],explicit_limit=1)
        self.assertEqual(p['roots'],[]);self.assertTrue(verify_product(p))
        self.assertEqual(product_population(p,[[-10**12,10**12],[-10**12,10**12]],work_limit=1)['count'],0)

    def test_shared_prime_rejected(self):
        with self.assertRaises(ValueError):product_packet(PARABOLA,[[2,2],[2,3]])

    def test_mixed_source_rejected(self):
        with self.assertRaises(ValueError):compose_atlases([atlas_packet(PARABOLA,2,2),atlas_packet([[1,0,1]],3,2)])

    def test_input_evidence_copied(self):
        locals=[atlas_packet(PARABOLA,2,2),atlas_packet(PARABOLA,3,2)];p=compose_atlases(locals)
        locals[0]['terms'][0][0]+=1;self.assertTrue(verify_product(p))

    def test_source_substitution_rejected(self):
        p=self.packet();p['terms'][0][0]+=1;self.assertFalse(verify_product(p))

    def test_omitted_combination_rejected(self):
        p=self.packet();p['roots'].pop();self.assertFalse(verify_product(p))

    def test_duplicate_combination_rejected(self):
        p=self.packet();p['roots'][-1]=p['roots'][0];self.assertFalse(verify_product(p))

    def test_changed_period_rejected(self):
        p=self.packet();p['modulus']+=1;self.assertFalse(verify_product(p))

    def test_omitted_local_branch_rejected(self):
        p=self.packet();p['locals'][0]['levels'][0]['roots'].pop();self.assertFalse(verify_product(p))

    def test_changed_representation_rejected(self):
        p=self.packet();p['representation']='factored';self.assertFalse(verify_product(p))

    def test_bool_coordinate_rejected(self):
        p=self.packet();p['roots'][0][0]=False;self.assertFalse(verify_product(p))

    def test_contains_arbitrary_signed_coordinates(self):
        p=self.packet(1)
        for z in [[-3,9],[0,0],[3,9]]:self.assertTrue(product_contains(p,z))
        self.assertFalse(product_contains(p,[3,8]))

    def test_signed_box_count_and_addressing(self):
        p=self.packet(1);b=[[-8,9],[-9,8]];expected=[[x,y] for x in range(-8,10) for y in range(-9,9) if (y-x*x)%p['modulus']==0]
        count=product_population(p,b)['count'];self.assertEqual(count,len(expected));seen=[]
        for i in range(count):
            z=product_select(p,b,i);self.assertEqual(product_rank(p,b,z),i);seen.append(z)
        self.assertEqual(sorted(seen),expected)

    def test_large_index_roundtrip(self):
        p=self.packet(1);b=[[-10**12,10**12],[-10**12,10**12]];n=product_population(p,b)['count']
        for i in [0,n//2,n-1]:self.assertEqual(product_rank(p,b,product_select(p,b,i)),i)

    def test_work_budget_rejects_without_partial_count(self):
        with self.assertRaises(ValueError):product_population(self.packet(1),[[-10**12,10**12],[-10**12,10**12]],work_limit=2)

    def test_scan_budget_rejects_before_source_scan(self):
        with self.assertRaises(ValueError):product_scan(self.packet(1),[[-10**12,10**12],[-10**12,10**12]])

    def test_outside_rank_and_select(self):
        p=self.packet();b=[[0,0],[0,0]]
        with self.assertRaises(IndexError):product_select(p,b,-1)
        with self.assertRaises(IndexError):product_select(p,b,1)
        with self.assertRaises(ValueError):product_rank(p,b,[1,1])

    def test_single_factor(self):
        p=product_packet(PARABOLA,[[2,2]]);self.assertTrue(verify_product(p));self.assertEqual(p['modulus'],4)

    def test_all_actual_source_points_retained(self):
        p=product_packet([[1,0,2],[-1,3,0],[2,0,0]],[[2,3],[3,2]],explicit_limit=1)
        self.assertEqual(product_scan(p,[[-10,10],[-10,10]])['points'],[[3,-5],[3,5]])

    def test_native_budget_explicit(self):
        p=product_packet(PARABOLA,[[2,3],[3,2],[5,3]])
        with self.assertRaises(ValueError):native_product(p,[[0,0],[0,0]])

    def test_query_operations(self):
        p=dispatch(None,{'op':'residue_atlas_product','args':{'terms':PARABOLA,'factors':[[2,2],[3,2]],'explicit_limit':1}})
        self.assertTrue(dispatch(None,{'op':'verify_residue_atlas_product','args':{'packet':p}})['valid'])
        self.assertTrue(dispatch(None,{'op':'residue_product_contains','args':{'packet':p,'point':[3,9]}}))
        self.assertEqual(dispatch(None,{'op':'residue_product_rank','args':{'packet':p,'bounds':[[0,0],[0,0]],'point':[0,0]}}),0)
