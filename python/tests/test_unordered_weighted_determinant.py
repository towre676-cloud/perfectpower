import copy
import unittest
from perfectpower.weighted_gram_determinant import weighted_determinant,verify_weighted_determinant

class WeightedTests(unittest.TestCase):
    def test_real_identity_each_subset_once(self):
        p=weighted_determinant([[1,0],[0,1],[1,1]],[2,3,5])
        self.assertEqual(p['determinant'],['31','0']);self.assertEqual(p['subset_count'],3)
        self.assertEqual([t['rows'] for t in p['terms']],[[0,1],[0,2],[1,2]])
        self.assertTrue(verify_weighted_determinant(p))

    def test_complex_entries_and_weights(self):
        p=weighted_determinant([[[1,1],2],[3,[0,-1]],[[2,-1],[1,2]]],[[1,1],0,[-2,3]])
        self.assertEqual(p['determinant'],p['unordered_sum']);self.assertFalse(p['nonnegative_real_weights'])
        self.assertTrue(verify_weighted_determinant(p))

    def test_empty_zero_and_deficient(self):
        for matrix,weights,n,value in [([],[],0,['1','0']),([],[],2,['0','0']),([[],[]],[1,2],0,['1','0']),([[1,2]],[1],2,['0','0']),([[1,2],[2,4]],[1,1],2,['0','0'])]:
            p=weighted_determinant(matrix,weights,columns=n);self.assertEqual(p['determinant'],value);self.assertTrue(verify_weighted_determinant(p))

    def test_zero_weights_select_supported_bases(self):
        p=weighted_determinant([[1,0],[0,1],[1,1]],[1,0,2]);self.assertEqual(p['nonzero_supported_minors'],[[0,2]])
        self.assertTrue(p['positive_determinant'])
        q=weighted_determinant([[1,0],[0,1]],[1,0]);self.assertFalse(q['positive_determinant'])

    def test_permutation_invariance(self):
        p=weighted_determinant([[1,2],[3,4],[5,6]],['1/2',2,3])
        q=weighted_determinant([[5,6],[1,2],[3,4]],[3,'1/2',2]);self.assertEqual(p['determinant'],q['determinant'])

    def test_tampering_and_budgets(self):
        p=weighted_determinant([[1],[2]],[1,2])
        for key,value in [('determinant',['0','0']),('subset_count',True),('unexpected',1)]:
            q=copy.deepcopy(p);q[key]=value;self.assertFalse(verify_weighted_determinant(q))
        with self.assertRaises(ValueError):weighted_determinant([[True]],[1])
        with self.assertRaises(ValueError):weighted_determinant([[1]*8]*16,[1]*16)

if __name__=='__main__':unittest.main()
