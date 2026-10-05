import unittest
from itertools import permutations, product
from perfectpower.weyl_scaffold import chamber, orbit_size, search, symmetry_defect

class WeylTests(unittest.TestCase):
    def test_orbits_independent(self):
        for v in [(0,0,0,0,0),(1,1,0,0,0),(1,2,3,4,5),(1,-1,2,2,0)]:
            actual={tuple(s*t for s,t in zip(sign,p)) for p in permutations(v) for sign in product((-1,1),repeat=5)}
            self.assertEqual(len(actual),orbit_size(v))
            self.assertEqual(len({chamber(x) for x in actual}),1)
    def test_labeled_orbit_not_equivalent(self):
        r=search([0,1],[[1,2]],[1])
        self.assertEqual(r['winners'],[['1','0']])
        self.assertEqual(r['tested'],4)
    def test_every_tie(self):
        self.assertEqual(search([-1,0,1],[[1,1]],[0])['winners'],[['-1','1'],['0','0'],['1','-1']])
    def test_recovery(self):
        rows=[[int(i==j) for j in range(5)] for i in range(5)]
        r=search(['-1/3','0','1/12','1/5'],rows,['1/12','-1/3',0,0,'1/5'])
        self.assertEqual(r['score'],'0'); self.assertEqual(len(r['winners']),1)
    def test_symmetry(self):
        self.assertTrue(symmetry_defect([[1,0],[0,1]],[0,0])['invariant'])
        self.assertFalse(symmetry_defect([[1,0],[0,1]],[1,0])['invariant'])
        self.assertFalse(symmetry_defect([[1,0],[0,2]],[0,0])['invariant'])
    def test_guards(self):
        for kw in [{'candidate_limit':1},{'support':-1},{'weights':[-1]},{'axis_penalties':[-1]}]:
            with self.assertRaises(ValueError): search([0,1],[[1]],[1],**kw)
        with self.assertRaises(ValueError): search([0.1],[[1]],[1])
