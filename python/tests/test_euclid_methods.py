import unittest
import random
from fractions import Fraction as Q
from math import gcd,isqrt
from copy import deepcopy
from perfectpower.euclid_descent import resultant_certificate,check_resultant,compile_descent,check_descent,classify_input,gcd_receipt,finite_descent_population
from perfectpower.euclid_geometry import segment_intersection,point_segment_distance_squared,voronoi_cells,nearest_sites,string_disk_contacts,orientation
from perfectpower.euclid_exact import QuadraticSurd,sqrt_continued_fraction,pell_from_cf,sqrt_exhaustion,check_exhaustion,euclidean_gcd,check_gcd,check_cf,isolate_root,check_root_isolation
from perfectpower.core import integer_power_root
from perfectpower.divisor_square import WorkLimit


class DescentTests(unittest.TestCase):
    def test_resultants_and_gcds(self):
        r=random.Random(1337)
        try:
            import sympy as S
        except ImportError:S=None
        for _ in range(100):
            a=[r.randint(-5,5) for _ in range(r.randint(2,5))];b=[r.randint(-5,5) for _ in range(r.randint(2,5))]
            a[-1]=r.choice([-3,-1,1,2]);b[-1]=r.choice([-2,-1,1,3])
            try:p=resultant_certificate(a,b)
            except ValueError:continue
            self.assertTrue(check_resultant(p,a,b))
            if S:
                x=S.Symbol('x');self.assertEqual(p['resultant'],int(S.resultant(sum(c*x**i for i,c in enumerate(a)),sum(c*x**i for i,c in enumerate(b)),x)))
            for n in range(-10,11):
                q=gcd_receipt(p,n);self.assertEqual(q['evaluated_bezout'],p['resultant']);self.assertEqual(p['resultant']%q['gcd'],0)
    def test_signed_complete_branches(self):
        for a,b in [([0,1],[2,1]),([0,1],[1,1]),([-2,0,1],[3,1]),([1,1],[-1,1]),([0,-1],[2,-1])]:
            for d in range(2,6):
                p=compile_descent(a,b,d);self.assertTrue(check_descent(p))
                for n in range(-100,101):
                    q=classify_input(p,n);v=q['values'][0]*q['values'][1]
                    self.assertEqual(q['status']!='NOT_A_POWER',integer_power_root(v,d) is not None)
                    if q['status']=='BRANCH':
                        branch=p['branches'][q['branch']];u,w=q['factor_roots']
                        self.assertEqual(branch['left_coefficient']*u**d,q['values'][0])
                        self.assertEqual(branch['right_coefficient']*w**d,q['values'][1])
    def test_rejections(self):
        p=resultant_certificate([0,1],[2,1]);p['u'][0]+=1
        with self.assertRaises(ValueError):check_resultant(p,[0,1],[2,1])
        with self.assertRaises(ValueError):resultant_certificate([0,1],[0,0,1])
        with self.assertRaises(WorkLimit):compile_descent([0,1],[30,1],5,branch_limit=10)
        p=compile_descent([0,1],[2,1]);p['branches'].pop()
        with self.assertRaises(ValueError):check_descent(p)
    def test_population(self):
        p=compile_descent([0,1],[2,1]);pop=finite_descent_population(p,-20,20)
        expected=[n for n in range(-20,21) if integer_power_root(n*(n+2),2) is not None]
        self.assertEqual(pop.count(),len(expected))
        self.assertEqual([pop.select(i)[0] for i in range(pop.count())],expected)


class GeometryTests(unittest.TestCase):
    def test_contacts_and_degeneracies(self):
        self.assertEqual(segment_intersection([0,0],[2,2],[0,2],[2,0]),{'kind':'PROPER','points':[['1','1']]})
        self.assertEqual(segment_intersection([0,0],[2,0],[1,0],[3,0])['kind'],'OVERLAP')
        self.assertEqual(segment_intersection([0,0],[0,0],[0,0],[1,1])['kind'],'TOUCH')
        self.assertEqual(segment_intersection([0,0],[1,0],[2,0],[3,0])['kind'],'DISJOINT')
        q=point_segment_distance_squared([1,1],[0,0],[2,0]);self.assertEqual(q['squared_distance'],'1')
        q=point_segment_distance_squared([3,1],[0,0],[2,0]);self.assertEqual(q['squared_distance'],'2')
        q=string_disk_contacts([[0,0],[2,0]],{'ball':{'center':[1,1],'radius':1}});self.assertTrue(q['contacts'][0]['tangent'])
        with self.assertRaises(ValueError):orientation([0.0,0],[1,0],[0,1])
    def test_string_contact_and_winding_integration(self):
        from perfectpower.euclid_geometry import string_geometry
        path=[[0,0],[4,0],[4,4],[0,4],[0,0]]
        objects={'inside':{'center':[2,2],'radius':'1/2'},'touch':{'center':[2,1],'radius':1}}
        p=string_geometry(path,objects)
        self.assertTrue(p['objects']['inside']['whole_disk_topologically_enclosed'])
        self.assertFalse(p['objects']['touch']['whole_disk_topologically_enclosed'])
        self.assertEqual(p['objects']['touch']['winding'],1)
        p=string_geometry(path[:-1],objects);self.assertFalse(p['closed'])
        self.assertIsNone(p['objects']['inside']['winding'])
    def test_precision_stress(self):
        big=2**60
        self.assertEqual(orientation([0,0],[big,big-1],[big+1,big]),1)
        self.assertEqual(float(big)*float(big)-float(big-1)*float(big+1),0)
        self.assertEqual(nearest_sites({'left':[big,0],'right':[big+1,0]},[f'{4*big+1}/4',0])['sites'],['left'])
    def test_voronoi_ties_and_boundaries(self):
        sites={'a':[0,0],'b':[2,0],'duplicate':[0,0]};p=voronoi_cells(sites,[[-1,-1],[3,1]])
        self.assertEqual(p['cells']['a']['vertices'],p['cells']['duplicate']['vertices'])
        self.assertEqual(nearest_sites(sites,[1,0])['sites'],['a','b','duplicate'])
        self.assertEqual(nearest_sites(sites,[0,0])['sites'],['a','duplicate'])
        for name,cell in p['cells'].items():
            for point in cell['vertices']:self.assertIn(name,nearest_sites(sites,point)['sites'])
    def test_random_voronoi_vertices_and_segment_symmetry(self):
        r=random.Random(42)
        for _ in range(40):
            sites={str(i):[r.randrange(-5,6),r.randrange(-5,6)] for i in range(5)}
            p=voronoi_cells(sites,[[-3,-3],[3,3]])
            for name,cell in p['cells'].items():
                for point in cell['vertices']:self.assertIn(name,nearest_sites(sites,point)['sites'])
            a,b,c,d=[[r.randrange(-5,6),r.randrange(-5,6)] for _ in range(4)]
            self.assertEqual(segment_intersection(a,b,c,d),segment_intersection(c,d,a,b))


class ExactTests(unittest.TestCase):
    def test_surd_field_and_order(self):
        s=QuadraticSurd(2);self.assertEqual((s*s).compare(2),0)
        self.assertEqual((s/s).compare(1),0);self.assertEqual(s.floor(),1);self.assertEqual((-s).floor(),-2)
        self.assertGreater((s-1).sign(),0);self.assertLess((s-2).sign(),0)
        self.assertGreater((2-s).sign(),0);self.assertLess((1-s).sign(),0)
        self.assertEqual(QuadraticSurd(2,Q(3,2),Q(0)).floor(),1)
        with self.assertRaises(ValueError):QuadraticSurd(4)
        with self.assertRaises(ValueError):s+QuadraticSurd(3)
        with self.assertRaises(ZeroDivisionError):QuadraticSurd(2,0,0).inverse()
    def test_continued_fractions_and_pell(self):
        from perfectpower.bounded_pell import pell_unit
        for D in range(2,101):
            if isqrt(D)**2==D:continue
            cf=sqrt_continued_fraction(D);self.assertTrue(check_cf(cf));unit=pell_from_cf(D)
            self.assertEqual(tuple(unit['unit']),pell_unit(D))
            p,q=unit['unit'];self.assertEqual(p*p-D*q*q,1)
        self.assertEqual(sqrt_continued_fraction(2)['period'],[2])
        self.assertEqual(pell_from_cf(61)['unit'],[1766319049,226153980])
        p=sqrt_continued_fraction(7);p['period'][0]+=1
        with self.assertRaises(ValueError):check_cf(p)
    def test_gcd_signs_zero(self):
        for a in range(-15,16):
            for b in range(-15,16):
                p=euclidean_gcd(a,b);self.assertEqual(p['gcd'],gcd(a,b));self.assertTrue(check_gcd(p))
    def test_exhaustion_and_tampering(self):
        for x in [0,1,2,3,4,Q(2,3),10000]:
            p=sqrt_exhaustion(x,'1/1000000');self.assertTrue(check_exhaustion(p));lo,hi=map(Q,(p['lower'],p['upper']))
            self.assertLessEqual(lo*lo,x);self.assertGreaterEqual(hi*hi,x);self.assertLessEqual(hi-lo,Q(1,1000000))
            self.assertLessEqual(hi-lo,Q(p['halving_bound']))
        p=sqrt_exhaustion(2,'1/100');p['upper']='1'
        with self.assertRaises(ValueError):check_exhaustion(p)
        with self.assertRaises(WorkLimit):sqrt_exhaustion(2,'1/1000000',step_limit=2)
    def test_sturm_exhaustion_repeated_and_irrational(self):
        for cs,lo,hi in [([-2,0,1],1,2),([4,0,-4,0,1],1,2),([-1,-1,0,1],1,2),([-1,3,-3,1],0,2)]:
            p=isolate_root(cs,lo,hi,'1/1000000');self.assertTrue(check_root_isolation(p))
            self.assertLessEqual(Q(p['interval'][1])-Q(p['interval'][0]),Q(1,1000000))
        with self.assertRaises(ValueError):isolate_root([-1,0,1],-2,2,'1/100')
        with self.assertRaises(ValueError):isolate_root([-1,0,1],1,2,'1/100')


if __name__=='__main__':unittest.main()
