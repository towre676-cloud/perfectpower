import copy,json,unittest
from unittest.mock import patch
from math import isqrt
from itertools import product
from perfectpower.elliptic_arithmetic import EllipticCurve,encode_point
from perfectpower.elliptic_torsion_index import torsion_subgroup_index,verify_torsion_subgroup_index
from perfectpower.pell7_complete import certificate,verify_certificate,orbit,address,solutions
from perfectpower.query_service import dispatch


def packet(E,points,p,basis,torsion,orders,source):
    c=E.subgroup_presentation(points,p)
    candidates={}
    for cs in product(range(-8,9),repeat=len(basis)):
        for ts in product(*(range(n) for n in orders)):
            P=None
            for Q,n in zip(basis+torsion,cs+ts):P=E.add(P,E.mul(Q,n))
            candidates[P]=list(cs+ts)
    coords=[candidates[E.checked(P)] for P in c['preimage']['generators']]
    return torsion_subgroup_index(c,basis,torsion,orders,source,coords)


class TorsionIndices(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.examples=[]
        for curve,p in (([0,-1,1,0,0],5),([1,-1,1,-3,3],7)):
            E=EllipticCurve(curve);c=E.subgroup_presentation([],p)
            T=E.checked(c['preimage']['generators'][0])
            cls.examples.append(packet(E,[],p,[],[T],[p],[]))
        E=EllipticCurve([-1,0]);cls.double=packet(E,[],2,[],[E.checked([0,0]),E.checked([1,0])],[2,2],[])
        E=EllipticCurve([-2,0]);P=E.checked([2,2]);T=E.checked([0,0])
        cls.mixed=packet(E,[E.mul(P,2),T,T],2,[P],[T],[2],[[2,0],[0,1],[0,1]])
        cls.torsion_closed=packet(E,[T,T],2,[],[T],[2],[[1],[1]])
        cls.mixed_odd=[packet(E,[E.mul(P,p),T],p,[P],[T],[2],[[p,0],[0,1]]) for p in (5,7)]
        cls.all=cls.examples+[cls.double,cls.mixed,cls.torsion_closed]+cls.mixed_odd

    def test_actual_indices_and_group_invariants(self):
        self.assertEqual([c['actual_subgroup_index'] for c in self.all[:5]],[5,7,4,2,1])
        self.assertEqual(self.double['generator_lattice']['group_invariant_factors'],[2,2])
        self.assertEqual(self.mixed['generator_lattice']['group_invariant_factors'],[2])
        self.assertEqual(self.mixed['source_lattice']['free_rank'],1)
        self.assertEqual([c['actual_subgroup_index'] for c in self.mixed_odd],[5,7])
        for c in self.all:self.assertTrue(verify_torsion_subgroup_index(json.loads(json.dumps(c))))

    def test_all_relations_are_exact_point_relations(self):
        for c in self.all:
            E=EllipticCurve(c['presentation']['preimage']['curve'])
            for key,pointkey in [('source_lattice','source_points'),('generator_lattice','generators')]:
                points=[E.checked(P) for P in c['presentation']['preimage'][pointkey]]
                for row in c[key]['relation_basis']:
                    value=None
                    for P,n in zip(points,row):value=E.add(value,E.mul(P,n))
                    self.assertIsNone(value)
                self.assertEqual(len(c[key]['relation_basis']),len(points)-len(c['basis']))

    def test_replay_never_calls_producers_or_bounded_search(self):
        with patch('perfectpower.elliptic_torsion_index.smith_certificate',side_effect=AssertionError),patch.object(EllipticCurve,'independence',side_effect=AssertionError):
            for c in self.all:self.assertTrue(verify_torsion_subgroup_index(c))

    def test_corruptions_rejected(self):
        c=self.mixed
        paths=[('actual_subgroup_index',),('torsion_orders',0),('source_coordinates',0,0),
               ('generator_coordinates',0,0),('source_lattice','ambient_lattice_index'),
               ('generator_lattice','relation_basis',0,0),('generator_lattice','smith','right',0,0),
               ('generator_lattice','group_invariant_factors',0),('generator_lattice','free_rank')]
        for path in paths:
            b=copy.deepcopy(c);target=b
            for k in path[:-1]:target=target[k]
            target[path[-1]]+=1
            self.assertFalse(verify_torsion_subgroup_index(b),path)
        for bad in (None,[],{},True):self.assertFalse(verify_torsion_subgroup_index(bad))
        b=copy.deepcopy(c);b['basis']=[b['torsion_basis'][0]]
        self.assertFalse(verify_torsion_subgroup_index(b))
        b=copy.deepcopy(self.double);b['torsion_basis'][1]=b['torsion_basis'][0]
        self.assertFalse(verify_torsion_subgroup_index(b))
        b=copy.deepcopy(c);b['torsion_orders']=[4] # relation holds but injection fails
        self.assertFalse(verify_torsion_subgroup_index(b))
        b=copy.deepcopy(c);b['complete_mordell_weil_group']=True
        self.assertFalse(verify_torsion_subgroup_index(b))
        self.assertFalse(verify_torsion_subgroup_index(c,work_limit=1))

    def test_service(self):
        self.assertTrue(dispatch(None,{'op':'verify_elliptic_torsion_subgroup_index','args':{'cert':self.mixed}})['valid'])


class CompletePell(unittest.TestCase):
    def test_complete_census(self):
        expected=[]
        for x in range(100001):
            if (x*x+7)%2:continue
            z=(x*x+7)//2;y=isqrt(z)
            if y*y==z:expected.extend((sx*x,sy*y) for sx in (-1,1) for sy in (-1,1))
        self.assertEqual(solutions(100000),sorted(expected))
        self.assertEqual(len(expected),52)

    def test_large_unique_addresses_and_recurrence(self):
        for i in (0,1):
            for n in (0,1,2,10,100,1000):
                x,y=orbit(i,n)
                self.assertEqual(x*x+7,2*y*y)
                for sx,sy in product((-1,1),repeat=2):
                    self.assertEqual(address(sx*x,sy*y),dict(seed_index=i,n=n,x_sign=sx,y_sign=sy))
                a,b=orbit(i,n+1);c,d=orbit(i,n+2)
                self.assertEqual((c,d),(6*a-x,6*b-y))

    def test_not_solution_and_resource_failure(self):
        self.assertIsNone(address(0,0));self.assertIsNone(address(1,1))
        with self.assertRaises(ValueError):address(*orbit(0,2),step_limit=1)
        for i,n in ((True,0),(0,-1),(0,100001)):
            with self.assertRaises(ValueError):orbit(i,n)

    def test_certificate_and_service(self):
        c=certificate()
        with patch('perfectpower.pell7_complete.certificate',side_effect=AssertionError):
            self.assertTrue(verify_certificate(c))
        b=copy.deepcopy(c);b['terminal_table'][0]['y']=False;self.assertFalse(verify_certificate(b))
        for key in ('norm','terminal_y_max'):
            b=copy.deepcopy(c);b[key]+=1;self.assertFalse(verify_certificate(b))
        b=copy.deepcopy(c);b['seeds'].pop();self.assertFalse(verify_certificate(b))
        self.assertEqual(dispatch(None,{'op':'pell7_complete','args':{}}),c)
        self.assertTrue(dispatch(None,{'op':'verify_pell7_complete','args':{'c':c}})['valid'])
        self.assertEqual(dispatch(None,{'op':'pell7_address','args':{'x':5,'y':-4}})['address']['seed_index'],1)

if __name__=='__main__':unittest.main()
