import copy
import random
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
from perfectpower.elliptic_arithmetic import EllipticCurve,encode_point
from perfectpower.elliptic_certificates import certify_independence,replay_independence,local_matrix,binary_rows
from perfectpower.elliptic_certificate_verifier import verify_independence,character_rows,f2_rank,CheckBudget
from perfectpower.catalogue import Catalogue
from perfectpower.query_service import dispatch


class IndependenceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.E=EllipticCurve([-4,1]);cls.points=[[0,1],[2,1]]
        cls.cert=certify_independence(cls.E,cls.points,prime_bound=100)
        cls.doubled=certify_independence(cls.E,[encode_point(cls.E.mul(p,2)) for p in cls.points],prime_bound=100)

    def test_two_independent_points_and_no_discovery_in_replay(self):
        self.assertEqual(self.cert['rank_lower_bound'],2);self.assertTrue(self.cert['independent'])
        with patch('perfectpower.elliptic_certificates.local_matrix',side_effect=AssertionError('producer called')),patch('perfectpower.elliptic_certificates.binary_rows',side_effect=AssertionError('producer called')),patch('perfectpower.elliptic_arithmetic.rational_roots',side_effect=AssertionError('discovery called')):
            self.assertTrue(replay_independence(self.cert))

    def test_dependent_negated_torsion_and_empty_witnesses(self):
        E=self.E;p=self.points[0]
        for points,expected in (([p,p],1),([p,encode_point(E.neg(p))],1),([p,encode_point(E.mul(p,3))],1),([],0)):
            cert=certify_independence(E,points,prime_bound=50,halving_limit=3)
            self.assertEqual(cert['rank_lower_bound'],expected)
            self.assertTrue(verify_independence(cert))
            self.assertEqual(cert['independent'],len(points)==expected)
        E=EllipticCurve([4,0])
        cert=certify_independence(E,[[2,4],[0,0],None],prime_bound=50,halving_limit=3)
        self.assertEqual(cert['rank_lower_bound'],0);self.assertFalse(cert['independent']);self.assertTrue(verify_independence(cert))

    def test_recorded_halving_transformations_and_torsion_offsets(self):
        self.assertEqual(len(self.doubled['halving_steps']),2)
        self.assertEqual(self.doubled['rank_lower_bound'],2)
        self.assertTrue(verify_independence(self.doubled))
        E=EllipticCurve([-2,0]);p=E.mul([2,2],2)
        cert=certify_independence(E,[encode_point(p)],prime_bound=100,halving_limit=4)
        self.assertTrue(cert['halving_steps']);self.assertEqual(cert['two_torsion_dimension'],1)
        self.assertTrue(cert['independent']);self.assertTrue(verify_independence(cert))
        # A separate exact change of span with a nonzero torsion offset.
        T=E.checked([0,0]);h=E.checked([2,2]);source=E.add(E.mul(h,2),T)
        modified=certify_independence(E,[encode_point(h)],prime_bound=100,halving_limit=4)
        modified['original_points']=[encode_point(source)]
        modified['halving_steps']=[dict(indices=[0],offset=encode_point(T),replace=0,half=encode_point(h))]
        self.assertTrue(verify_independence(modified))

    def test_generalized_models_and_scaled_bad_primes(self):
        E=EllipticCurve([1,'-1/4',1,'-1/2','-9/4'])
        self.assertTrue(certify_independence(E,[[3,3]],prime_bound=50)['independent'])
        # Rational model is good at 5 but the integral-model scaling is not.
        E=EllipticCurve([0,'-2/15625']);p=E.checked(['3/25','1/25'])
        cert=certify_independence(E,[encode_point(p)],prime_bound=50)
        self.assertNotIn(5,[packet['prime'] for packet in cert['primes']])
        self.assertTrue(verify_independence(cert))

    def test_independent_elimination_and_local_rows_agree(self):
        rng=random.Random(20261006)
        for _ in range(100):
            rows=[rng.randrange(1<<17) for _ in range(rng.randrange(1,20))]
            self.assertEqual(binary_rows(rows)[0],f2_rank(rows,17,CheckBudget(10000)))
        for E,points in ((self.E,[self.E.checked(p) for p in self.points]),(EllipticCurve([0,-2]),[EllipticCurve([0,-2]).mul([3,5],2),None])):
            producer,packets,_,columns=local_matrix(E,points,50)
            rows,other,width=character_rows(E,points,50,CheckBudget(100000))
            self.assertEqual((producer,packets,columns),(rows,other,width))

    def test_full_small_prime_local_images_are_homomorphisms(self):
        # Independently enumerate finite groups, not only rational sample points.
        # The integral change X=4x,Y=8y gives f=X³+16aX+64b.
        for a,b,p in ((-4,1,5),(-4,1,7),(-1,0,7),(0,-2,5)):
            A,B=16*a%p,64*b%p
            roots=[r for r in range(p) if (r**3+A*r+B)%p==0]
            points=[None]+[(x,y) for x in range(p) for y in range(p) if (y*y-x**3-A*x-B)%p==0]
            def add(u,v):
                if u is None:return v
                if v is None:return u
                x,y=u;z,w=v
                if x==z and (y+w)%p==0:return None
                slope=((3*x*x+A)*pow(2*y,-1,p) if x==z else (w-y)*pow(z-x,-1,p))%p
                xx=(slope*slope-x-z)%p
                return xx,(slope*(x-xx)-y)%p
            def image(u):
                if u is None:return 0
                x,y=u;bits=0
                for j,r in enumerate(roots):
                    value=(x-r)%p
                    if value==0:value=(3*r*r+A)%p
                    self.assertNotEqual(value,0)
                    if pow(value,(p-1)//2,p)==p-1:bits|=1<<j
                return bits
            for u in points:
                self.assertEqual(image(add(u,u)),0)
                for v in points:self.assertEqual(image(add(u,v)),image(u)^image(v))

    def test_tampered_packets_and_strict_types_reject(self):
        mutations=[('matrix_rank',0),('matrix_rank',True),('rank_lower_bound',1),('columns',0),('matrix_rows',['0','0']),('independent',1),('two_torsion_dimension',1),('scope','complete basis'),('complete_basis',True),('execution_verified',True),('prime_bound',True),('schema','pp-elliptic-independence/1')]
        for key,value in mutations:
            forged=copy.deepcopy(self.cert);forged[key]=value
            self.assertFalse(verify_independence(forged),key)
        for change in ('prime','root','original','working','unknown','torsion_proof'):
            forged=copy.deepcopy(self.cert)
            if change=='prime':forged['primes'][0]['prime']=9
            elif change=='root':forged['primes'][0]['roots'][0]+=1
            elif change=='original':forged['original_points'][0]=None
            elif change=='working':forged['working_points'][0]=None
            elif change=='unknown':forged['complete_integer_census']=True
            else:forged['two_torsion_proof']['prime']=9
            self.assertFalse(verify_independence(forged),change)
        for key,value in (('half',None),('offset',['0','1']),('replace',True),('indices',[0,0])):
            forged=copy.deepcopy(self.doubled);forged['halving_steps'][0][key]=value
            self.assertFalse(verify_independence(forged),key)
        forged=copy.deepcopy(self.cert);forged['primes'][0]['roots'][0]=True
        self.assertFalse(verify_independence(forged))

    def test_bounds_and_cold_service_replay(self):
        self.assertFalse(verify_independence(self.cert,work_limit=1))
        self.assertFalse(verify_independence(self.cert,work_limit=True))
        for kwargs in ({'prime_bound':2001},{'prime_bound':True},{'halving_limit':65},{'node_limit':0}):
            with self.assertRaises(ValueError):certify_independence(self.E,self.points,**kwargs)
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'objects.sqlite'
            with Catalogue(path) as c:c.register('elliptic_curve',self.E.specification,'E')
            with Catalogue(path) as c:
                cert=dispatch(c,dict(op='call',object='E',method='independence',args=dict(points=self.points,prime_bound=100)))
                self.assertTrue(dispatch(c,dict(op='verify_elliptic_independence',args={'cert':cert}))['valid'])


if __name__=='__main__':unittest.main()
