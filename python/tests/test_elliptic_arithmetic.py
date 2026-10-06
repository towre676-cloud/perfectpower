import copy
import io
import json
import tempfile
import unittest
from fractions import Fraction as Q
from pathlib import Path
from unittest.mock import patch
from perfectpower import polyalg as P
from perfectpower.elliptic_arithmetic import (EllipticCurve, encode_point,
    rational_root_certificate, rational_roots, q)
from perfectpower.elliptic_certificate_verifier import verify_halves
from perfectpower.divisor_square import WorkLimit
from perfectpower.catalogue import Catalogue
from perfectpower.query_service import dispatch, serve


class RationalFibreTests(unittest.TestCase):
    def test_infinity_and_nondivisible_two_torsion(self):
        E=EllipticCurve([-1,0]);packet=E.rational_halves(None)
        self.assertEqual(packet['points'],[None,['-1','0'],['0','0'],['1','0']])
        self.assertTrue(verify_halves(packet))
        packet=E.rational_halves([0,0])
        self.assertEqual(packet['points'],[])
        self.assertEqual(packet['method'],'empty_division_fibre')
        self.assertTrue(verify_halves(packet))

    def test_single_half_and_four_element_coset(self):
        E=EllipticCurve([0,-2]);p=E.checked([3,5])
        packet=E.rational_halves(E.mul(p,2))
        self.assertEqual(packet['points'],[['3','5']]);self.assertTrue(verify_halves(packet))
        self.assertEqual(E.rational_halves([3,5])['points'],[])
        E=EllipticCurve([-25,0]);p=E.checked(['25/4','75/8'])
        packet=E.rational_halves(E.mul(p,2))
        self.assertEqual(len(packet['points']),4)
        self.assertTrue(verify_halves(packet))
        self.assertTrue(all(E.mul(h,2)==E.mul(p,2) for h in packet['points']))

    def test_generalized_weierstrass_and_inverse_maps(self):
        E=EllipticCurve([1,'-1/4',1,'-1/2','-9/4']);p=E.checked([3,3])
        short=EllipticCurve([0,-2]);mapped=E.transport(p,short)
        self.assertEqual(mapped,short.checked([3,5]))
        self.assertEqual(short.transport(mapped,E),p)
        self.assertIsNone(E.add(p,E.neg(p)))
        self.assertEqual(E.mul(p,-3),E.neg(E.mul(p,3)))
        self.assertTrue(verify_halves(E.rational_halves(E.mul(p,2))))
        self.assertEqual(E.model_transport([3,3],short.specification)['point'],['3','5'])

    def test_rational_scaling_map_and_two_isogeny(self):
        E=EllipticCurve([0,-2]);F=EllipticCurve([0,-128]);p=[3,5]
        self.assertEqual(E.model_transport(p,F.specification)['point'],['12','40'])
        self.assertEqual(F.transport(E.transport(p,F),E),E.checked(p))
        self.assertIsNone(E.isomorphism([0,-3]))
        E=EllipticCurve([-2,0]);T=[0,0];p=E.checked([2,2])
        target=EllipticCurve(E.isogeny(T)['target'])
        self.assertIsNone(E.isogeny_point(T,T));self.assertIsNone(E.isogeny_point(None,T))
        self.assertEqual(E.isogeny_point(E.mul(p,2),T),target.mul(E.isogeny_point(p,T),2))

    def test_sturm_transform_repeated_roots_and_huge_numerators(self):
        root=Q(10**80+3,7)
        f=P.mul(P.power((-root,1),2),(Q(2,3),1))
        cert=rational_root_certificate(f)
        self.assertEqual(list(map(Q,cert['roots'])),[Q(-2,3),root])
        self.assertEqual(rational_roots(f),[Q(-2,3),root])
        from perfectpower.elliptic_certificate_verifier import CheckBudget,check_rational_roots
        self.assertEqual(check_rational_roots(cert,f,100000,CheckBudget(2000000))[0],[Q(-2,3),root])

    def test_complete_fibres_against_separate_bounded_point_enumeration(self):
        from math import isqrt
        for a,b in ((-1,0),(-2,0),(-4,1),(0,-2)):
            E=EllipticCurve([a,b]);bounded=set()
            for denominator in range(1,5):
                for numerator in range(-12,13):
                    x=Q(numerator,denominator);v=x**3+a*x+b
                    if v<0:continue
                    n,d=isqrt(v.numerator),isqrt(v.denominator)
                    if n*n==v.numerator and d*d==v.denominator:
                        bounded.update((x,y) for y in {Q(n,d),Q(-n,d)})
            for p in sorted(bounded)[:4]:
                target=E.mul(p,2);packet=E.rational_halves(target)
                self.assertTrue(verify_halves(packet))
                returned={None if h is None else tuple(map(Q,h)) for h in packet['points']}
                self.assertTrue({h for h in bounded if E.mul(h,2)==target}<=returned)
                for h in returned:self.assertEqual(E.mul(h,2),target)

    def test_empty_fallback_and_discovery_free_check(self):
        E=EllipticCurve([0,-2]);target=E.mul([3,5],2)
        with patch('perfectpower.elliptic_arithmetic.discovered_roots',return_value=iter(())):
            packet=E.rational_halves(target)
        self.assertIsNotNone(packet['division_certificate'])
        with patch.object(EllipticCurve,'halves',side_effect=AssertionError('discovery called')),patch('perfectpower.elliptic_arithmetic.rational_roots',side_effect=AssertionError('discovery called')):
            self.assertTrue(verify_halves(packet))

    def test_mutations_and_budgets(self):
        packet=EllipticCurve([-1,0]).rational_halves(None)
        for key,value in (('complete',1),('execution_verified',True),('schema','bad'),('points',[]),('root_nodes',True),('anchor',['0','0']),('node_limit',True)):
            forged=copy.deepcopy(packet);forged[key]=value;self.assertFalse(verify_halves(forged),key)
        forged=copy.deepcopy(packet);forged['two_torsion_certificate']['roots']=[]
        self.assertFalse(verify_halves(forged))
        forged=copy.deepcopy(packet);forged['two_torsion_certificate']['integer_certificate']['nodes'].pop()
        self.assertFalse(verify_halves(forged))
        self.assertFalse(verify_halves(packet,work_limit=1))
        self.assertFalse(verify_halves(packet,node_limit=1))
        with self.assertRaises(WorkLimit):EllipticCurve([-1,0]).rational_halves(None,node_limit=1)
        for limit in (0,True,100001):
            with self.assertRaises(ValueError):EllipticCurve([-1,0]).rational_halves(None,node_limit=limit)
        for spec in (None,{},[0,0],[True,1]):
            with self.assertRaises((ValueError,TypeError)):EllipticCurve(spec)
        with self.assertRaises(ValueError):q(1.0)


class EllipticServiceTests(unittest.TestCase):
    def test_cold_reload_and_allowlist(self):
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'objects.sqlite'
            with Catalogue(path) as c:
                identity=dispatch(c,dict(op='register',kind='elliptic_curve',specification={'ainvs':[0,-2]},name='E'))['id']
            with Catalogue(path) as c:
                self.assertEqual(c.definition('E')['id'],identity)
                doubled=dispatch(c,dict(op='call',object='E',method='point_multiply',args={'p':[3,5],'scalar':2}))
                packet=dispatch(c,dict(op='call',object='E',method='rational_halves',args={'p':doubled}))
                self.assertTrue(dispatch(c,dict(op='verify_elliptic_halves',args={'cert':packet}))['valid'])
                with self.assertRaises(ValueError):dispatch(c,dict(op='call',object='E',method='checked',args={'p':[3,5]}))
                output=io.StringIO()
                requests=[dict(op='call',object='E',method='rational_halves',args={'p':[3,5],'node_limit':1}),dict(op='call',object='E',method='point_add',args={'left':[3,5],'right':[3,-5]})]
                serve(c,io.StringIO('\n'.join(map(json.dumps,requests))+'\n'),output)
                results=list(map(json.loads,output.getvalue().splitlines()))
                self.assertFalse(results[0]['ok']);self.assertTrue(results[1]['ok']);self.assertIsNone(results[1]['result'])


if __name__=='__main__':unittest.main()
