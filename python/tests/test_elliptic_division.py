import copy
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
from perfectpower import polyalg as P
from perfectpower.elliptic_arithmetic import EllipticCurve,encode_point,q
from perfectpower.elliptic_division import tripling_polynomials,tripling_equation,factors
from perfectpower.elliptic_division_verifier import verify_thirds,verify_division,polynomials
from perfectpower.divisor_square import WorkLimit
from perfectpower.catalogue import Catalogue
from perfectpower.query_service import dispatch


class RationalDivisionTests(unittest.TestCase):
    def test_exact_three_and_six_torsion(self):
        E=EllipticCurve([0,1])
        c=E.rational_thirds(None)
        self.assertEqual(c['points'],[None,['0','-1'],['0','1']]);self.assertTrue(verify_thirds(c))
        c=E.rational_division(None,6)
        self.assertEqual(c['points'],[None,['-1','0'],['0','-1'],['0','1'],['2','-3'],['2','3']])
        self.assertTrue(verify_division(c))

    def test_nine_torsion_on_a_generalized_model(self):
        E=EllipticCurve([-3,-12,-12,0,0]);p=E.checked([0,0])
        self.assertIsNone(E.mul(p,9));self.assertIsNotNone(E.mul(p,3))
        for n,size in ((3,3),(9,9),(18,9),(27,9),(36,9)):
            c=E.rational_division(None,n)
            self.assertEqual(len(c['points']),size);self.assertTrue(verify_division(c))
            if n==9:self.assertEqual({E.checked(h) for h in c['points']},{E.mul(p,k) for k in range(9)})

    def test_all_supported_scalar_kernels(self):
        E=EllipticCurve([0,1])
        for n in (1,2,3,4,6,8,9,12,16,18,24,27,32,36):
            c=E.rational_division(None,n)
            known=[None,[-1,0],[0,-1],[0,1],[2,-3],[2,3]]
            expected=sorted([encode_point(E.checked(p)) for p in known if E.mul(p,n) is None],key=lambda p:p or [])
            self.assertEqual(c['points'],expected);self.assertTrue(verify_division(c))

    def test_recover_large_multiples_and_generalized_points(self):
        for spec,p in (([0,-2],[3,5]),([1,'-1/4',1,'-1/2','-9/4'],[3,3]),([-4,1],[0,1])):
            E=EllipticCurve(spec)
            for n in (3,6,12,18,36):
                c=E.rational_division(E.mul(p,n),n)
                self.assertEqual(c['points'],[encode_point(E.checked(p))]);self.assertTrue(verify_division(c))

    def test_empty_tripling_and_composed_fibres(self):
        E=EllipticCurve([0,-2])
        c=E.rational_thirds([3,5]);self.assertEqual(c['points'],[])
        self.assertIsNotNone(c['division_certificate']);self.assertTrue(verify_thirds(c))
        c=E.rational_division([3,5],18);self.assertEqual(c['points'],[])
        self.assertEqual(len(c['stages']),3);self.assertEqual(c['stages'][-1]['fibres'],[])
        self.assertTrue(verify_division(c))

    def test_target_sign_and_torsion_coset(self):
        E=EllipticCurve([0,9]);p=E.checked([3,6])
        c=E.rational_thirds(E.mul(p,3))
        expected={p,E.add(p,[0,3]),E.add(p,[0,-3])}
        self.assertEqual({E.checked(h) for h in c['points']},expected)
        self.assertTrue(verify_thirds(c))
        for target in ([0,1],[2,3],[2,-3]):
            F=EllipticCurve([0,1]);c=F.rational_thirds(target)
            for h in c['points']:self.assertEqual(F.mul(h,3),F.checked(target))
            self.assertTrue(verify_thirds(c))
        E=EllipticCurve([0,-2]);p=E.mul([3,5],3)
        self.assertEqual(E.rational_thirds(p)['points'],[['3','5']])
        self.assertEqual(E.rational_thirds(E.neg(p))['points'],[['3','-5']])

    def test_independent_polynomial_expansion_and_group_law(self):
        # Test generalized coordinate translation as well as short equations.
        count=0
        for spec in ([0,1],[0,-2],[-4,1],[1,-1,1,-10,-20],[1,'-1/4',1,'-1/2','-9/4']):
            E=EllipticCurve(spec)
            for x in range(-4,9):
                for y in range(-15,16):
                    if not E.contains((q(x),q(y))):continue
                    h=E.checked([x,y]);target=E.mul(h,3);psi,phi=tripling_polynomials(E)
                    other,f=polynomials(E,target);self.assertEqual(psi,other)
                    if target is None:self.assertEqual(P.evaluate(psi,q(x)),0)
                    else:
                        self.assertEqual(tripling_equation(E,target),f)
                        self.assertEqual(P.evaluate(f,q(x)),0)
                        self.assertEqual(P.evaluate(phi,q(x))/P.evaluate(psi,q(x))**2,target[0]+E.cubic[2]/3)
                    count+=1
        self.assertGreater(count,15)

    def test_fallback_search_proves_nonempty_fibre(self):
        E=EllipticCurve([0,-2])
        with patch('perfectpower.elliptic_division.discovered_roots',return_value=iter(())):
            c=E.rational_thirds(E.mul([3,5],3))
        self.assertIsNotNone(c['division_certificate']);self.assertEqual(c['points'],[['3','5']])
        self.assertTrue(verify_thirds(c))

    def test_replay_never_searches(self):
        E=EllipticCurve([0,1]);c=E.rational_division(None,36)
        empty=EllipticCurve([0,-2]).rational_thirds([3,5])
        with patch('perfectpower.elliptic_division.rational_thirds',side_effect=AssertionError('producer called')),patch('perfectpower.elliptic_arithmetic.discovered_roots',side_effect=AssertionError('search called')),patch('perfectpower.elliptic_division.discovered_roots',side_effect=AssertionError('search called')),patch('perfectpower.elliptic_arithmetic.rational_root_certificate',side_effect=AssertionError('root discovery called')):
            self.assertTrue(verify_division(c));self.assertTrue(verify_thirds(empty))

    def test_omitted_and_reordered_branches_reject(self):
        cert=EllipticCurve([0,1]).rational_division(None,36)
        mutations=[]
        c=copy.deepcopy(cert);c['stages'][2]['fibres'].pop();mutations.append(c)
        c=copy.deepcopy(cert);c['stages'][2]['targets'].reverse();mutations.append(c)
        c=copy.deepcopy(cert);c['stages'][-1]['points'].pop();mutations.append(c)
        c=copy.deepcopy(cert);c['points'].pop();mutations.append(c)
        c=copy.deepcopy(cert);c['stages'][2]['fibres'][0]['target']=['0','1'];mutations.append(c)
        c=copy.deepcopy(cert);c['stages'][2]['fibres'][0]['node_limit']+=1;mutations.append(c)
        for c in mutations:self.assertFalse(verify_division(c))

    def test_forged_root_and_anchor_reject(self):
        cert=EllipticCurve([0,-2]).rational_thirds([3,5])
        for field,value in (('root_nodes',0),('root_nodes',True),('points',[['3','5']]),('anchor',['3','5']),('method','torsion_coset'),('execution_verified',True),('complete',1),('node_limit',True)):
            c=copy.deepcopy(cert);c[field]=value;self.assertFalse(verify_thirds(c))
        c=copy.deepcopy(cert);c['division_certificate']['roots']=['3'];self.assertFalse(verify_thirds(c))
        c=copy.deepcopy(cert);chain=c['three_torsion_certificate']['integer_certificate']['sturm_chain'];chain[0]=(chain[0][0]+1,*chain[0][1:])
        self.assertFalse(verify_thirds(c))

    def test_strict_composition_metadata(self):
        cert=EllipticCurve([0,1]).rational_division(None,6)
        for field,value in (('scalar',True),('scalar',5),('scalar',12),('factors',[2,True]),('factors',[3,2]),('stages',[]),('branch_limit',1),('complete',1),('root_nodes',True),('schema','unsupported')):
            c=copy.deepcopy(cert);c[field]=value;self.assertFalse(verify_division(c))

    def test_budgets_and_rejected_scalars(self):
        E=EllipticCurve([0,1])
        for n in (0,-1,True,5,7,37,2.0):
            with self.assertRaises(ValueError):E.rational_division(None,n)
        for limit in (0,True,100001):
            with self.assertRaises(ValueError):E.rational_thirds(None,limit)
        with self.assertRaises(WorkLimit):E.rational_thirds(None,1)
        with self.assertRaises(WorkLimit):E.rational_division(None,6,branch_limit=2)
        c=E.rational_division(None,36)
        self.assertFalse(verify_division(c,work_limit=1));self.assertFalse(verify_division(c,node_limit=c['root_nodes']-1))
        # No accidental budget renewal when the first stages are affordable.
        with self.assertRaises(WorkLimit):E.rational_division(None,36,node_limit=c['root_nodes']-1)

    def test_persistent_service_and_json_roundtrip(self):
        with tempfile.TemporaryDirectory() as tmp:
            db=Path(tmp)/'catalogue.sqlite'
            with Catalogue(db) as cat:cat.register('elliptic_curve',{'ainvs':[0,0,0,0,1]},'E')
            with Catalogue(db) as cat:
                c=dispatch(cat,dict(op='call',object='E',method='rational_division',args=dict(p=None,scalar=36)))
                c=json.loads(json.dumps(c));self.assertTrue(verify_division(c))
                self.assertTrue(dispatch(cat,dict(op='verify_elliptic_division',args=dict(cert=c)))['valid'])
                thirds=dispatch(cat,dict(op='call',object='E',method='rational_thirds',args=dict(p=None)))
                self.assertTrue(dispatch(cat,dict(op='verify_elliptic_thirds',args=dict(cert=thirds)))['valid'])
            requests=[dict(op='call',object='E',method='rational_division',args=dict(p=None,scalar=6)),dict(op='call',object='E',method='rational_division',args=dict(p=None,scalar=5)),dict(op='call',object='E',method='rational_thirds',args=dict(p=None))]
            run=subprocess.run([sys.executable,'-m','perfectpower','service','--database',str(db)],input=''.join(json.dumps(r)+'\n' for r in requests),text=True,capture_output=True,check=True)
            rows=[json.loads(line) for line in run.stdout.splitlines()]
            self.assertEqual([r['ok'] for r in rows],[True,False,True])
            self.assertTrue(verify_division(rows[0]['result']));self.assertTrue(verify_thirds(rows[2]['result']))


if __name__=='__main__':unittest.main()
