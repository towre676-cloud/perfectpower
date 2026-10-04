import itertools
import json
import os
import random
import subprocess
import sys
import unittest
from copy import deepcopy
from fractions import Fraction as Q
from perfectpower import exact_linear as E
from perfectpower.divisor_square import WorkLimit
from perfectpower.deep_recovery_cli import exact_json
from perfectpower.witness_resolvent import (witness_resolvent,verify_resolvent,
    resolvent_value,compare_resolvents,subsequence_resolvent)
from perfectpower.connection_polytope import ConnectionGraph
from perfectpower.connection_measure import ConnectionMeasure,verify_measure
from perfectpower.connection_updates import reweight,verify_reweight


class WitnessTests(unittest.TestCase):
    def test_fibonacci_source(self):
        r=witness_resolvent([[0,1],[1,1]],[1,0],[[1,0]])
        self.assertEqual(r['outputs'][0]['numerator'],(1,-1))
        self.assertEqual(r['outputs'][0]['denominator'],(1,-1,-1))
        self.assertEqual(resolvent_value(r,100),218922995834555169026)

    def test_metaplectic_star(self):
        for p in (2,3,5,7,11,13):
            a=[[int((i==p) != (j==p)) for j in range(p+1)] for i in range(p+1)]
            s=[int(i==0) for i in range(p+1)]
            r=witness_resolvent(a,s,[s])
            self.assertEqual(r['outputs'][0]['numerator'],(1,0,1-p))
            self.assertEqual(r['outputs'][0]['denominator'],(1,0,-p))
            self.assertEqual([resolvent_value(r,k) for k in range(15)],
                [1 if k==0 else 0 if k%2 else p**(k//2-1) for k in range(15)])

    def test_nilpotent_transient(self):
        r=witness_resolvent([[0,1,0],[0,0,1],[0,0,0]],[0,0,1],[[1,0,0]])
        self.assertEqual(r['outputs'][0],{'numerator':(0,0,1),'denominator':(1,),'recurrence_order':3})
        self.assertEqual([resolvent_value(r,k) for k in range(8)],[0,0,1,0,0,0,0,0])

    def test_cancel_invisible_pole(self):
        r=witness_resolvent([[2,0],[0,3]],[1,1],[[1,0],[0,1],[0,0]])
        self.assertEqual(r['denominator'],(1,-5,6))
        self.assertEqual([o['denominator'] for o in r['outputs']],[(1,-2),(1,-3),(1,)])
        self.assertEqual(resolvent_value(r,100,0),2**100)

    def test_zero_seed(self):
        r=witness_resolvent([[1,1],[0,1]],[0,0],[[1,1]])
        self.assertEqual(r['reachable_dimension'],0)
        self.assertEqual(resolvent_value(r,2**63),0)
        self.assertTrue(verify_resolvent(r))

    def test_repeated_pole(self):
        r=witness_resolvent([[1,1],[0,1]],[0,1],[[1,0]])
        self.assertEqual(r['outputs'][0]['denominator'],(1,-2,1))
        self.assertEqual(resolvent_value(r,1000),1000)

    def test_random_independent_matrix_iteration(self):
        rng=random.Random(1201)
        for n in range(1,6):
            for trial in range(8):
                a=[[Q(rng.randint(-2,2),rng.randint(1,3)) for _ in range(n)] for _ in range(n)]
                s=[rng.randint(-2,2) for _ in range(n)];h=[[rng.randint(-2,2) for _ in range(n)] for _ in range(2)]
                r=witness_resolvent(a,s,h);v=tuple(s)
                for i in range(18):
                    for j,row in enumerate(h):self.assertEqual(resolvent_value(r,i,j),sum(x*y for x,y in zip(row,v)))
                    v=E.apply(a,v)

    def test_subsequence(self):
        a=[[0,1],[1,1]];s=[0,1];h=[[1,0]]
        full=witness_resolvent(a,s,h)
        for offset,step in ((0,2),(3,4),(5,0)):
            sample=subsequence_resolvent(a,s,h,offset=offset,step=step)
            for n in range(12):self.assertEqual(resolvent_value(sample,n),resolvent_value(full,offset+step*n))
        nil=subsequence_resolvent([[0,1],[0,0]],[0,1],[[1,0]],offset=3,step=2)
        self.assertEqual(resolvent_value(nil,10000),0)

    def test_equal_and_earliest_difference(self):
        a=witness_resolvent([[2]],[1],[[1]])
        b=witness_resolvent([[2,0],[0,3]],[1,1],[[1,0]])
        self.assertEqual(compare_resolvents(a,b)['status'],'EQUAL_FOR_ALL_NONNEGATIVE_INDICES')
        a=witness_resolvent([[0,1,0],[0,0,1],[0,0,0]],[0,0,1],[[1,0,0]])
        b=witness_resolvent([[0]],[0],[[1]])
        r=compare_resolvents(a,b)
        self.assertEqual((r['first_index'],r['difference']),(2,1))

    def test_tamper_identity_fraction_dimension(self):
        r=witness_resolvent([[2,0],[0,3]],[1,1],[[1,0]])
        for key,value in (('denominator',(1,-5,5)),('reachable_dimension',1),('seed',(2,1)),('execution_verified',True)):
            t=deepcopy(r);t[key]=value;self.assertFalse(verify_resolvent(t))
        t=deepcopy(r);t['outputs'][0]['numerator']=(2,);self.assertFalse(verify_resolvent(t))
        t=deepcopy(r);t['outputs'][0]['numerator']=(1,-3);t['outputs'][0]['denominator']=(1,-5,6);self.assertFalse(verify_resolvent(t))
        self.assertFalse(verify_resolvent(None))

    def test_json_roundtrip_and_no_discovery_replay(self):
        from unittest.mock import patch
        r=witness_resolvent([[1,'1/2'],[0,1]],[0,1],[[1,0]])
        r=json.loads(json.dumps(r,default=exact_json))
        with patch('perfectpower.witness_resolvent.E.solve',side_effect=AssertionError('discovery')):
            self.assertTrue(verify_resolvent(r));self.assertEqual(resolvent_value(r,11),Q(11,2))

    def test_budgets_and_bad_types(self):
        with self.assertRaises(WorkLimit):witness_resolvent([[1,0],[0,1]],[1,1],[[1,0]],work_limit=1)
        for a in ([[True]],[[1.0]]):
            with self.assertRaises(ValueError):witness_resolvent(a,[1],[[1]])
        with self.assertRaises(ValueError):subsequence_resolvent([[1]],[1],[[1]],step=-1)
        with self.assertRaises(WorkLimit):subsequence_resolvent([[2]],[1],[[1]],offset=2**63)
        r=witness_resolvent([[2]],[1],[[1]])
        with self.assertRaises(WorkLimit):resolvent_value(r,100,bit_limit=16)
        with self.assertRaises(ValueError):resolvent_value(r,-1)


class RepairTests(unittest.TestCase):
    def setUp(self):
        self.graph=ConnectionGraph(3,((0,1,0),(1,2,0),(2,0,1),(0,0,1),(0,1,1)),3)
        self.base=ConnectionMeasure(self.graph,[1,2,3,4,5])

    def test_simultaneous_increases_decreases(self):
        weights=[0,Q(1,2),5,4,2]
        r=reweight(self.base,weights);fresh=ConnectionMeasure(self.graph,weights).receipt()
        self.assertTrue(verify_reweight(r));self.assertTrue(verify_measure(r['updated']))
        for key in ('normalizing_determinant','laplacian_inverse','transfer_kernel','edge_marginals'):
            self.assertEqual(r['updated'][key],fresh[key])

    def test_rank_loss_and_unchanged(self):
        for weights in ([0]*5,[1,2,0,0,0]):
            r=reweight(self.base,weights);self.assertEqual(r['updated']['status'],'RANK_DEFICIENT')
            self.assertIsNone(r['defect_inverse']);self.assertTrue(verify_reweight(r))
        r=reweight(self.base,self.base.weights)
        self.assertEqual(r['changed_edges'],[]);self.assertEqual(r['inversion_dimension'],0)
        self.assertEqual(r['updated']['transfer_kernel'],self.base.receipt()['transfer_kernel'])

    def test_all_zero_pattern_weights(self):
        for weights in itertools.product((0,1),repeat=5):
            r=reweight(self.base,weights);fresh=ConnectionMeasure(self.graph,weights).receipt()
            self.assertEqual(r['updated']['status'],fresh['status'])
            self.assertEqual(r['updated']['normalizing_determinant'],fresh['normalizing_determinant'])
            self.assertEqual(r['updated']['edge_marginals'],fresh['edge_marginals'])

    def test_cyclotomic_and_parallel_loop_models(self):
        for power in (2,3,4,5,6,7):
            g=ConnectionGraph(2,((0,1,0),(0,1,1),(1,1,1)),power)
            m=ConnectionMeasure(g,[1,2,3]);r=reweight(m,[2,0,4])
            self.assertTrue(verify_reweight(r));self.assertTrue(verify_measure(r['updated']))

    def test_roundtrip_and_future_events(self):
        r=json.loads(json.dumps(reweight(self.base,[1,0,3,4,5])))
        self.assertTrue(verify_reweight(r))
        repaired=ConnectionMeasure.from_receipt(r['updated']);fresh=ConnectionMeasure(self.graph,[1,0,3,4,5])
        for inc,exc in (((0,),()),((),(3,)),((2,),(4,)),((1,),())):
            self.assertEqual(repaired.event(inc,exc),fresh.event(inc,exc))

    def test_tamper_small_and_large_certificates(self):
        r=reweight(self.base,[1,2,3,4,6])
        for key,value in (('changed_edges',[0]),('inversion_dimension',2),('determinant_ratio',['0']),('defect_matrix',[[['0']]])):
            t=deepcopy(r);t[key]=value;self.assertFalse(verify_reweight(t))
        t=deepcopy(r);t['updated']['edge_marginals'][0]=['0'];self.assertFalse(verify_reweight(t))
        t=deepcopy(r);t['base']['normalizing_determinant']=['1'];self.assertFalse(verify_reweight(t))
        t=deepcopy(r);t['defect_inverse']=[[['0']]];self.assertFalse(verify_reweight(t))
        self.assertFalse(verify_reweight(None))

    def test_replay_never_discovers_new_inverse(self):
        from unittest.mock import patch
        r=reweight(self.base,[1,2,3,4,6])
        with patch('perfectpower.connection_updates._inverse',side_effect=AssertionError('discovery')):
            self.assertTrue(verify_reweight(r))

    def test_bad_weights_limits_rank_deficient_base(self):
        with self.assertRaises(ValueError):reweight(self.base,[-1,2,3,4,5])
        with self.assertRaises(WorkLimit):reweight(self.base,[1,2,3,4,6],work_limit=1)
        with self.assertRaises(ValueError):reweight(ConnectionMeasure(self.graph,[0]*5),[1]*5)


class CLITests(unittest.TestCase):
    def test_commands(self):
        commands=[['witness-resolvent','--matrix','[[0,1],[1,1]]','--seed','[0,1]','--readouts','[[1,0]]','--index','10'],
            ['connection-reweight','--vertices','2','--edges','[[0,1,0],[0,1,1]]','--power','3','--weights','[1,1]','--new-weights','[2,1]']]
        for command in commands:
            p=subprocess.run([sys.executable,'-m','perfectpower']+command+['--verify'],capture_output=True,text=True,env=os.environ)
            self.assertEqual(p.returncode,0,p.stderr);self.assertTrue(json.loads(p.stdout)['certificate_replay'])


if __name__=='__main__':unittest.main()
