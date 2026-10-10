import copy
import json
from fractions import Fraction as Q
from math import comb
import unittest
from perfectpower.telescoping import (discover_binomial_sum, replay_binomial_sum,
    BinomialSumSequence, discover_antidifference, replay_antidifference,
    sum_from_antidifference)
from perfectpower.generating_cli import execute

class TelescopingTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.packets={p:discover_binomial_sum(p,max_order=2) for p in range(1,5)}

    def test_all_four_families_against_independent_direct_sums(self):
        for p,packet in self.packets.items():
            packet=json.loads(json.dumps(packet))
            self.assertTrue(replay_binomial_sum(packet)['boundary_conditions_proved'])
            series=BinomialSumSequence(packet)
            self.assertEqual(series.terms(size=81),[sum(comb(n,k)**p for k in range(n+1)) for n in range(81)])
            self.assertEqual(packet['order'],1 if p<3 else 2)

    def test_certificate_and_seed_tampering(self):
        for p in self.packets.values():
            for field in ('coefficients','certificate_polynomial'):
                bad=copy.deepcopy(p);bad[field][0]['numerator'][0]=str(Q(bad[field][0]['numerator'][0])+1)
                with self.assertRaises(ValueError):replay_binomial_sum(bad)
            bad=copy.deepcopy(p);bad['initial'][0]='2'
            with self.assertRaises(ValueError):replay_binomial_sum(bad)

    def test_domain_rejected_even_for_valid_scaled_identity(self):
        bad=copy.deepcopy(self.packets[1])
        bad['certificate_polynomial'][0]['denominator']=['-1','1']
        with self.assertRaises(ValueError):replay_binomial_sum(bad)

    def test_bounded_failure_and_input_guards(self):
        self.assertEqual(discover_binomial_sum(3,max_order=1)['status'],'ANSATZ_UNRESOLVED')
        self.assertFalse(discover_binomial_sum(3,max_order=1)['nonexistence_proved'])
        for p in (True,0,5,2.0):
            with self.assertRaises(ValueError):discover_binomial_sum(p)
        with self.assertRaises(ValueError):discover_binomial_sum(2,degree=13)

    def test_power_window_complete_but_not_unbounded(self):
        s=BinomialSumSequence(self.packets[1]);packet=s.power_hits(size=120)
        self.assertEqual([v['index'] for v in packet['hits']],list(range(0,120,2)))
        self.assertFalse(packet['unbounded_classification_proved'])
        for item in packet['hits']:self.assertEqual(int(item['root'])**2,int(item['value']))
        s.packet['initial'][0]='99' # does not change the already compiled values
        self.assertEqual(s.coefficient(0),1)

    def test_geometric_antidifference_and_finite_boundaries(self):
        for ratio in (-3,-1,1,2,Q(3,2)):
            packet=discover_antidifference(str(ratio),degree=1)
            self.assertTrue(replay_antidifference(packet)['valid'])
            for start in range(5):
                for stop in range(start,15):
                    out=sum_from_antidifference(packet,start,stop,3)
                    self.assertEqual(Q(out['sum']),sum((3*Q(ratio)**k for k in range(stop-start)),Q(0)))

    def test_polynomial_and_rational_terms(self):
        for degree in range(1,6):
            # t(k)=(k+1)^degree, ratio=(k+2)^degree/(k+1)^degree.
            from perfectpower.core import power
            ratio={'numerator':list(map(str,power((Q(2),Q(1)),degree))),
                   'denominator':list(map(str,power((Q(1),Q(1)),degree)))}
            packet=discover_antidifference(ratio,denominator=ratio['denominator'],degree=degree+1)
            self.assertEqual(Q(sum_from_antidifference(packet,0,40,1)['sum']),sum(k**degree for k in range(1,41)))
        ratio={'numerator':[1,1],'denominator':[3,1]} # t(k)=1/((k+1)(k+2))
        packet=discover_antidifference(ratio,degree=1)
        self.assertEqual(Q(sum_from_antidifference(packet,0,30,'1/2')['sum']),Q(30,31))

    def test_antidifference_poles_failure_and_tamper(self):
        packet=discover_antidifference({'numerator':[1,1],'denominator':[0,1]},degree=2)
        with self.assertRaises(ValueError):sum_from_antidifference(packet,0,5,1)
        bad=copy.deepcopy(packet);bad['certificate']['numerator'][0]='99'
        with self.assertRaises(ValueError):replay_antidifference(bad)
        self.assertEqual(discover_antidifference({'numerator':[1,1],'denominator':[2,1]},degree=2)['status'],'ANSATZ_UNRESOLVED')

    def test_cli_bridge(self):
        out=execute({'kind':'binomial_sum','specification':{'power':3,'max_order':2},'query':{'size':20}})
        self.assertEqual(list(map(int,out['terms'])),[sum(comb(n,k)**3 for k in range(n+1)) for n in range(20)])
        self.assertTrue(out['replay']['boundary_conditions_proved'])
        out=execute({'kind':'antidifference','specification':{'ratio':2},'query':{'start':0,'stop':10,'initial_term':1}})
        self.assertEqual(out['finite_sum']['sum'],'1023')

    def test_closed_form_solutions_are_checked_not_guessed(self):
        from perfectpower.telescoping import certify_hypergeometric_solution, replay_hypergeometric_solution
        for power,ratio in ((1,2),(2,{'numerator':[2,4],'denominator':[1,1]})):
            p=certify_hypergeometric_solution(self.packets[power],ratio)
            self.assertTrue(replay_hypergeometric_solution(p)['valid'])
            bad=copy.deepcopy(p);bad['initial']='2'
            with self.assertRaises(ValueError):replay_hypergeometric_solution(bad)
        with self.assertRaises(ValueError):certify_hypergeometric_solution(self.packets[3],8)

    def test_module_cli_compile_then_replay(self):
        import os,subprocess,sys,tempfile
        from pathlib import Path
        with tempfile.TemporaryDirectory() as folder:
            src=Path(folder)/'spec.json';out=Path(folder)/'out.json'
            src.write_text(json.dumps({'kind':'binomial_sum','specification':{'power':2},'query':{'size':8}}))
            subprocess.run([sys.executable,'-m','perfectpower.telescoping','compile',str(src),'--out',str(out)],check=True,capture_output=True)
            r=subprocess.run([sys.executable,'-m','perfectpower.telescoping','replay',str(out)],check=True,capture_output=True,text=True)
            self.assertTrue(json.loads(r.stdout)['boundary_conditions_proved'])
