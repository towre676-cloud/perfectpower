import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from fractions import Fraction as Q
from perfectpower.generating_arithmetic import pell_generating,modular_power_gf,modular_count,replay_arithmetic_gf,compile_spec,replay
from perfectpower.generating import RationalGF
from perfectpower.recurrence import Recurrence
from perfectpower.binary64 import bits
from perfectpower.binary_polynomial import polynomial_power_certificate,replay_binary_polynomial


class ArithmeticSeriesTests(unittest.TestCase):
    def test_pell_exact_equations_and_unit_multiplication(self):
        for D in (2,3,5,6,7,13):
            p=pell_generating(D);self.assertTrue(replay_arithmetic_gf(p))
            gx=RationalGF(p['x']['numerator'],p['x']['denominator'])
            gy=RationalGF(p['y']['numerator'],p['y']['denominator'])
            x,y=1,0;u,v=p['unit']
            for n in range(25):
                self.assertEqual((gx.nth(n),gy.nth(n)),(x,y))
                self.assertEqual(x*x-D*y*y,1)
                x,y=u*x+D*v*y,v*x+u*y
        p=pell_generating(2,[17,12]);self.assertEqual(p['unit'],[17,12])
        with self.assertRaises(ValueError):pell_generating(2,[3,3])

    def test_recurrence_adapter_preserves_old_api(self):
        recurrence=Recurrence((1,1),(0,1))
        p,q=recurrence.generating_function()
        self.assertEqual(recurrence.minimal_generating_function(),RationalGF(p,q))
        self.assertEqual(recurrence.minimal_generating_function().nth(100),recurrence.nth(100))

    def test_other_session_series_bridge(self):
        from perfectpower.generating_functions import RationalSeries
        from perfectpower.generating import replay_generating
        series=RationalSeries({'numerator':[0,1],'denominator':[1,-1,-1]})
        packet=series.realization_certificate()
        self.assertTrue(replay_generating(packet))
        self.assertEqual(packet['dimension'],2)
        extracted=series.subsequence(offset=2,step=3)
        for n in range(12):self.assertEqual(extracted.coefficient(n),series.coefficient(3*n+2))
        series=RationalSeries({'numerator':[1],'denominator':[1,'-1/3']})
        self.assertTrue(replay_generating(series.analytic_tail('1/4','1/2',10)))

    def test_modular_sieve_count_and_ogf_against_enumeration(self):
        for c,a in [([1,1],[0,1]),([-1,6],[1,3]),([1],[7]),([0,1],[3,2])]:
            for modulus in (4,5,8,11):
                p=modular_power_gf(c,a,2,modulus)
                self.assertTrue(replay_arithmetic_gf(p))
                f=p['accepted_index_gf'];gf=RationalGF(f['numerator'],f['denominator'])
                residues={x*x%modulus for x in range(modulus)}
                values=Recurrence(tuple(c),tuple(a)).terms(160)
                accepted=tuple(int(x%modulus in residues) for x in values)
                self.assertEqual(gf.coefficients(160),accepted)
                self.assertEqual(modular_count(p,160),sum(accepted))
                cumulative=gf*RationalGF([1],[1,-1])
                self.assertEqual(cumulative.nth(10**12-1),modular_count(p,10**12))

    def test_congruence_is_only_a_filter(self):
        p=modular_power_gf([1],[17],2,8)
        self.assertEqual(modular_count(p,100),100)
        self.assertIn('necessary filter',p['scope'])

    def test_polynomial_exact_value_not_rounded_result(self):
        p=polynomial_power_certificate(bits(0.1),[0,0,1],2)
        self.assertTrue(p['is_power']);self.assertEqual(Q(p['root']),Q.from_float(0.1))
        self.assertTrue(replay_binary_polynomial(p))
        p=polynomial_power_certificate(bits(1e16),[1,1],2)
        self.assertEqual(Q(p['value']),10**16+1)
        self.assertFalse(p['is_power'])
        self.assertEqual(1e16+1.0,1e16)
        p=polynomial_power_certificate(bits(-0.5),[0,0,0,1],3)
        self.assertEqual(Q(p['root']),-Q(1,2))

    def test_replay_rejects_tamper(self):
        p=modular_power_gf([1,1],[0,1],2,5)
        for key in ('accepted_index_gf','cycle_table','power_residues','scope'):
            bad=copy.deepcopy(p);bad[key]=None
            with self.assertRaises(ValueError):replay_arithmetic_gf(bad)
        p=polynomial_power_certificate(bits(0.25),[0,1],2);p['root']='3'
        with self.assertRaises(ValueError):replay_binary_polynomial(p)

    def test_cli_examples_roundtrip(self):
        root=Path(__file__).resolve().parents[2]
        for path in sorted((root/'examples/arithmetic_series').glob('*.json')):
            spec=json.loads(path.read_text());packet=compile_spec(spec)
            self.assertTrue(replay(json.loads(json.dumps(packet))))
        with tempfile.TemporaryDirectory() as tmp:
            source=Path(tmp)/'source.json';target=Path(tmp)/'packet.json'
            source.write_text(json.dumps({'kind':'binary64_power','word':bits(0.25),'degree':2}))
            subprocess.run([sys.executable,'-m','perfectpower','arithmetic-series','compile',str(source),'--output',str(target)],check=True,capture_output=True)
            result=subprocess.run([sys.executable,'-m','perfectpower','arithmetic-series','replay',str(target)],check=True,capture_output=True,text=True)
            self.assertTrue(json.loads(result.stdout)['accepted'])


if __name__=='__main__':unittest.main()
