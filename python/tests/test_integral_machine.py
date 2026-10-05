import itertools
import json
import os
import random
import subprocess
import sys
import unittest
from copy import deepcopy
from fractions import Fraction as Q
from unittest.mock import patch
from perfectpower import exact_linear as E
from perfectpower.deep_recovery_cli import exact_json
from perfectpower.observable_machine import minimal_machine,recurrence_batch,word_output
from perfectpower.recurrence import Recurrence
from perfectpower.integer_lifting import ReductionLimit
from perfectpower.divisor_square import WorkLimit
from perfectpower.integral_machine import (integral_machine,integralize_machine,verify_integral_machine,
    integral_word_output,integral_power_output,project_state,observation_fibre,distinguish_states,modular_power_output)


class IntegralMachineTests(unittest.TestCase):
    def test_integer_outputs_same_minimum(self):
        a=[[[2,0,0],[0,3,0],[0,0,7]]];s=[1,1,0];h=[[1,0,0]]
        r=integral_machine(a,s,h)
        self.assertEqual((r['reachable_dimension'],r['minimal_dimension']),(2,1))
        self.assertEqual(integral_power_output(r,100),(2**100,))
        self.assertTrue(verify_integral_machine(r))

    def test_index_not_orbit_lattice_claim(self):
        r=integral_machine([[[1,1],[0,1]]],[0,2],[[1,0]])
        self.assertEqual(r['selected_word_lattice_index'],4)
        self.assertEqual(integral_word_output(r,[0]*5),(10,))
        # Odd coordinates are allowed in the saturated chart, though all
        # integer combinations of actual orbit words are even in this model.
        self.assertEqual(len(project_state(r,[1,0])),2)

    def test_actual_divisibility_not_coordinate_denominators(self):
        r=integral_machine([[[1,1],[0,1]]],[0,2],[[2,0]])
        self.assertEqual(r['observation_image_factors'],[2,2])
        bad=observation_fibre(r,[1,2]);self.assertEqual(bad['status'],'DIVISIBILITY_OBSTRUCTION')
        self.assertEqual(bad['modulus'],2)
        good=observation_fibre(r,[4,10]);self.assertEqual(good['status'],'INTEGER_AFFINE_FIBRE')
        x=good['original_particular'];self.assertEqual(2*x[0],4);self.assertEqual(2*(x[0]+x[1]),10)

    def test_prime_power_depth(self):
        r=integral_machine([[[1,1],[0,1]]],[0,1],[[4,0]])
        self.assertEqual(r['observation_image_factors'],[4,4])
        bad=observation_fibre(r,[2,0]);self.assertEqual((bad['status'],bad['modulus']),('DIVISIBILITY_OBSTRUCTION',4))

    def test_full_integer_fibre_future_invisible(self):
        r=integral_machine([[[2,0],[0,3]]],[1,1],[[1,0]])
        result=observation_fibre(r,[5]);x=result['original_particular'];basis=result['original_kernel_basis']
        self.assertEqual(len(basis),1)
        for t in range(-5,6):
            y=tuple(v+t*w for v,w in zip(x,basis[0]))
            self.assertEqual(y[0],5);self.assertEqual(project_state(r,y),result['quotient_state'])

    def test_outside_reachable_rejected(self):
        r=integral_machine([[[2,0],[0,3]]],[1,0],[[1,0]])
        with self.assertRaises(ValueError):project_state(r,[1,1])
        self.assertEqual(project_state(r,[5,0]),(5,))

    def test_zero_seed_and_zero_output(self):
        for s,h in (([0,0],[[1,1]]),([1,2],[[0,0]])):
            r=integral_machine([[[1,1],[0,1]]],s,h)
            self.assertEqual(r['minimal_dimension'],0)
            self.assertEqual(integral_power_output(r,2**63),(0,))
            self.assertEqual(observation_fibre(r,[])['status'],'INTEGER_AFFINE_FIBRE')
            self.assertTrue(verify_integral_machine(r))

    def test_future_visible_not_just_current_readout(self):
        r=integral_machine([[[1,1],[0,1]]],[0,1],[[1,0]])
        self.assertEqual(r['minimal_dimension'],2)
        self.assertNotEqual(project_state(r,[0,1]),project_state(r,[0,2]))
        w=distinguish_states(r,[0,1],[0,2]);self.assertEqual((w['word'],w['difference']),((0,),-1))
        hidden=integral_machine([[[2,0],[0,3]]],[1,1],[[1,0]])
        self.assertEqual(distinguish_states(hidden,[5,0],[5,100])['status'],'ALL_FUTURE_EQUAL')

    def test_all_moduli_including_old_denominators(self):
        r=integral_machine([[[1,1],[0,1]]],[0,2],[[4,0]])
        for modulus in (2,3,4,6,8,9,12,19):
            for n in (0,1,100,2**63):self.assertEqual(modular_power_output(r,n,modulus),(8*n%modulus,))
        r=integral_machine([[[2]]],[1],[[1]])
        self.assertEqual(modular_power_output(r,10**12,12),(pow(2,10**12,12),))
        with self.assertRaises(ValueError):modular_power_output(r,2,1)

    def test_noncommuting_orders(self):
        r=integral_machine([[[1,1],[0,1]],[[1,0],[1,1]]],[1,0],[[1,0]])
        self.assertEqual(integral_word_output(r,[0,1]),(1,))
        self.assertEqual(integral_word_output(r,[0,1],order='written'),(2,))

    def test_random_independent_all_words(self):
        rng=random.Random(6801)
        for n in range(1,5):
            for trial in range(4):
                ops=[[[rng.randint(-2,2) for _ in range(n)] for _ in range(n)] for _ in range(2)]
                s=[rng.randint(-2,2) for _ in range(n)];h=[[rng.randint(-2,2) for _ in range(n)]]
                r=integral_machine(ops,s,h)
                for length in range(5):
                    for word in itertools.product(range(2),repeat=length):
                        v=tuple(s)
                        for i in word:v=E.apply(ops[i],v)
                        self.assertEqual(integral_word_output(r,word),tuple(E.apply(h,v)))

    def test_shared_eleven_models(self):
        models=[Recurrence((1,1),(i,i+1)) for i in range(11)]
        r=integralize_machine(recurrence_batch(models))
        self.assertEqual((r['state_dimension'],r['minimal_dimension']),(22,2))
        for n in (0,1,10,100,1000):self.assertEqual(integral_power_output(r,n),tuple(m.nth(n) for m in models))
        self.assertTrue(all(type(x) is int for a in r['operators_minimal'] for row in a for x in row))

    def test_json_and_discovery_free_replay(self):
        r=json.loads(json.dumps(integral_machine([[[1,1],[0,1]]],[0,2],[[2,0]]),default=exact_json))
        with patch('perfectpower.integral_machine.minimal_machine',side_effect=AssertionError()),patch('perfectpower.integral_machine.smith_certificate',side_effect=AssertionError()),patch('perfectpower.integral_machine.E.inverse',side_effect=AssertionError()):
            self.assertTrue(verify_integral_machine(r));self.assertEqual(integral_word_output(r,[0,0]),(8,))

    def test_tamper_charts_operators_seed(self):
        r=integral_machine([[[1,1],[0,1]]],[0,2],[[2,0]])
        for key,value in (('selected_word_lattice_index',1),('minimal_dimension',1),('seed_minimal',[1,2]),('operators_minimal',[[[1,0],[0,1]]]),('observation_image_factors',[1,2]),('quotient',[[1,1],[0,1]])):
            t=deepcopy(r);t[key]=value;self.assertFalse(verify_integral_machine(t),key)
        for key in ('reachable_smith','observation_smith'):
            t=deepcopy(r);t[key]['operations'].append(['row','add',0,0,1]);self.assertFalse(verify_integral_machine(t))
        self.assertFalse(verify_integral_machine(None))

    def test_observation_fibre_independent_exhaustion(self):
        # Exhaustive states confirm precisely the recorded observation image.
        r=integral_machine([[[1,1],[0,1]]],[0,1],[[3,0]])
        for a,b in itertools.product(range(-4,5),repeat=2):
            f=observation_fibre(r,[a,b]);self.assertEqual(f['status']=='INTEGER_AFFINE_FIBRE',a%3==0 and b%3==0)

    def test_bad_inputs_and_budgets(self):
        for entry in (True,1.5,Q(1,2)):
            with self.assertRaises(ValueError):integral_machine([[[entry]]],[1],[[1]])
        with self.assertRaises(ReductionLimit):integral_machine([[[1,1],[0,1]]],[0,1],[[1,0]],operation_limit=1)
        with self.assertRaises(ValueError):integral_machine([[[1]]],[1],[[1]],entry_bit_limit=0)
        r=integral_machine([[[2]]],[1],[[1]])
        with self.assertRaises(WorkLimit):integral_power_output(r,10000)
        with self.assertRaises(WorkLimit):integral_word_output(r,[0]*4097)
        with self.assertRaises(ValueError):observation_fibre(r,[])

    def test_cli(self):
        p=subprocess.run([sys.executable,'-m','perfectpower','integral-machine','--operators','[[[1,1],[0,1]]]','--seed','[0,2]','--readouts','[[2,0]]','--word','[0,0]','--observations','[1,2]','--verify'],capture_output=True,text=True,env=os.environ)
        self.assertEqual(p.returncode,0,p.stderr);r=json.loads(p.stdout)
        self.assertTrue(r['certificate_replay']);self.assertEqual(r['output'],[8]);self.assertEqual(r['observation_fibre']['status'],'DIVISIBILITY_OBSTRUCTION')


if __name__=='__main__':unittest.main()
