import copy
import itertools
import json
import random
import subprocess
import sys
import unittest
from fractions import Fraction as Q
from pathlib import Path
from perfectpower.factored_sieve import (power_residue,prime_power_table,verify_prime_power_table,
    factored_cover,verify_factored_cover,scan_factored,adaptive_cover)
from perfectpower.residue_cover import residue_cover,scan_cover,candidate_count,evaluate,verify_cover
from perfectpower.observable_machine import minimal_machine,verify_machine,word_output,recurrence_batch,power_outputs
from perfectpower.recurrence import Recurrence
from perfectpower.deep_recovery_cli import exact_json
from perfectpower.divisor_square import WorkLimit
from perfectpower.core import integer_power_root
from perfectpower.arithmetic_engine import ArithmeticEngine,verify_result

ROOT=Path(__file__).resolve().parents[2]


class LocalDepths(unittest.TestCase):
    def test_power_images_exhaustive_including_singular_dyadic_cases(self):
        for p,a,d in itertools.product((2,3,5,7),(1,2,3,4),range(2,17)):
            q=p**a;image={pow(x,d,q) for x in range(q)}
            self.assertEqual([x for x in range(q) if power_residue(x,d,p,a)],sorted(image),(p,a,d))

    def test_large_depth_predicate_without_enumeration(self):
        for p in (2,3,5,7):
            for d in (2,3,4,6,16):
                for v in (-11,-3,0,1,4,10):self.assertTrue(power_residue(v**d,d,p,100))
        self.assertFalse(power_residue(2,2,2,100));self.assertFalse(power_residue(3,2,2,100))
        self.assertTrue(power_residue(1+2**6,16,2,100))
        self.assertFalse(power_residue(1+2**5,16,2,100))

    def test_depth_table_against_full_polynomial_witness_enumeration(self):
        for f,d,p,a in itertools.product(([0,1],[1,1,1],[-1,0,1],[3,0,0,1]),(2,3,4),(2,3,5),(1,2,3)):
            t=prime_power_table(f,d,p,a);q=p**a;image={pow(y,d,q) for y in range(q)}
            self.assertEqual(list(t['allowed']),[x for x in range(q) if evaluate(f,x)%q in image])
            self.assertTrue(verify_prime_power_table(f,d,json.loads(json.dumps(t))))

    def test_levels_and_tamper(self):
        t=prime_power_table([0,1],4,2,8)
        self.assertEqual([q for q,_ in t['levels']],[2**a for a in range(1,9)])
        x=copy.deepcopy(t);x['levels']=x['levels'][:-1];self.assertFalse(verify_prime_power_table([0,1],4,x))
        x=copy.deepcopy(t);x['allowed']=();self.assertFalse(verify_prime_power_table([0,1],4,x))
        x=copy.deepcopy(t);x['tested_lifts']+=1;self.assertFalse(verify_prime_power_table([0,1],4,x))

    def test_parameter_and_budget_failures(self):
        for p,a,d in ((4,1,2),(2,0,2),(2,1,1),(True,1,2),(2,True,2)):
            with self.assertRaises(ValueError):power_residue(1,d,p,a)
        with self.assertRaises(WorkLimit):prime_power_table([0,1],2,2,17)
        with self.assertRaises(WorkLimit):prime_power_table([0,1],2,2,8,work_limit=1)


class FactoredSearches(unittest.TestCase):
    def test_bounded_points_against_unfiltered_scan(self):
        rng=random.Random(264)
        for _ in range(30):
            f=[rng.randint(-9,9) for _ in range(rng.randint(2,7))];f[-1]=rng.choice((-3,1,2));d=rng.choice((2,3,4,5,6))
            c=factored_cover(residue_cover(f,d));r=scan_factored(c,-50,50)
            wanted=[]
            for x in range(-50,51):
                y=integer_power_root(evaluate(f,x),d)
                if y is not None:wanted.extend((x,v) for v in sorted({y,-y} if d%2==0 else {y}))
            self.assertEqual(r['points'],wanted);self.assertTrue(verify_cover(c))
            self.assertEqual(candidate_count(c,-50,50),r['candidates_checked'])

    def test_huge_combined_modulus_without_global_residue_table(self):
        f=[1,1]+[0]*62+[1];b=residue_cover(f,10);c=factored_cover(b)
        self.assertGreater(c['modulus'],10**13);self.assertFalse(c['combined_residue_table_materialized'])
        old=scan_cover(b,-10000,10000);new=scan_cover(c,-10000,10000)
        self.assertEqual(new['points'],old['points']);self.assertEqual(new['candidates_checked'],16)
        self.assertGreater(old['candidates_checked'],100*new['candidates_checked'])
        self.assertTrue(verify_factored_cover(json.loads(json.dumps(c))))

    def test_non_coprime_depths_and_nonempty_local_does_not_mean_solution(self):
        c=factored_cover(residue_cover([101,0,1],2),((2,5),(2,6),(3,2)))
        r=scan_factored(c,-40,40);self.assertFalse(c['global_obstruction']);self.assertEqual(r['points'],[])
        self.assertGreater(r['candidates_checked'],0)

    def test_empty_depth_table_is_global_obstruction(self):
        c=factored_cover(residue_cover([3,0,2],2,moduli=(5,)),((2,4),))
        self.assertTrue(c['global_obstruction']);self.assertEqual(scan_factored(c,-10**100,10**100)['points'],[])
        self.assertTrue(verify_factored_cover(c))

    def test_filters_and_root_budget_fail_without_partial_answers(self):
        c=factored_cover(residue_cover([0,0,1],2))
        with self.assertRaises(WorkLimit):scan_factored(c,-100,100,filter_limit=1)
        with self.assertRaises(WorkLimit):scan_factored(c,-100,100,work_limit=1)
        with self.assertRaises(ValueError):scan_factored(c,1,-1)
        with self.assertRaises(ValueError):factored_cover(c)
        with self.assertRaises(ValueError):factored_cover(residue_cover([0,1],2),((2,3),(2,3)))

    def test_cover_tamper_rejected(self):
        self.assertFalse(verify_cover([]));self.assertFalse(verify_cover(None))
        c=factored_cover(residue_cover([1,0,1],2))
        changes=[lambda x:x.__setitem__('modulus',x['modulus']+1),lambda x:x.__setitem__('global_obstruction',True),
            lambda x:x.__setitem__('execution_verified',True),lambda x:x['tables'][0].__setitem__('allowed',[]),
            lambda x:x['base'].__setitem__('allowed',[]),lambda x:x.__setitem__('base',[])]
        for change in changes:
            x=copy.deepcopy(c);change(x);self.assertFalse(verify_factored_cover(x))

    def test_adaptation_preserves_small_leaves(self):
        b=residue_cover([-199,1,1,1,1],2);self.assertIs(adaptive_cover(b,-42,42),b)
        self.assertEqual(adaptive_cover(b,-100000,100000)['schema'],'pp-factored-cover/1')

    def test_engine_complete_with_far_exceptional_root_and_new_filters(self):
        f=[-10**20,1,0,0,0,0,1];r=ArithmeticEngine().solve(f,3,strict=True)
        self.assertEqual(r['points'],[(10**20,10**40)]);self.assertTrue(verify_result(r))
        self.assertEqual(r['statistics']['candidates_checked'],120)
        self.assertEqual(r['statistics']['sieve_candidates_tested'],4763)
        self.assertGreater(r['proof']['leaf']['cover']['modulus'],10**13)
        self.assertTrue(verify_result(json.loads(json.dumps(r))))


class MinimalMachines(unittest.TestCase):
    def test_reachable_and_future_invisible_directions(self):
        r=minimal_machine([[[2,0,0],[0,3,0],[0,0,7]]],[1,1,0],[[1,0,0]])
        self.assertEqual((r['state_dimension'],r['reachable_dimension'],r['minimal_dimension']),(3,2,1))
        for i in range(20):self.assertEqual(power_outputs(r,i),(Q(2**i),))
        self.assertTrue(verify_machine(r));self.assertNotEqual(r['hankel_determinant'],0)

    def test_future_observation_cannot_be_removed(self):
        r=minimal_machine([[[0,1],[1,0]]],[1,0],[[0,1]])
        self.assertEqual(r['minimal_dimension'],2);self.assertEqual(word_output(r,[]),(Q(0),))
        self.assertEqual(word_output(r,[0]),(Q(1),))

    def test_noncommuting_execution_direction(self):
        r=minimal_machine([[[1,1],[0,1]],[[1,0],[1,1]]],[1,0],[[1,0]])
        self.assertEqual(word_output(r,[0,1]),(Q(1),));self.assertEqual(word_output(r,[0,1],order='written'),(Q(2),))
        self.assertEqual(word_output(r,[0,1],original=True),word_output(r,[0,1]))

    def test_all_small_noncommuting_words_independently(self):
        rng=random.Random(1247)
        for n in range(1,6):
            ops=[[[rng.randrange(-1,2) for _ in range(n)] for _ in range(n)] for _ in range(2)]
            seed=[rng.randrange(-2,3) for _ in range(n)];h=[[rng.randrange(-2,3) for _ in range(n)] for _ in range(2)]
            r=minimal_machine(ops,seed,h);self.assertTrue(verify_machine(r))
            for length in range(5):
                for word in itertools.product(range(2),repeat=length):
                    v=seed
                    for i in word:v=[sum(x*y for x,y in zip(row,v)) for row in ops[i]]
                    expected=tuple(sum(x*y for x,y in zip(row,v)) for row in h)
                    self.assertEqual(word_output(r,word),expected)

    def test_zero_seed_and_zero_readout_machines(self):
        for seed,h in (([0,0],[[1,1]]),([1,2],[[0,0]])):
            r=minimal_machine([[[2,1],[0,3]]],seed,h)
            self.assertEqual(r['minimal_dimension'],0);self.assertTrue(verify_machine(r))
            self.assertEqual(word_output(r,[0]*10),(Q(0),));self.assertEqual(power_outputs(r,10**18),(Q(0),))

    def test_rational_serialization_and_multiple_readouts(self):
        r=minimal_machine([[[Q(1,2),0],[0,Q(1,3)]]],[1,1],[[1,1],[1,-1]])
        r=json.loads(json.dumps(r,default=exact_json));self.assertTrue(verify_machine(r))
        self.assertEqual(power_outputs(r,4),(Q(1,16)+Q(1,81),Q(1,16)-Q(1,81)))

    def test_supplied_recurrences_share_states_for_every_index(self):
        models=[Recurrence((1,1),(i,2*i+1)) for i in range(11)];r=recurrence_batch(models)
        self.assertEqual((r['state_dimension'],r['minimal_dimension']),(22,2))
        for n in (0,1,2,10,100,1000):self.assertEqual(power_outputs(r,n),tuple(m.nth(n) for m in models))

    def test_hankel_witness_and_intertwiner_tamper(self):
        r=minimal_machine([[[2,0,0],[0,3,0],[0,0,7]]],[1,1,0],[[1,0,0]])
        changes=[lambda x:x['operators_minimal'][0][0].__setitem__(0,3),lambda x:x['reachable_basis'][0].__setitem__(0,2),
            lambda x:x['readouts_minimal'][0].__setitem__(0,0),lambda x:x.__setitem__('hankel_determinant','0'),
            lambda x:x.__setitem__('hankel_columns',[]),lambda x:x.__setitem__('state_words',[]),
            lambda x:x.__setitem__('readout_words',[]),lambda x:x.__setitem__('word_order','written'),
            lambda x:x.__setitem__('execution_verified',True)]
        for change in changes:
            x=json.loads(json.dumps(r,default=exact_json));change(x);self.assertFalse(verify_machine(x))

    def test_shape_work_and_arithmetic_budgets(self):
        with self.assertRaises(WorkLimit):minimal_machine([[[0,1],[1,0]]],[1,0],[[1,0]],product_limit=1)
        for ops,seed,h in (([[[1.0]]],[1],[[1]]),([[[1]]],[True],[[1]]),([[[1]]],[1],[])):
            with self.assertRaises(ValueError):minimal_machine(ops,seed,h)
        r=minimal_machine([[[2]]],[1],[[1]])
        with self.assertRaises(ValueError):power_outputs(r,-1)
        with self.assertRaises(ValueError):word_output(r,[1])
        with self.assertRaises(WorkLimit):word_output(r,[0]*5000)
        with self.assertRaises(WorkLimit):power_outputs(r,1000000)

    def test_cli_commands(self):
        cases=[['observable-machine','--operators','[[[2,0],[0,3]]]','--seed','[1,1]','--readouts','[[1,0]]','--word','[0,0]','--verify'],
            ['recurrence-batch','--models','[{"coefficients":[1,1],"initial":[0,1]},{"coefficients":[1,1],"initial":[2,1]}]','--index','10','--verify'],
            ['factored-scan','--coeff','[1,0,1]','--lo','-100','--hi','100','--verify']]
        for args in cases:
            p=subprocess.run([sys.executable,'-m','perfectpower',*args],capture_output=True,text=True,cwd=ROOT,check=True)
            self.assertTrue(json.loads(p.stdout)['certificate_replay'])


if __name__=='__main__':unittest.main()
