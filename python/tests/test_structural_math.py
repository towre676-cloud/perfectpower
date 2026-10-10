import copy
import itertools
import json
import random
import subprocess
import sys
import unittest
from fractions import Fraction as Q
from math import isqrt, prod
from perfectpower.species import (SpeciesPopulation, species_of, invariants, minimum,
                                 occupations, from_occupations, power_divisor_count)
from perfectpower.inequality_certificates import *
from perfectpower.descent_squareclasses import (squareclasses, local_cover, real_obstructed,
    descent_candidates, check_descent, recover_cover, lift_cover, two_isogeny_rank_bound, check_rank_bound)
from perfectpower.psg_polynomial import parse
from perfectpower.divisor_square import WorkLimit


def brute_species(bound):
    """Independent integer traversal with divisor stripping."""
    result = set()
    for integer in range(1, bound+1):
        n, powers = integer, []
        for p in range(2, integer+1):
            if p*p > n:
                break
            e = 0
            while n % p == 0:
                n //= p; e += 1
            if e:
                powers.append(e)
        if n > 1:
            powers.append(1)
        result.add(tuple(sorted(powers, reverse=True)))
    return result


class SpeciesTests(unittest.TestCase):
    def test_complete_small_bounds(self):
        for bound in range(1, 150):
            expected = sorted(brute_species(bound))
            p = SpeciesPopulation(bound)
            self.assertEqual(p.count(), len(expected))
            self.assertEqual(p.page(0, 1000), expected)
            self.assertEqual([p.rank(s) for s in expected], list(range(p.count())))

    def test_intersected_filters(self):
        base = brute_species(3000)
        for power, free, tau, omega in itertools.product((1, 2, 3), (None, 3), (None, 1, 6, 12), (None, 4)):
            expected = sorted(a for a in base if all(e % power == 0 for e in a)
                and (free is None or all(e < free for e in a))
                and (tau is None or prod(e+1 for e in a) == tau)
                and (omega is None or sum(a) == omega))
            p = SpeciesPopulation(3000, power=power, power_free=free, divisor_count=tau, omega=omega)
            self.assertEqual(p.page(0, 1000), expected)
            for i, s in enumerate(expected):
                self.assertEqual(p.rank(s), i)

    def test_primorial_coordinates_and_lattices(self):
        for a in brute_species(1000):
            self.assertEqual(from_occupations(occupations(a)), a)
            packet = invariants(a)
            self.assertEqual(sum(packet['divisor_rank_polynomial']), prod(e+1 for e in a))
            self.assertEqual(packet['divisor_rank_polynomial'], packet['divisor_rank_polynomial'][::-1])
            self.assertEqual(species_of(minimum(a)), a)
            n = minimum(a)
            for d in (2, 3, 4):
                powers = [k**d for k in range(1, n+1) if k**d <= n and n % k**d == 0]
                self.assertEqual(power_divisor_count(a, d), len(powers))

    def test_identity_and_invalid_members(self):
        self.assertTrue(invariants(())['unit_all_power_exponents'])
        self.assertEqual(SpeciesPopulation(1, power=99999).page(), [()])
        p = SpeciesPopulation(100, power=2)
        for bad in ((1,), (2, 1), (8,)):
            with self.assertRaises(ValueError): p.rank(bad)
        with self.assertRaises(IndexError): p.select(p.count())
        for bad in (0, -1, True, 1.0):
            with self.assertRaises(ValueError): SpeciesPopulation(bad)

    def test_budget_and_large_bound(self):
        with self.assertRaises(WorkLimit): SpeciesPopulation(10**20, state_limit=1)
        p = SpeciesPopulation(10**30, power=2, divisor_count=81)
        self.assertGreater(p.count(), 0)
        for i in (0, p.count()-1):
            a = p.select(i)
            self.assertEqual(p.rank(a), i)
            self.assertLessEqual(minimum(a), 10**30)

    def test_existing_population_and_persistent_catalogue(self):
        from perfectpower.populations import ExactPopulation
        from perfectpower.catalogue import Catalogue
        p = ExactPopulation({'kind':'species','bound':1000,'power':2})
        for record in p.page(0,100):
            self.assertEqual(p.rank(record),record['rank'])
            self.assertEqual(p.locate(exponents=record['species']),record['rank'])
        sample = p.sample(min(5,p.count()),seed=71)
        self.assertEqual(len({r['rank'] for r in sample}),len(sample))
        self.assertEqual(p.partition(3,2)['stop'],p.count())
        optimum = p.optimize('divisor_count',sense='max')
        self.assertEqual(optimum['value'],max(r['values']['divisor_count'] for r in p.page(0,100)))
        bad = p.select(0); bad['values']['omega'] = 999
        with self.assertRaises(ValueError): p.rank(bad)
        with self.assertRaises(ValueError): p.restrict(True)
        import tempfile
        from pathlib import Path
        with tempfile.TemporaryDirectory() as directory:
            path = str(Path(directory)/'catalogue.sqlite')
            with Catalogue(path) as c:
                c.register('population',p.specification,'species')
            with Catalogue(path) as c:
                self.assertEqual(c.get('species').page(0,100),p.page(0,100))


class InequalityTests(unittest.TestCase):
    def test_schur_singular_and_exact_tiny_margin(self):
        p=toeplitz_certificate([1,1,1])
        self.assertEqual(p['schur_increments'],['1','0','0'])
        self.assertEqual(p['increment_ratios'],['0',None])
        self.assertTrue(check_toeplitz(p))
        tiny=Q(1,10**100)
        p=toeplitz_certificate([1,1-tiny])
        self.assertEqual(Q(p['schur_increments'][1]),2*tiny-tiny*tiny)
        self.assertTrue(check_toeplitz(p))
        bad=copy.deepcopy(p);bad['leading_determinants'][1]='0'
        with self.assertRaises(ValueError):check_toeplitz(bad)
    def test_random_psd_and_singular(self):
        rng = random.Random(527)
        for n in range(1, 8):
            for _ in range(8):
                B = tuple(tuple(Q(rng.randrange(-3, 4), rng.randrange(1, 4)) for _ in range(n)) for _ in range(n))
                a = multiply(B, transpose(B))
                self.assertTrue(check_psd(psd_certificate(a), a))
        p = psd_certificate([[0,0,0],[0,1,1],[0,1,1]])
        self.assertEqual(p['rank'], 1)
        self.assertFalse(p['positive_definite'])
        self.assertTrue(check_psd(p))

    def test_psd_negative_and_tampered(self):
        for a in ([[0,1],[1,0]], [[1,2],[2,1]], [[-1]], [[1,2],[0,1]]):
            with self.assertRaises(ValueError): psd_certificate(a)
        p = psd_certificate([[2,1],[1,2]])
        for key in ('D','L','matrix','rank','positive_definite'):
            bad = copy.deepcopy(p)
            if key == 'D': bad[key][0] = '-1'
            elif key in ('L','matrix'): bad[key][0][0] = '7'
            elif key == 'rank': bad[key] = 1
            else: bad[key] = False
            with self.assertRaises(ValueError): check_psd(bad)

    def test_quartic_squares_and_binding(self):
        vs = ('x','y')
        basis = [parse('x^2+y^2-1', vs), parse('x-y', vs)]
        p = squares_certificate(basis, ['1/3', 2])
        f = (basis[0]**2)/3+2*basis[1]**2
        self.assertTrue(check_gram(p, f))
        bound = lower_bound_certificate(f, terms=[((), p)])
        self.assertTrue(check_lower_bound(bound, f))
        with self.assertRaises(ValueError): check_lower_bound(bound, f+1)
        bad = copy.deepcopy(p); bad['psd']['matrix'][0][0] = '1'
        with self.assertRaises(ValueError): check_gram(bad)

    def test_constrained_and_product_bounds(self):
        vs = ('x','y'); f = parse('3-x^2-y^2', vs); g = parse('1-x^2-y^2', vs)
        one = squares_certificate([parse('1', vs)])
        p = lower_bound_certificate(f, 2, inequalities=[g], terms=[((0,), one)])
        self.assertTrue(check_lower_bound(p, f, inequalities=[g]))
        with self.assertRaises(ValueError): check_lower_bound(p, inequalities=[-g])
        x, y = parse('x',vs), parse('y',vs)
        p = lower_bound_certificate(x*y, inequalities=[x,y], terms=[((0,1), one)])
        self.assertTrue(check_lower_bound(p))

    def test_infeasibility_from_equality(self):
        vs = ('x','y'); x, y = parse('x',vs), parse('y',vs)
        equation = x*x+y*y+1
        p = infeasibility_certificate(equalities=[equation], terms=[((), squares_certificate([x,y]))],
                                      ideal=[(0, parse('-1',vs))])
        self.assertTrue(check_lower_bound(p))
        self.assertEqual(Polynomial.from_packet(p['target']).evaluate([0,0]), -1)

    def test_exact_quadratic_minima_and_ties(self):
        f = parse('(x-y-2)^2/3+5', ('x','y'))
        p = quadratic_minimum(f)
        self.assertTrue(check_lower_bound(p['bound'], f))
        self.assertEqual(p['bound']['lower'], '5')
        self.assertEqual(len(p['tie_directions']), 1)
        point = list(map(Q,p['point'])); direction = list(map(Q,p['tie_directions'][0]))
        for t in (-100, -1, 0, 3, 999):
            self.assertEqual(f.evaluate([x+t*v for x,v in zip(point,direction)]), 5)
        for expr in ('-x^2','x','x^2+y','x^4'):
            with self.assertRaises(ValueError): quadratic_minimum(parse(expr, ('x','y')))

    def test_lyapunov_exact_synthesis_and_source_binding(self):
        A = [[-1,10],[0,-2]]
        p = synthesize_lyapunov(A, '1/4')
        self.assertTrue(check_lyapunov(p, A))
        self.assertTrue(p['metric']['positive_definite'])
        with self.assertRaises(ValueError): check_lyapunov(p, [[1,10],[0,-2]])
        with self.assertRaises(ValueError): synthesize_lyapunov([[1]])
        with self.assertRaises(ValueError): synthesize_lyapunov([[-1]], 2)
        bad = copy.deepcopy(p); bad['alpha'] = '3'
        with self.assertRaises(ValueError): check_lyapunov(bad)

    def test_exact_inputs_only_and_budget(self):
        for a in ([[1.0]], [[True]], [[1,2]], []):
            with self.assertRaises(ValueError): psd_certificate(a)
        with self.assertRaises(WorkLimit): synthesize_lyapunov([[-int(i==j) for j in range(9)] for i in range(9)])


class DescentTests(unittest.TestCase):
    def test_native_rank_bounds_from_both_curves(self):
        for a,b,upper in ((0,-1,0),(0,1,0),(-5,4,0),(0,-2,1),(0,-25,2)):
            p=two_isogeny_rank_bound(a,b)
            self.assertEqual(p['rank_upper_bound'],upper)
            self.assertTrue(check_rank_bound(p,a,b))
            self.assertEqual(p['rank_exact'],0 if upper==0 else None)
            bad=copy.deepcopy(p);bad['rank_upper_bound']+=1
            with self.assertRaises(ValueError):check_rank_bound(bad)
    def test_complete_signed_divisors(self):
        self.assertEqual(squareclasses(0,-72), [-6,-3,-2,-1,1,2,3,6])
        with self.assertRaises(ValueError): squareclasses(2,1)
        with self.assertRaises(WorkLimit): squareclasses(0,1000003*1000033,work_limit=1)

    def test_projective_charts_against_all_primitive_pairs(self):
        for a,b in ((0,-2),(-5,4),(0,1),(3,-6)):
            for d in squareclasses(a,b):
                for prime,depth in ((2,3),(3,2),(5,1)):
                    p = local_cover(a,b,d,prime,depth)
                    m = prime**depth; squares = {w*w%m for w in range(m)}
                    brute = any((u%prime or v%prime) and
                        (d*u**4+a*u*u*v*v+(b//d)*v**4)%m in squares
                        for u in range(m) for v in range(m))
                    self.assertEqual(p['obstructed'], not brute)

    def test_actual_rational_point_recovery(self):
        for a,b in ((0,-2),(-5,4),(0,-1)):
            for denominator in range(1,7):
                for numerator in range(-30,31):
                    x = Q(numerator, denominator)
                    y2 = x*(x*x+a*x+b)
                    if y2 < 0: continue
                    u,v = isqrt(y2.numerator), isqrt(y2.denominator)
                    if u*u != y2.numerator or v*v != y2.denominator: continue
                    for y in (Q(u,v), -Q(u,v)):
                        p = recover_cover(a,b,x,y)
                        if x:
                            self.assertEqual(Q(p['x']), x); self.assertEqual(Q(p['y']), y)
                            self.assertFalse(real_obstructed(a,b,p['d']))
                            for prime in (2,3,5):
                                self.assertFalse(local_cover(a,b,p['d'],prime)['obstructed'])
                        else: self.assertEqual(p['exceptional'], '(0,0)')
        self.assertEqual(lift_cover(0,-2,2,1,1,1)['y'], '2')

    def test_tamper_scope_and_real_obstruction(self):
        p = descent_candidates(0,1)
        self.assertTrue(check_descent(p,0,1))
        self.assertEqual(p['survivors'], [1])
        self.assertTrue(real_obstructed(0,1,-1))
        for row in p['classes']:
            self.assertIn(row['status'], ('excluded','unresolved'))
        bad = copy.deepcopy(p); bad['survivors'] = []
        with self.assertRaises(ValueError): check_descent(bad)
        with self.assertRaises(WorkLimit): descent_candidates(0,1,places=[(257,3)])
        with self.assertRaises(ValueError): lift_cover(0,-2,2,1,1,2)
        for places in ([[-1,2]], [[4,1]], [[2,-1]], [[2,1,3]], [[True,1]]):
            with self.assertRaises(ValueError): descent_candidates(0,1,places=places)


class ConsoleTests(unittest.TestCase):
    def test_public_commands(self):
        calls = [('species','--integer','360'), ('species-population','--bound','1000','--ranks','[0,2]'),
                 ('quadratic-minimum','--variables','x,y','--objective','(x-y)^2+2'),
                 ('matrix-psd','--matrix','[[1,1],[1,1]]'),
                 ('linear-stability','--matrix','[[-1,10],[0,-2]]'),
                 ('toeplitz-schur','--moments','[1,"1/2","1/4"]'),
                 ('inequality-bound','--variables','x,y','--objective','3-x^2-y^2','--lower','2',
                  '--inequalities','["1-x^2-y^2"]','--squares','[{"indices":[0],"polynomials":["1"]}]'),
                 ('two-torsion-descent','--a','0','--b','-2')]
        for call in calls:
            r = subprocess.run([sys.executable,'-m','perfectpower',*call],capture_output=True,text=True)
            self.assertEqual(r.returncode,0,r.stderr)
            self.assertIsInstance(json.loads(r.stdout),dict)


if __name__ == '__main__':
    unittest.main()
