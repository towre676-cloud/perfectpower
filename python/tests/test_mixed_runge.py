import random
import unittest
from perfectpower.mixed_runge import quadratic_roots, solve_example, equation


class MixedRungeTests(unittest.TestCase):
    def test_complete_published_points(self):
        r = solve_example()
        self.assertEqual(r['points'], [(-1,-4),(-1,-1),(-1,1),(-1,2)])
        self.assertEqual(r['fibres_examined'], 49)
        self.assertFalse(r['execution_verified'])

    def test_projection_random(self):
        rng = random.Random(508)
        for _ in range(500):
            a, b, c = [rng.randint(-20, 20) for _ in range(3)]
            if (a,b,c) == (0,0,0):
                continue
            roots = quadratic_roots(a,b,c)
            self.assertTrue(all(a*x*x+b*x+c == 0 for x in roots))
            self.assertEqual([x for x in roots if -50 <= x <= 50],
                             [x for x in range(-50,51) if a*x*x+b*x+c == 0])

    def test_no_coordinate_scan(self):
        n = 10**40
        self.assertEqual(quadratic_roots(1,-2*n,n*n), [n])

    def test_degenerate_fibres(self):
        self.assertEqual(quadratic_roots(0,-15,-7), [])
        self.assertEqual(quadratic_roots(0,-3,6), [2])
        self.assertEqual(quadratic_roots(0,0,3), [])
        with self.assertRaises(ValueError):
            quadratic_roots(0,0,0)

    def test_independent_rectangle_comparison(self):
        self.assertEqual(solve_example()['points'],
                         [(x,y) for x in range(-100,101) for y in range(-100,101)
                          if equation(x,y)])

    def test_integrality_filter(self):
        self.assertEqual(quadratic_roots(4,0,-1), [])
        self.assertEqual(quadratic_roots(-1,0,4), [-2,2])


if __name__ == '__main__':
    unittest.main()
