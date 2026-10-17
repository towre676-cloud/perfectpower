"""Exact finite algebra, actual morphisms, and DFT recovery regression checks."""
import unittest
from fractions import Fraction as Q
from perfectpower.period_transport import PhaseObject
from perfectpower.phase_descent import (
    PhaseClass, PhaseSpace, PhaseLinearMap, StageFunctional, FiniteLinearCocone,
    colimit_witness, direct_sum_inclusions, inflate_space, induce_space,
    restrict_space, induce_map, restrict_map, frobenius_to_restriction,
    frobenius_from_restriction, dft_profile, cyclic_period_trace,
    induced_primitive_factorization, descent_receipt,
)


class PhaseDescentTests(unittest.TestCase):
    def test_canonical_phase_group_algebra(self):
        a = PhaseClass(((Q(7, 6), 2), (Q(1, 6), -1), (Q(-2, 3), 3)))
        self.assertEqual(a, PhaseClass(((Q(1, 6), 1), (Q(1, 3), 3))))
        self.assertEqual(a.conductor, 6)
        self.assertEqual(a*a.dual(), a.dual()*a)
        unit = PhaseClass(((0, 1),))
        self.assertEqual(a*unit, a)
        self.assertEqual((a+a.dual()).at_stage(30).minimal_conductor, 6)
        with self.assertRaises(ValueError):
            a.at_stage(4)

    def test_colimit_equality_has_finite_witness(self):
        a = PhaseObject(6, ((1, 2), (2, -1)))
        b = a.lift(30)
        c = a.lift(42)
        receipt = colimit_witness(a, b, c)
        self.assertEqual(receipt['common_stage'], 210)
        self.assertTrue(receipt['equal'])
        self.assertFalse(colimit_witness(a, PhaseObject(6, ((1, 3),)))['equal'])
        self.assertEqual(PhaseClass.from_stage(a), PhaseClass.from_stage(b))

    def test_finite_cocone_is_compatible_and_does_not_invent_values(self):
        two = StageFunctional(2, (3, 5))
        three = StageFunctional(3, (3, 7, 11))
        self.assertTrue(two.compatible(three))
        c = FiniteLinearCocone((two, three))
        value = PhaseClass(((0, -1), (Q(1, 2), 2), (Q(2, 3), 3)))
        self.assertEqual(c.evaluate(value), 40)
        self.assertEqual(c.receipt()['covered_basis_count'], 4)
        with self.assertRaises(ValueError):
            c.evaluate(PhaseClass(((Q(1, 6), 1),)))
        with self.assertRaises(ValueError):
            FiniteLinearCocone((two, StageFunctional(4, (3, 9, 6, 8))))
        self.assertEqual(two.evaluate(PhaseObject(8, ((4, 2),))), 10)

    def test_actual_matrix_composition_identity_and_faithful_forget(self):
        v = PhaseSpace(((Q(1, 3), 2), (0, 1)))
        w = PhaseSpace(((Q(1, 3), 1), (0, 2)))
        z = PhaseSpace(((Q(1, 3), 2), (0, 1)))
        f = PhaseLinearMap(v, w, {Q(1, 3): ((2, -1),), 0: ((3,), (4,))})
        g = PhaseLinearMap(w, z, {Q(1, 3): ((5,), (6,)), 0: ((7, 8),)})
        h = f.then(g)
        self.assertEqual(dict(h.blocks)[Q(1, 3)], ((Q(10), Q(-5)), (Q(12), Q(-6))))
        self.assertEqual(h.apply({0: (2,), Q(1, 3): (3, 4)})[0], (Q(106),))
        self.assertEqual(PhaseLinearMap.identity(v).then(f), f)
        self.assertEqual(f.then(PhaseLinearMap.identity(w)), f)
        self.assertEqual(f.dual().dual(), f)
        self.assertEqual(h.dual(), g.dual().then(f.dual()))
        self.assertNotEqual(f.forget(), PhaseLinearMap(v, w).forget())
        with self.assertRaises(ValueError):
            PhaseLinearMap(v, w, {Q(1, 2): ((1,),)})

    def test_direct_sum_maps_and_inclusions(self):
        a = PhaseSpace(((0, 2), (Q(1, 2), 1)))
        b = PhaseSpace(((0, 1), (Q(1, 3), 1)))
        i, j = direct_sum_inclusions(a, b)
        self.assertEqual(i.apply({0: (2, 3)})[0], (Q(2), Q(3), Q(0)))
        self.assertEqual(j.apply({0: (5,)})[0], (Q(0), Q(0), Q(5)))
        f, g = PhaseLinearMap.identity(a), PhaseLinearMap.identity(b)
        self.assertEqual(f.direct_sum(g), PhaseLinearMap.identity(a.direct_sum(b)))
        self.assertEqual(i.then(f.direct_sum(g)), i)
        self.assertEqual(j.then(f.direct_sum(g)), j)

    def test_tensor_maps_bifunctoriality_with_colliding_grades(self):
        a = PhaseSpace(((0, 1), (Q(1, 2), 1)))
        b = PhaseSpace(((0, 2), (Q(1, 2), 1)))
        f = PhaseLinearMap(a, a, {0: ((2,),), Q(1, 2): ((3,),)})
        g = PhaseLinearMap(b, b, {0: ((1, 2), (3, 4)), Q(1, 2): ((5,),)})
        self.assertEqual(PhaseLinearMap.identity(a).tensor(PhaseLinearMap.identity(b)),
                         PhaseLinearMap.identity(a.tensor(b)))
        self.assertEqual(f.tensor(g).then(f.tensor(g)), f.then(f).tensor(g.then(g)))
        self.assertEqual(a.tensor(b).phase_class(), a.phase_class()*b.phase_class())

    def test_induction_differs_from_inflation(self):
        v = PhaseSpace(((Q(1, 1680), 1),))
        self.assertEqual(inflate_space(v, 1680, 443520).dimension, 1)
        w = induce_space(v, 1680, 443520)
        self.assertEqual(w.dimension, 264)
        self.assertEqual(sum(d for x, d in w.multiplicities if x.denominator == 443520), 240)
        self.assertEqual(restrict_space(w, 443520, 1680), PhaseSpace(((Q(1, 1680), 264),)))

    def test_induction_and_restriction_are_actual_functors(self):
        a = PhaseSpace(((Q(1, 3), 2), (0, 1)))
        f = PhaseLinearMap(a, a, {Q(1, 3): ((2, 3), (4, 5)), 0: ((6,),)})
        self.assertEqual(induce_map(f.then(f), 3, 12), induce_map(f, 3, 12).then(induce_map(f, 3, 12)))
        big = induce_map(f, 3, 12)
        self.assertEqual(restrict_map(big.then(big), 12, 3), restrict_map(big, 12, 3).then(restrict_map(big, 12, 3)))
        self.assertEqual(induce_map(PhaseLinearMap.identity(a), 3, 12), PhaseLinearMap.identity(induce_space(a, 3, 12)))

    def test_frobenius_adjunction_stacks_and_splits_actual_maps(self):
        for n in range(1, 8):
            for d in (1, 2, 3, 5):
                N = n*d
                v = PhaseSpace(tuple((Q(k, n), 1+(k % 2)) for k in range(n)))
                w = PhaseSpace(tuple((Q(k, N), 1+(k % 3)) for k in range(N)))
                iv = induce_space(v, n, N)
                f = PhaseLinearMap(iv, w, tuple((x, tuple(tuple(Q(1+i+2*j+int(x*N), 7)
                              for j in range(iv.dims()[x])) for i in range(m))) for x, m in w.multiplicities))
                g = frobenius_to_restriction(f, v, w, n, N)
                self.assertEqual(frobenius_from_restriction(g, v, w, n, N), f)
                self.assertEqual(frobenius_to_restriction(frobenius_from_restriction(g, v, w, n, N), v, w, n, N), g)
                u = PhaseLinearMap(v, v, tuple((x, tuple(tuple(Q((i+1)*(j+2)) for j in range(m))
                                                     for i in range(m))) for x, m in v.multiplicities))
                self.assertEqual(frobenius_to_restriction(induce_map(u, n, N).then(f), v, w, n, N), u.then(g))
                z = PhaseLinearMap(w, w, tuple((x, tuple(tuple(Q(i == j)*(i+2) for j in range(m))
                                                     for i in range(m))) for x, m in w.multiplicities))
                self.assertEqual(frobenius_to_restriction(f.then(z), v, w, n, N), g.then(restrict_map(z, N, n)))

    def test_exact_dft_inverse_all_conductors_through_32(self):
        for n in range(1, 33):
            value = PhaseClass(tuple((Q(k, n), Q(((k*13+n) % 11)-5, 3)) for k in range(n)))
            self.assertEqual(dft_profile(value, n).inverse(), value)
        for n in (36, 40, 48, 60, 64):
            value = PhaseClass(((0, 2), (Q(1, n), -3), (Q(7, n), Q(2, 5))))
            self.assertEqual(dft_profile(value, n).inverse(), value)
        with self.assertRaises(ValueError):
            dft_profile(PhaseClass(((Q(1, 65), 1),)), 65)

    def test_full_complex_trace_retains_orientation(self):
        a = PhaseClass(((Q(1, 5), 1),))
        b = a.dual()
        self.assertNotEqual(dft_profile(a).traces, dft_profile(b).traces)
        # Their real parts agree: the symmetrized phase classes are identical.
        self.assertEqual(a+a.dual(), b+b.dual())
        trace = cyclic_period_trace(a, 2)
        self.assertEqual(trace.coefficient(1), a.at_stage().cyclotomic_trace(1))
        self.assertEqual(trace.packet()['domain'], 'Re(weight)>1')
        with self.assertRaises(ValueError):
            cyclic_period_trace(a, 1)

    def test_root_order_factorization_and_integrated_receipt(self):
        f = induced_primitive_factorization(1680, 264)
        self.assertEqual(f['total_degree'], 101376)
        self.assertEqual(f['factors'], [{'conductor': 40320, 'degree': 9216},
                                        {'conductor': 443520, 'degree': 92160}])
        self.assertEqual(induced_primitive_factorization(1, 6)['factors'],
                         [{'conductor': 1, 'degree': 1}, {'conductor': 2, 'degree': 1},
                          {'conductor': 3, 'degree': 2}, {'conductor': 6, 'degree': 2}])
        r = descent_receipt()
        self.assertTrue(r['dft_example']['recovered_exactly'])
        self.assertEqual(r['induction_dimensions']['nonprimitive_branches'], 24)


if __name__ == '__main__':
    unittest.main()
