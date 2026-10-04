import unittest
from importlib.util import find_spec

@unittest.skipUnless(find_spec('numpy') and find_spec('scipy'),'optional analytic backend unavailable')
class SurfacePeriodTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        from perfectpower.conformal_mesh import hyperelliptic_mesh
        from perfectpower.surface_periods import symplectic_period_matrix
        cls.coeff=[0,-1,0,0,0,1]
        cls.mesh=hyperelliptic_mesh(cls.coeff,6)
        cls.periods=symplectic_period_matrix(cls.mesh)

    def test_actual_riemann_relations(self):
        p=self.periods
        self.assertLess(p['symmetry_residual'],1e-10)
        self.assertLess(p['first_bilinear_relative_residual'],1e-10)
        self.assertGreater(min(p['imaginary_part_eigenvalues']),0)
        self.assertGreater(min(p['second_bilinear_eigenvalues']),0)
        self.assertTrue(all(c['sheet_transport_checked'] for c in p['cycles']))
        self.assertFalse(p['quadrature_error_certified'])

    def test_contour_deformation(self):
        from perfectpower.surface_periods import symplectic_period_matrix
        import numpy as np
        p=symplectic_period_matrix(self.mesh,1e-11,(.2,.3,.5))
        decode=lambda rows:np.array([[complex(*z) for z in row] for row in rows])
        self.assertLess(np.max(np.abs(decode(p['generator_periods'])-decode(self.periods['generator_periods']))),1e-9)

    def test_known_square_torus_and_higher_genus(self):
        from perfectpower.conformal_mesh import hyperelliptic_mesh
        from perfectpower.surface_periods import symplectic_period_matrix
        p=symplectic_period_matrix(hyperelliptic_mesh([-1,0,0,0,1],6))
        self.assertLess(abs(complex(*p['tau'][0][0])-1j),1e-10)
        # Independent real Euler integral checks absolute period scale.
        from scipy.integrate import quad
        from math import sqrt
        euler,_=quad(lambda t:1/sqrt(1-t**4),0,1,epsabs=1e-11,epsrel=1e-11)
        self.assertAlmostEqual(abs(complex(*p['A'][0][0])),2*sqrt(2)*euler,places=9)
        for degree in (7,9):
            p=symplectic_period_matrix(hyperelliptic_mesh([-1]+[0]*(degree-1)+[1],6))
            self.assertEqual(p['genus'],(degree-1)//2)
            self.assertLess(p['symmetry_residual'],1e-9)
            self.assertGreater(min(p['imaginary_part_eigenvalues']),0)

    def test_general_path_inverse_and_subdivision(self):
        from perfectpower.surface_periods import integrate_path
        import numpy as np
        a=.3+.7j;b=.6+.8j
        for coeff,d in [(self.coeff,2),([-1,0,0,1],3),([0,-1,2,-1,0,1,-2,1],2)]:
            p=integrate_path(coeff,d,[a,b]);q=integrate_path(coeff,d,[b,a],sheet=p['end_sheet'])
            r=integrate_path(coeff,d,[a,(a+b)/2,b])
            decode=lambda p:np.array([complex(*z) for z in p['period_vector']])
            self.assertLess(np.max(np.abs(decode(p)+decode(q))),1e-10)
            self.assertLess(np.max(np.abs(decode(p)-decode(r))),1e-10)

    def test_inverse_chart_and_branch_transport(self):
        from perfectpower.surface_periods import integrate_path
        p=integrate_path(self.coeff,2,[3+3j,4+4j]);q=integrate_path(self.coeff,2,[3+3j,4+4j],['inverse'])
        for a,b in zip(p['period_vector'],q['period_vector']):self.assertLess(abs(complex(*a)-complex(*b)),1e-10)
        # This small polygon circles x=1 once: a square root changes sheet.
        points=[1.2+.2j,.8+.2j,.8-.2j,1.2-.2j,1.2+.2j]
        p=integrate_path(self.coeff,2,points)
        self.assertEqual(p['end_sheet'],1);self.assertFalse(p['closed_lift'])
        q=integrate_path(self.coeff,2,points+points[1:])
        self.assertTrue(q['closed_lift'])
        self.assertLess(abs(complex(*q['period_vector'][0])),1e-10)

    def test_canonical_metric_and_lattice_shift(self):
        from perfectpower.surface_periods import bergman_metric,integrate_path,jacobian_coordinates
        import numpy as np
        p=self.periods;m=bergman_metric(p,.3+.7j)
        self.assertGreater(m['density_in_x_chart'],0);self.assertLessEqual(m['curvature'],0)
        q=integrate_path(self.coeff,2,[.3+.7j,.6+.8j]);u=jacobian_coordinates(p,q)
        a=np.array([[complex(*z) for z in row] for row in p['A']]);b=np.array([[complex(*z) for z in row] for row in p['B']])
        v=np.array([complex(*z) for z in q['period_vector']])+a@np.array([2,-3])+b@np.array([-1,4])
        shifted=jacobian_coordinates(p,{'period_vector':[[z.real,z.imag] for z in v]})
        for x,y in zip(u['reduced_coordinates'],shifted['reduced_coordinates']):self.assertLess(abs(complex(*x)-complex(*y)),1e-10)

    def test_metric_is_symplectic_basis_invariant(self):
        import numpy as np
        from perfectpower.surface_periods import bergman_metric
        p=self.periods;swap=dict(p)
        a=np.array([[complex(*z) for z in row] for row in p['A']]);b=np.array([[complex(*z) for z in row] for row in p['B']])
        tau=np.linalg.solve(b,-a)
        encode=lambda x:[[[float(z.real),float(z.imag)] for z in row] for row in x]
        swap.update(A=encode(b),B=encode(-a),tau=encode(tau))
        for z in [.3+.7j,2+1j]:
            x=bergman_metric(p,z);y=bergman_metric(swap,z)
            self.assertAlmostEqual(x['density_in_x_chart'],y['density_in_x_chart'],places=12)
            self.assertAlmostEqual(x['curvature'],y['curvature'],places=10)

    def test_domains(self):
        from perfectpower.surface_periods import integrate_path,CycleIntegrator
        for pts,charts in [([0j,1j],['inverse']),([.5,1.5],None),([1j],None)]:
            with self.assertRaises(ValueError):integrate_path(self.coeff,2,pts,charts)
        with self.assertRaises(ValueError):CycleIntegrator(self.mesh,center_weights=(1,0,0))
