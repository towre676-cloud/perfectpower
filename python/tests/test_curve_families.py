"""Independent algebra, classical period checks, path exclusions and service."""
import copy
import itertools
import math
import random
import tempfile
import unittest
from fractions import Fraction as Q
from pathlib import Path
from perfectpower import polyalg as P,exact_linear as E
from perfectpower.core import mul
from perfectpower.rational_functions import RationalFunction as RF,AlgebraBudget,solve_many
from perfectpower.curve_families import CurveFamily
from perfectpower.family_continuation import pullback,path_certificate
from perfectpower.catalogue import Catalogue,encoded
from perfectpower.query_service import dispatch
from perfectpower.populations import ExactPopulation
from perfectpower.divisor_square import WorkLimit

LEGENDRE=dict(coefficients=[[0],[0,1],[-1,-1],[1]])
GENUS_TWO=dict(coefficients=[[0,1],[-1],[0],[0],[0],[1]])
try:
    import numpy as np
    import scipy
    NUMERICAL=True
except ImportError:NUMERICAL=False


class CurveFamilies(unittest.TestCase):
    def test_rational_field_canonical_and_identities(self):
        rng=random.Random(662)
        for _ in range(40):
            a=RF([rng.randrange(-3,4) for _ in range(4)],[2,1])
            b=RF([rng.randrange(-3,4) for _ in range(3)],[3,0,1])
            self.assertEqual((a+b)-b,a);self.assertEqual(a*b,b*a)
            self.assertEqual((a*b).derivative(),a.derivative()*b+a*b.derivative())
            if b:self.assertEqual((a/b)*b,a)
            for t in (Q(0),Q(1,3),Q(2)):
                self.assertEqual((a*b).evaluate(t),a.evaluate(t)*b.evaluate(t))
        self.assertEqual(RF([0,2,2],[0,2]).packet(),dict(numerator=['1','1'],denominator=['1']))
        with self.assertRaises(ValueError):RF([1],[0])
        with self.assertRaises(ValueError):RF.parse(1.2)
        with self.assertRaises(WorkLimit):RF([1]*4,budget=AlgebraBudget(degree_limit=2))

    def test_fraction_field_linear_system(self):
        t=RF([0,1]);one=RF([1]);a=[[t,one],[one,t]]
        answer=solve_many(a,[[one],[t]])
        self.assertEqual(answer,[[RF([0])],[one]])
        self.assertIsNone(solve_many([[one],[one]],[[one],[t]]))

    def test_legendre_connection_and_classical_operator(self):
        f=CurveFamily(LEGENDRE)
        self.assertEqual(f.discriminant,P.poly([0,0,1,-2,1]))
        self.assertEqual(f.observable()['polynomial_operator'],[[1],[-4,8],[0,-4,4]])
        from perfectpower.exact_operators import Weyl
        packet=f.observable();operator=Weyl({(v['t_degree'],v['D_degree']):Q(v['coefficient']) for v in packet['weyl_terms']})
        series=[Q(math.comb(2*n,n)**2,16**n) for n in range(40)]
        self.assertEqual(operator.act_series(series,36),[Q(0)]*36)
        self.assertEqual([b['kind'] for b in f.packet['basis']],['holomorphic','second_kind'])
        for t in (Q(1,4),Q(1,2),Q(3,4)):
            for i in range(2):
                self.assertEqual(f.connection[i][i].evaluate(t),(-1 if i==0 else 1)/(2*(t-1)))

    def test_genus_two_known_matrix_and_scalar(self):
        f=CurveFamily(GENUS_TWO);self.assertEqual(f.discriminant,P.poly([-256,0,0,0,3125]))
        for t in (Q(0),Q(1,5),Q(-1,3),Q(2)):
            d=P.evaluate(f.discriminant,t)
            self.assertEqual([a.evaluate(t) for a in f.connection[0]],[-Q(1875,2)*t**3/d,-250*t*t/d,200*t/d,480/d])
        self.assertEqual(f.observable()['polynomial_operator'],[[84645],[0,1380000],[0,0,1845000],[0,0,0,600000],[-4096,0,0,0,50000]])

    def test_random_family_specialization_independent_rational_elimination(self):
        rng=random.Random(771)
        for m in (3,5,7):
            for _ in range(2):
                coefficients=[[rng.randrange(-2,3),rng.randrange(-2,3)] for _ in range(m)]+[[1]]
                f=CurveFamily(dict(coefficients=coefficients))
                for t in (Q(-2),Q(1,3),Q(3)):
                    if not P.evaluate(f.discriminant,t):continue
                    p=P.poly(a.evaluate(t) for a in f.f);dt=P.poly(a.derivative().evaluate(t) for a in f.f);dx=P.derivative(p)
                    self.assertEqual((-1)**(m*(m-1)//2)*P.resultant(p,P.derivative(p)),P.evaluate(f.discriminant,t))
                    size=2*m-1;columns=[]
                    for j in range(m-1):columns.append(list((Q(0),)*j+p)+[Q(0)]*(size-j-len(p)))
                    for k in range(m):
                        r=P.poly([0]*k+[1]);v=P.add(mul(P.derivative(r),p),P.scale(mul(r,dx),-Q(1,2)))
                        columns.append(list(v)+[Q(0)]*(size-len(v)))
                    matrix=E.transpose(columns)
                    for i in range(m-1):
                        target=P.scale(P.poly([0]*i+list(dt)),-Q(1,2));answer=E.solve(matrix,list(target)+[Q(0)]*(size-len(target)))
                        self.assertEqual(answer[:m-1],tuple(a.evaluate(t) for a in f.connection[i]))
                        self.assertEqual(answer[m-1:],tuple(a.evaluate(t) for a in f.reductions[i]))

    def test_observable_compression_and_zero(self):
        f=CurveFamily(dict(coefficients=[[0,1],[0],[0],[0],[0],[1]]))
        p=f.observable();self.assertEqual(p['order'],1);self.assertEqual(p['polynomial_operator'],[[3],[0,10]])
        self.assertEqual(f.observable([0]*4)['order'],0)
        self.assertEqual(f.observable([0]*4)['polynomial_operator'],[[1]])
        self.assertEqual(f.observable([0,1,0,0])['polynomial_operator'],[[1],[0,10]])

    def test_observable_dependency_and_apparent_zero(self):
        f=CurveFamily(GENUS_TWO);packet=f.observable([[0,1],0,0,0])
        self.assertEqual(packet['order'],4)
        self.assertEqual(packet['scalar_singularities_outside_discriminant'],['0','1'])
        for t in (Q(1,7),Q(2,7)):
            rows=[[RF.parse(a).evaluate(t) for a in row] for row in packet['derivative_rows']]
            self.assertEqual(E.rank(rows),4)
            terminal=[RF.parse(a).evaluate(t) for a in packet['terminal_row']]
            operator=[RF.parse(a).evaluate(t) for a in packet['monic_operator']]
            self.assertEqual(tuple(terminal),tuple(-sum(operator[i]*rows[i][j] for i in range(4)) for j in range(4)))

    def test_complex_pullback_and_whole_segment_exclusion(self):
        p=P.poly([1,2,0,1]);a=(Q(1,3),Q(2,5));b=(Q(-2,3),Q(1,7))
        real,imag=pullback(p,a,b)
        for t in (0,Q(1,4),1):
            z=complex(a[0]+t*(b[0]-a[0]),a[1]+t*(b[1]-a[1]))
            self.assertAlmostEqual(P.evaluate(real,t),P.evaluate(p,z).real,places=12)
            self.assertAlmostEqual(P.evaluate(imag,t),P.evaluate(p,z).imag,places=12)
        f=CurveFamily(GENUS_TWO)
        with self.assertRaises(ValueError):path_certificate(f,[0,1])
        with self.assertRaises(ValueError):path_certificate(f,[0,[0,1]])
        points,packet=path_certificate(f,[0,['1/4','1/4'],[1,'1/4'],1])
        self.assertTrue(packet['exact_no_excluded_zero_on_segments'])
        # Irrational root in the interior; neither endpoint is singular.
        with self.assertRaises(ValueError):path_certificate(f,[[0,0],[1,0]])
        with self.assertRaises(ValueError):path_certificate(f,[0,0],[('extra',[0,1])])

    def test_integer_parameter_population_and_bounded_points(self):
        f=CurveFamily(LEGENDRE);p=ExactPopulation(f.parameter_population(-10,10)['specification'])
        self.assertEqual(p.count(),19)
        self.assertEqual([p.select(i)['parameter'] for i in range(p.count())],[n for n in range(-10,11) if n not in (0,1)])
        self.assertEqual(f.parameter_domain()['cardinality'],None)
        f=CurveFamily(GENUS_TWO);actual=f.integer_points(0,-20,20)['points'];expected=[]
        for x in range(-20,21):
            for y in range(-2000,2001):
                if y*y==x**5-x:expected.append((x,y))
        self.assertEqual(actual,expected)
        self.assertFalse(f.integer_points(0,-20,20)['global_integer_completeness'])

    def test_service_persistence_and_allowlists(self):
        with tempfile.TemporaryDirectory() as directory:
            path=str(Path(directory)/'families.sqlite')
            with Catalogue(path) as c:
                c.register('curve_family',LEGENDRE,'elliptic')
                derived=dispatch(c,dict(op='call',object='elliptic',method='parameter_population',args=dict(lower=-3,upper=3)))
                c.register('population',derived['specification'],'smooth_parameters')
            with Catalogue(path) as c:
                self.assertEqual(c.get('smooth_parameters').count(),5)
                self.assertEqual(dispatch(c,dict(op='call',object='elliptic',method='observable'))['order'],2)
                with self.assertRaises(ValueError):dispatch(c,dict(op='call',object='elliptic',method='_observable'))

    def test_input_contracts_and_algebra_budgets(self):
        for coefficients in ([[0,1],[0],[0],[0],[1]],[[0],[0],[0],[2]],[[0],[0],[0],[1]],[[0]*6,[0],[0],[1]]):
            with self.assertRaises(ValueError):CurveFamily(dict(coefficients=coefficients))
        with self.assertRaises(WorkLimit):CurveFamily(dict(GENUS_TWO,work_limit=100))
        with self.assertRaises(ValueError):CurveFamily(LEGENDRE).specialize(0)
        with self.assertRaises(ValueError):CurveFamily(GENUS_TWO).observable([1])
        with self.assertRaises(ValueError):CurveFamily(GENUS_TWO).integer_points(0,1,0)

    @unittest.skipUnless(NUMERICAL,'optional numpy/scipy backend')
    def test_genus_two_matrix_scalar_and_direct_period(self):
        f=CurveFamily(GENUS_TWO);mark=dict(center=['1/2',0],radius='13/20');path=[0,'1/10','1/5']
        a=f.period_path(path,mark);b=f.period_path(path,mark,mode='scalar');direct=f.marked_period('1/5',mark)
        for left,right in zip(a['trajectory'][-1]['state'],direct['period_vector']):self.assertLess(abs(complex(*left)-complex(*right)),2e-8)
        self.assertLess(abs(complex(*a['trajectory'][-1]['observable'])-complex(*b['trajectory'][-1]['observable'])),2e-8)
        negative=f.marked_period(0,dict(mark,sheet=1))
        for x,y in zip(a['initialization']['period_vector'],negative['period_vector']):self.assertLess(abs(complex(*x)+complex(*y)),2e-9)

    @unittest.skipUnless(NUMERICAL,'optional numpy/scipy backend')
    def test_legendre_initialization_against_rational_period_interval(self):
        from perfectpower.legendre_period_bounds import normalized_period_interval
        f=CurveFamily(LEGENDRE);mark=dict(center='1/8',radius='1/5')
        result=f.marked_period('1/4',mark);bounds=normalized_period_interval(Q(1,4),64)
        value=abs(complex(*result['period_vector'][0]))/(2*math.pi)
        self.assertLess(abs(value-float(Q(bounds['lower']))),2e-10)

    @unittest.skipUnless(NUMERICAL,'optional numpy/scipy backend')
    def test_transport_composition_inverse_and_nontrivial_loop(self):
        f=CurveFamily(LEGENDRE)
        matrix=lambda path:np.array([[complex(*v) for v in row] for row in f.transport(path)['transfer_matrix']])
        a=matrix(['1/4','1/3']);b=matrix(['1/3','1/2']);c=matrix(['1/4','1/2'])
        self.assertLess(np.max(abs(b@a-c)),3e-9)
        self.assertLess(np.max(abs(matrix(['1/2','1/4'])@c-np.eye(2))),3e-9)
        # Exact rational square loop encloses t=0 and avoids t=1.
        loop=matrix(['1/4',['1/4','1/4'],['-1/4','1/4'],['-1/4','-1/4'],['1/4','-1/4'],'1/4'])
        self.assertLess(abs(np.trace(loop)-2),2e-8);self.assertLess(abs(np.linalg.det(loop)-1),2e-8)
        self.assertGreater(np.max(abs(loop-np.eye(2))),.1)

    @unittest.skipUnless(NUMERICAL,'optional numpy/scipy backend')
    def test_scalar_apparent_pole_matrix_route_and_contour_contracts(self):
        f=CurveFamily(GENUS_TWO);mark=dict(center='1/2',radius='13/20');weights=[[0,1],0,0,0]
        result=f.period_path([0,'1/5'],mark,weights)
        self.assertEqual(result['trajectory'][0]['observable'],[0.,0.])
        with self.assertRaises(ValueError):f.period_path([0,'1/5'],mark,weights,mode='scalar')
        a=f.period_path(['1/10','1/5'],mark,weights);b=f.period_path(['1/10','1/5'],mark,weights,mode='scalar')
        self.assertLess(abs(complex(*a['trajectory'][-1]['observable'])-complex(*b['trajectory'][-1]['observable'])),2e-8)
        with self.assertRaises(ValueError):f.marked_period(0,dict(center=0,radius='1/5',turns=1))
        with self.assertRaises(ValueError):f.marked_period(0,dict(center=0,radius=1))


if __name__=='__main__':unittest.main()
