import unittest,math,random
from fractions import Fraction as Q
from copy import deepcopy
from perfectpower import michor_geometry as M,bernstein_boxes as B
from perfectpower.divisor_square import WorkLimit

ONE=[[0,0,1]]
SPHERE_D=B.power({(0,0):Q(1),(2,0):Q(1),(0,2):Q(1)},4)
COEFF=[0,-1,0,0,0,1]

def sphere():return M.compile_metric([[0,0,4]],SPHERE_D)
def invmap():return [{'numerator':[[1,0,1]],'denominator':[[2,0,1],[0,2,1]]},
                     {'numerator':[[0,1,1]],'denominator':[[2,0,1],[0,2,1]]}]

class DifferentialGeometry(unittest.TestCase):
    def test_flat_sphere_hyperbolic_and_curve_curvature(self):
        flat=M.compile_metric(ONE,ONE);hyper=M.compile_metric(ONE,[[0,4,1]])
        for p in [[1,1],['2/3','7/5'],[-2,3]]:
            self.assertEqual(M.evaluate_metric(flat,p)['curvature_interval'],['0','0'])
            self.assertEqual(M.evaluate_metric(sphere(),p)['curvature_interval'],['1','1'])
            self.assertEqual(M.evaluate_metric(hyper,p)['curvature_interval'],['-1','-1'])
        self.assertEqual(M.evaluate_metric(M.hyperelliptic_metric(COEFF),[2,0])['curvature_interval'],['-12/25','-12/25'])

    def test_branch_and_infinity_metric_stays_regular(self):
        for chart in ['branch','infinity']:
            p=M.hyperelliptic_metric(COEFF,chart,branch=0 if chart=='branch' else None)
            v=M.evaluate_metric(p,[0,0]);self.assertEqual(v['density_interval'],['4','4']);self.assertEqual(v['curvature_interval'],['0','0'])
        with self.assertRaises(ValueError):M.evaluate_metric(M.hyperelliptic_metric(COEFF),[0,0])
        with self.assertRaises(ValueError):M.hyperelliptic_metric([0,0,0,1])

    def test_exact_energy_and_transport_rates(self):
        p=M.hyperelliptic_metric(COEFF);rng=random.Random(711)
        for _ in range(30):
            q=[Q(rng.randrange(15,30),10),Q(rng.randrange(1,10),10)]
            v=[Q(rng.randrange(-5,6),7),Q(rng.randrange(-5,6),11)];z=[Q(2,3),Q(-4,5)]
            *_,g,h=M._point_data(p,q);a=M.acceleration(p,q,v);zd=[-a for a in M.connection_action(p,q,v,z)]
            gv=sum(a*b for a,b in zip(g,v))
            self.assertEqual(gv*sum(a*a for a in v)+2*sum(a*b for a,b in zip(v,a)),0)
            self.assertEqual(gv*sum(a*a for a in z)+2*sum(a*b for a,b in zip(z,zd)),0)

    def test_connection_metric_compatibility_and_symmetry(self):
        p=sphere();q=['2/3','1/7'];*_,g,h=M._point_data(p,q)
        C=[[[M._eval(c,*map(Q,q)) for c in row] for row in plane] for plane in p['connection']]
        for k in range(2):
            for i in range(2):
                for j in range(2):self.assertEqual(C[k][i][j],C[k][j][i])
        for k in range(2):
            for i in range(2):
                for j in range(2):self.assertEqual(g[k] if i==j else 0,C[j][k][i]+C[i][k][j])

    def test_jacobian_with_independent_central_difference(self):
        p=M.hyperelliptic_metric(COEFF);q=[Q(2),Q(1,3)];v=[Q(2,7),Q(-3,5)];J=M.geodesic_jacobian(p,q,v);eps=Q(1,10**7)
        for i in range(4):
            plus=q+v;minus=q+v;plus[i]+=eps;minus[i]-=eps
            a=M.acceleration(p,plus[:2],plus[2:]);b=M.acceleration(p,minus[:2],minus[2:])
            for k in range(2):self.assertAlmostEqual(float((a[k]-b[k])/(2*eps)),float(J[k+2][i]),places=10)

    def test_hamiltonian_legendre_relation(self):
        p=sphere();out=M.dynamics(p,[1,0],[0,1],momentum=[0,1],transport=[1,0],variation=[0,0,1,0])
        self.assertEqual(out['hamiltonian_interval'],['1/2','1/2']);self.assertEqual(out['hamiltonian_position_rates'],[['0','0'],['1','1']])
        self.assertEqual(out['hamiltonian_momentum_rates'],[['-1','-1'],['0','0']]);self.assertEqual(out['geodesic_acceleration'],['-1','0'])
        self.assertEqual(out['parallel_transport_rate'],['0','1'])

    def test_sphere_equator_and_parallel_transport_analytic_oracle(self):
        trace=M.trace_geodesic(sphere(),[1,0,0,1],2,100,transport=[1,0]);self.assertFalse(trace['certified_trajectory'])
        for row in trace['samples']:
            t=row['time'];expected=[math.cos(t),math.sin(t)]
            for a,b in zip(row['position'],expected):self.assertAlmostEqual(a,b,places=7)
            for a,b in zip(row['transport'],expected):self.assertAlmostEqual(a,b,places=7)
        self.assertLess(trace['maximum_energy_drift'],1e-8);self.assertLess(trace['maximum_transport_norm_drift'],1e-8)

    def test_hyperbolic_vertical_and_semicircle_oracles(self):
        p=M.compile_metric(ONE,[[0,4,1]])
        for initial,expected in [([0,1,0,1],lambda t:(0,math.exp(t))),([0,1,1,0],lambda t:(math.tanh(t),1/math.cosh(t)))]:
            trace=M.trace_geodesic(p,initial,1,80)
            for row in trace['samples']:
                for a,b in zip(row['position'],expected(row['time'])):self.assertAlmostEqual(a,b,places=7)

    def test_coordinate_variation_against_neighboring_geodesics(self):
        p=sphere();eps=Q(1,10**5);base=M.trace_geodesic(p,[1,0,0,1],1,80,variation=[0,0,1,0])
        plus=M.trace_geodesic(p,[1,0,eps,1],1,80);minus=M.trace_geodesic(p,[1,0,-eps,1],1,80)
        for k in range(4):
            a=plus['samples'][-1]['position']+plus['samples'][-1]['velocity'];b=minus['samples'][-1]['position']+minus['samples'][-1]['velocity']
            self.assertAlmostEqual((a[k]-b[k])/(2*float(eps)),base['samples'][-1]['variation'][k],places=7)

    def test_sphere_embedding_and_two_chart_overlap(self):
        rng=random.Random(17)
        for _ in range(25):
            p=[Q(rng.randrange(-10,11),7),Q(rng.randrange(-10,11),5)];xyz=list(map(Q,M.sphere_embedding(p)))
            self.assertEqual(sum(v*v for v in xyz),1)
            self.assertEqual([xyz[0]/(1-xyz[2]),xyz[1]/(1-xyz[2])],p)
            if any(p):
                r2=sum(v*v for v in p);other=[v/r2 for v in p]
                self.assertEqual(M.sphere_embedding(p),M.sphere_embedding(other,north_chart=True))

    def test_exact_rational_square_root_brackets(self):
        for value in [Q(0),Q(2),Q(1,7),Q(10**50+1,13)]:
            lo,hi=M.sqrt_interval(value,80);self.assertLessEqual(lo*lo,value);self.assertGreaterEqual(hi*hi,value)
        with self.assertRaises(ValueError):M.sqrt_interval(1.0)

    def test_tampered_metric_float_and_size_rejected(self):
        p=sphere();bad=deepcopy(p);bad['log_gradient'][0]['numerator']=ONE
        with self.assertRaises(ValueError):M.check_metric(bad)
        with self.assertRaises(ValueError):M.compile_metric([[0,0,1.0]],ONE)
        with self.assertRaises(WorkLimit):M.compile_metric([[64,1,1]],ONE)
        with self.assertRaises(ValueError):M.compile_metric([],ONE)
        with self.assertRaises(ValueError):M.evaluate_metric(M.compile_metric(ONE,[[0,4,1]]),[0,0])

class SmoothBridges(unittest.TestCase):
    def test_curve_rectangle_and_point_bounds(self):
        p=M.hyperelliptic_metric(COEFF);b=M.certify_domain(p,[2,'9/4',0,'1/4'],'1/4',1,depth=2)
        self.assertTrue(M.check_domain(p,b));self.assertFalse(b['unrestricted_curve_comparison'])
        out=M.bridge_distances(p,b,[2,0],['9/4','1/4']);self.assertEqual(out['squared_distance_interval'],['1/128','1/8'])
        for x in [Q(2),Q(17,8),Q(9,4)]:
            for y in [Q(0),Q(1,8),Q(1,4)]:
                rho=M.evaluate_metric(p,[x,y])['density_interval'];self.assertGreater(Q(rho[0]),Q(1,16));self.assertLess(Q(rho[1]),1)
        with self.assertRaises(ValueError):M.bridge_distances(p,b,[1,0],[2,0])

    def test_branch_and_infinity_continuous_boxes(self):
        for chart in ['branch','infinity']:
            p=M.hyperelliptic_metric(COEFF,chart,branch=0 if chart=='branch' else None)
            b=M.certify_domain(p,['-1/4','1/4','-1/4','1/4'],1,3,depth=2)
            self.assertTrue(M.check_domain(p,b));self.assertGreater(Q(M.evaluate_metric(p,[0,0])['density_interval'][0]),1)

    def test_global_plane_bounds_winner_and_distance(self):
        p,b=M.bounded_plane_bridge();self.assertTrue(b['global_distance_comparison'])
        for q in [[0,0],[1,2],[10**9,-10**9]]:
            lo,hi=map(Q,M.evaluate_metric(p,q)['density_interval']);self.assertGreaterEqual(lo,1);self.assertLessEqual(hi,2)
        self.assertEqual(M.bridge_distances(p,b,[0,0],[3,4])['distance_interval'],['5','15/2'])
        win=M.bridge_winner(p,b,[0,0],{'near':[0,0],'far':[3,4]},'near',1)
        self.assertTrue(win['strict_winner']);self.assertEqual(win['margins'],{'far':'2'})
        self.assertFalse(M.bridge_winner(p,b,[0,0],{'near':[0,0],'far':[3,4]},'near',2)['strict_winner'])

    def test_tampered_bounds_and_unresolved_comparison(self):
        p,b=M.bounded_plane_bridge();bad=deepcopy(b);bad['lower_scale']='2'
        with self.assertRaises(ValueError):M.check_domain(p,bad)
        p=M.hyperelliptic_metric(COEFF);b=M.certify_domain(p,[2,'9/4',0,'1/4'],'1/4',1,depth=2)
        bad=deepcopy(b);bad['box'][0]='1'
        with self.assertRaises(ValueError):M.check_domain(p,bad)
        with self.assertRaises(WorkLimit):M.certify_domain(p,[2,'9/4',0,'1/4'],1,2,depth=0)

class ChartsAndFlow(unittest.TestCase):
    def test_inversion_curvature_and_geodesic_chain_rule(self):
        p=sphere();t=M.pullback_metric(p,invmap());self.assertTrue(M.check_transport(p,t))
        self.assertEqual(t['geodesic_transport_residual'],['0','0'])
        self.assertEqual(M.evaluate_metric(t['metric'],[2,1])['curvature_interval'],['1','1'])
        out=M.transport_point(p,t,[2,1],[1,2]);self.assertEqual(out['point'],['2/5','1/5']);self.assertEqual(out['jacobian_determinant'],'-1/25')
        # The simplified pulled-back sphere metric extends to zero, but the
        # original chart inversion still does not. The retained domain rejects it.
        self.assertEqual(M.evaluate_metric(t['metric'],[0,0])['curvature_interval'],['1','1'])
        with self.assertRaises(ValueError):M.transport_point(p,t,[0,0],[1,0])

    def test_branch_overlap_and_critical_point_retained(self):
        p=M.hyperelliptic_metric(COEFF)
        mapping=[{'numerator':[[2,0,1],[0,2,-1]],'denominator':ONE},{'numerator':[[1,1,2]],'denominator':ONE}]
        t=M.pullback_metric(p,mapping);branch=M.hyperelliptic_metric(COEFF,'branch',branch=0)
        for q in [['1/3','1/5'],['1/4',0]]:
            self.assertEqual(M._eval(t['metric']['density_squared'],*map(Q,q)),M._eval(branch['density_squared'],*map(Q,q)))
        with self.assertRaises(ValueError):M.transport_point(p,t,[0,0],[1,0])
        self.assertEqual(M.evaluate_metric(branch,[0,0])['density_interval'],['4','4'])

    def test_nonconformal_scaling_and_constant_map_rejected(self):
        p=sphere()
        for mapping in [[{'numerator':[[1,0,2]],'denominator':ONE},{'numerator':[[0,1,1]],'denominator':ONE}],
                        [{'numerator':ONE,'denominator':ONE},{'numerator':ONE,'denominator':ONE}]]:
            with self.assertRaises(ValueError):M.pullback_metric(p,mapping)

    def test_point_transport_rejects_tampered_jacobian(self):
        p=sphere();transport=M.pullback_metric(p,invmap())
        transport['jacobian'][0][0]={'numerator':[[0,0,99]],'denominator':ONE}
        with self.assertRaises(ValueError):M.transport_point(p,transport,[1,0],[1,0])

    def test_flat_tube_exact_endpoint(self):
        p=M.compile_metric(ONE,ONE)
        tube=M.certify_flow_tube(p,[[0,0],[0,0],[1,1],[2,2]],[[-1,1],[-1,1],[1,1],[2,2]],'1/10')
        self.assertEqual(tube['endpoint_box'],[['1/10','1/10'],['1/5','1/5'],['1','1'],['2','2']]);self.assertTrue(M.check_flow_tube(p,tube))
        bad=deepcopy(tube);bad['endpoint_box'][0]=['0','0']
        with self.assertRaises(ValueError):M.check_flow_tube(p,bad)

    def test_sphere_tube_contains_analytic_solution(self):
        p=sphere();initial=[[1,1],[0,0],[0,0],[1,1]];tube=[['9/10','11/10'],['-1/10','1/10'],['-1/5','1/5'],['9/10','11/10']]
        cert=M.certify_flow_tube(p,initial,tube,'1/100')
        expected=[math.cos(.01),math.sin(.01),-math.sin(.01),math.cos(.01)]
        for (lo,hi),value in zip(cert['endpoint_box'],expected):self.assertLessEqual(float(Q(lo)),value);self.assertGreaterEqual(float(Q(hi)),value)
        self.assertLess(Q(cert['contraction_factor']),1)

    def test_picard_failures_are_explicit(self):
        p=M.compile_metric(ONE,ONE)
        for time,tube in [('1',[[0,1],[0,1],[1,1],[2,2]]),('1/10',[[0,'1/100'],[0,'1/100'],[1,1],[2,2]])]:
            with self.assertRaises(ValueError):M.certify_flow_tube(p,[[0,0],[0,0],[1,1],[2,2]],tube,time)
        with self.assertRaises(ValueError):M.certify_flow_tube(M.compile_metric(ONE,[[0,4,1]]),[[0,0],[0,0],[1,1],[1,1]],[[-1,1],[-1,1],[1,1],[1,1]],'1/10')

    def test_cli_packet_dispatch(self):
        from perfectpower.michor_cli import dispatch
        self.assertEqual(dispatch('plane',{'start':[0,0],'end':[3,4]})['distance']['distance_interval'],['5','15/2'])
        out=dispatch('dynamics',{'numerator':[[0,0,4]],'denominator_squared':B.encode(SPHERE_D),'point':[1,0],'velocity':[0,1]})
        self.assertEqual(out['geodesic_acceleration'],['-1','0'])

if __name__=='__main__':unittest.main()
