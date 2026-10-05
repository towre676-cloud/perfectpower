import copy
import unittest
from fractions import Fraction as Q
from perfectpower import bernstein_boxes as B
from perfectpower.metric_boxes import chart_density,compare,verify,MetricBoxSpace
from perfectpower.box_lean import emit_metric,emit_exclusion

class MetricBoxTests(unittest.TestCase):
    def test_tensor_round_trip(self):
        for m in range(5):
            for n in range(5):
                p={(m,n):Q(7,3),(0,0):Q(5)}
                a,b,rows=B.bernstein(p,[-2,3,Q(1,3),2])
                self.assertEqual(B.expand_basis(a,b,rows),B.normalized(p,[-2,3,Q(1,3),2]))

    def test_strict_closed_rectangle_and_zero(self):
        p=B.certify([(2,0,1),(0,2,1),(0,0,1)],[-1,1,-1,1],depth=4)
        self.assertTrue(B.verify(p));self.assertTrue(p['complete'])
        zero=B.certify([],[-1,1,-1,1],depth=0)
        self.assertTrue(B.verify(zero));self.assertFalse(zero['complete'])
        edge=B.certify([(1,0,1)],[0,1,0,1],depth=2)
        self.assertFalse(edge['complete']);self.assertTrue(B.verify(edge))

    def test_adaptive_tampering(self):
        p=B.certify([(2,0,1),(0,2,1),(0,0,1)],[-1,1,-1,1],depth=4)
        for mutate in [lambda q:q['nodes'].pop(),lambda q:q['nodes'][0]['coefficients'][0].__setitem__(0,'999'),
                       lambda q:q.__setitem__('sign',-1),lambda q:q['nodes'][0].__setitem__('address',[0])]:
            q=copy.deepcopy(p);mutate(q);self.assertFalse(B.verify(q))

    def test_joint_polynomial_multiplier(self):
        F=[(0,2,1),(3,0,-1)];G=[(0,1,1),(1,0,-1),(0,0,-1)]
        q,r=B.affine_remainder(F,G)
        self.assertEqual(B.add(B.mul(q,G),r),B.poly(F))
        packet=B.compile_system([F,G],[0,1,-10**100,10**100],depth=2)
        self.assertTrue(packet['excluded']);self.assertEqual(packet['route'],'affine_elimination')
        self.assertTrue(B.verify_exclusion(packet))
        self.assertEqual(packet['residual_boxes'],[])
        packet['weights'][1][0][2]='999';self.assertFalse(B.verify_exclusion(packet))

    def test_retained_common_zero(self):
        p=B.compile_system([[(0,2,1),(2,0,-1)],[(0,1,1),(1,0,-1)]],[-1,1,-1,1],depth=3)
        self.assertFalse(p['excluded']);self.assertTrue(B.verify_exclusion(p))
        for t in [Q(-1),Q(0),Q(1)]:
            self.assertTrue(any(Q(a)<=t<=Q(b) and Q(c)<=t<=Q(d) for a,b,c,d in p['residual_boxes']))

    def test_metric_branch_infinity_symmetry(self):
        for g in range(1,4):
            coeff=[0,-1]+[0]*(2*g-1)+[1]
            branch=chart_density(coeff,'branch',0);infinity=chart_density(coeff,'infinity')
            self.assertEqual(branch['numerator'],infinity['numerator'])
            self.assertEqual(branch['denominator_modulus_squared'],infinity['denominator_modulus_squared'])

    def test_branch_and_infinity_comparisons(self):
        for chart in ['branch','infinity']:
            p=compare([0,-1,0,1],chart,[-Q(1,4),Q(1,4),-Q(1,4),Q(1,4)],Q(99,100),Q(103,100),4,
                      branch=0 if chart=='branch' else None,depth=2)
            self.assertTrue(p['complete']);self.assertTrue(verify(p));self.assertFalse(p['global_distance_comparison'])
            for x,y in [(0,0),(Q(1,4),Q(1,4)),(Q(-1,4),Q(1,8))]:
                N=B.evaluate(p['chart_data']['numerator'],x,y);D=B.evaluate(p['chart_data']['denominator_modulus_squared'],x,y)
                self.assertLess(Q(p['lower_scale'])**4*16*D,N*N)
                self.assertLess(N*N,Q(p['upper_scale'])**4*16*D)

    def test_finite_metric_and_tampering(self):
        p=compare([0,-1,0,1],'finite',[2,3,0,Q(1,4)],Q(1,6),Q(1,2),depth=2)
        self.assertTrue(p['complete']);self.assertTrue(verify(p))
        for key,value in [('lower_scale','2'),('global_distance_comparison',True),('complete',False)]:
            bad=copy.deepcopy(p);bad[key]=value;self.assertFalse(verify(bad))
        bad=copy.deepcopy(p);bad['chart_data']['numerator'][0][2]='99';self.assertFalse(verify(bad))

    def test_chart_failures(self):
        for coeff,chart,branch in [([0,0,0,1],'branch',0),([0,1,-2,1],'branch',0),([0,0,0,1],'finite',None),([0,-1,0,1],'branch',2),([1,0,1],'finite',None)]:
            with self.assertRaises(ValueError):chart_density(coeff,chart,branch)
        with self.assertRaises(ValueError):compare([0,-1,0,1],'finite',[0,1,0,1],0,1)
        with self.assertRaises(B.WorkLimit):B.certify([(1,0,1)],[-1,1,-1,1],depth=4,node_limit=1)

    def test_even_degree_infinity(self):
        p=chart_density([-1,0,0,0,1],'infinity')
        self.assertEqual(p['genus'],1);self.assertEqual(p['numerator'],[[0,0,'1']])
        self.assertEqual(B.evaluate(p['denominator_modulus_squared'],0,0),1)

    def test_literal_lean_emission(self):
        p=compare([0,-1,0,1],'branch',[-Q(1,4),Q(1,4),-Q(1,4),Q(1,4)],Q(99,100),Q(103,100),4,branch=0,depth=2)
        source,names=emit_metric('sample',p)
        self.assertIn('rectangle_positive',source);self.assertIn('density_comparison',source)
        self.assertNotIn('native_decide',source);self.assertEqual(len(names),5)
        e=B.compile_system([[(0,2,1),(3,0,-1)],[(0,1,1),(1,0,-1),(0,0,-1)]],[0,1,-10,10],depth=2)
        source,names=emit_exclusion('sample',e)
        self.assertIn('no_common_zero',source)

    def test_reusable_metric_queries(self):
        p=compare([0,-1,0,1],'branch',[-Q(1,4),Q(1,4),-Q(1,4),Q(1,4)],Q(99,100),Q(103,100),4,branch=0,depth=2)
        space=MetricBoxSpace(p)
        for x,y in [(0,0),(Q(1,4),Q(1,4)),(Q(-1,8),Q(1,8))]:
            data=space.point([x,y]);lo,hi=map(Q,data['density_interval'])
            N=B.evaluate(p['chart_data']['numerator'],x,y);D=B.evaluate(p['chart_data']['denominator_modulus_squared'],x,y)
            self.assertLessEqual(lo*lo,N*N/D);self.assertLessEqual(N*N/D,hi*hi)
        self.assertEqual(space.point([0,0])['density_interval'],['4','4'])
        segment=space.segment([-Q(1,4),0],[Q(1,4),0])
        self.assertEqual(list(map(Q,segment['squared_path_length_interval'])),[Q(99,100)**2,Q(103,100)**2])
        self.assertEqual(space.statistics(),{'certificate_checks':1,'queries':5})
        with self.assertRaises(ValueError):space.point([1,1])

    def test_residual_box_tampering(self):
        packet=B.compile_system([[(0,1,1),(1,0,-1)]],[-1,1,-1,1],depth=2)
        self.assertTrue(B.verify_exclusion(packet))
        packet['residual_boxes']=[];self.assertFalse(B.verify_exclusion(packet))

    def test_zero_strata_and_complete_affine_faces(self):
        p=B.zero_strata([(2,0,1),(3,0,-1)],[0,1,-10,10])
        self.assertTrue(B.verify_zero_strata(p));self.assertTrue(p['complete'])
        self.assertEqual({s['x'] for s in p['zero_strata']},{'lower','upper'})
        eqs=[[(0,2,1),(3,0,-1)],[(0,1,1),(1,0,-1)]]
        complete=B.solve_affine_faces(eqs,[0,1,-10**100,10**100])
        self.assertTrue(complete['complete']);self.assertEqual(complete['models'],[[0,0],[1,1]])
        self.assertTrue(B.verify_affine_faces(complete))
        bad=copy.deepcopy(complete);bad['models'].pop();self.assertFalse(B.verify_affine_faces(bad))
        bad=copy.deepcopy(p);bad['zero_strata'].pop();self.assertFalse(B.verify_zero_strata(bad))
        image=B.solve_affine_faces([[(0,2,4),(3,0,-1)],[(0,1,2),(1,0,-1)]],[0,1,-10,10])
        self.assertTrue(B.verify_affine_faces(image));self.assertEqual(image['models'],[[0,0]])

    def test_zero_strata_against_independent_grid(self):
        p=B.mul([(2,0,1),(3,0,-1)],[(0,2,1),(0,3,-1)])
        strata=B.zero_strata(p,[0,1,0,1]);self.assertTrue(B.verify_zero_strata(strata))
        for x in [Q(0),Q(1,4),Q(1,2),Q(1)]:
            for y in [Q(0),Q(1,4),Q(1,2),Q(1)]:
                state=lambda q:'lower' if q==0 else 'upper' if q==1 else 'interior'
                predicted={'x':state(x),'y':state(y)} in strata['zero_strata']
                self.assertEqual(predicted,B.evaluate(p,x,y)==0)

    def test_native_voronoi_emission(self):
        from perfectpower.voronoi_certificate import produce
        from perfectpower.voronoi_lean import emit
        mesh={'vertices':4,'triangles':[[0,2,1],[0,1,3],[0,3,2],[1,2,3]],'edge_lengths':[[a,b,'1'] for a in range(4) for b in range(a+1,4)]}
        packet=produce(mesh,[0,1],[[0,Q(3,4),0,0]],1)
        source=emit('sample',mesh,packet)
        self.assertIn('by decide +kernel',source);self.assertIn('accepts sample_mesh sample_packet',source)
        self.assertNotIn('native_decide',source);self.assertNotIn('axiom ',source)
        packet['pieces'][0]['radius_upper']='0'
        with self.assertRaises(ValueError):emit('sample',mesh,packet)

if __name__=='__main__':unittest.main()
