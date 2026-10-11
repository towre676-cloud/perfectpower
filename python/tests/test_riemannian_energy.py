from fractions import Fraction as Q
import copy
import random
import unittest
from perfectpower.riemannian_energy import metric,quadratic,pullback,connection_jet,compile_energy_certificate
from perfectpower.divisor_square import WorkLimit

BASE={'metric':[2,1,3],'vertices':[[0,0],[1,2],[3,-1]],'durations':[1,2]}

class RiemannianEnergy(unittest.TestCase):
    def test_exact_energy_and_detour(self):
        r,s=compile_energy_certificate(BASE)
        self.assertEqual(Q(r['energy']),Q(59,4))
        self.assertEqual(Q(r['energy']),Q(r['straight_energy'])+Q(r['excess']))
        self.assertGreater(Q(r['excess']),0)
        self.assertIn('all_timed_paths',s)
        self.assertIn('vertices.zip vertices.tail',s)
        self.assertFalse(r['proof']['kernel_checked'])

    def test_stationary_and_constant_velocity(self):
        for vertices,times in [([[2,3],[2,3],[2,3]],[1,3]),
                               ([[0,0],[1,2],[3,6]],[1,2])]:
            r,_=compile_energy_certificate({**BASE,'vertices':vertices,'durations':times})
            self.assertEqual(r['excess'],'0');self.assertTrue(r['constant_velocity'])

    def test_rational_and_nearly_singular(self):
        r,_=compile_energy_certificate({'metric':[1,1,'1000001/1000000'],
                                       'vertices':[[0,0],['1/3','-2/5']],'durations':['7/11']})
        self.assertGreater(Q(r['energy']),0)
        self.assertEqual(r['excess'],'0')

    def test_invalid_metrics(self):
        for g in ([1,1,1],[-1,0,-1],[1,2,1],[0,0,1],[1,0],[1,0,1.0],[True,0,1]):
            with self.assertRaises(ValueError):compile_energy_certificate({**BASE,'metric':g})

    def test_invalid_path(self):
        for vertices,times in [([[0,0]],[]),([[0,0],[1,1]],[]),
                               ([[0,0],[1,1]],[0]),([[0,0],[1,1]],[-1]),
                               ([[0,0],[1,1]],[1.0])]:
            with self.assertRaises(ValueError):compile_energy_certificate({**BASE,'vertices':vertices,'durations':times})
        with self.assertRaises(WorkLimit):compile_energy_certificate(BASE,step_limit=1)
        with self.assertRaises(ValueError):compile_energy_certificate(BASE,namespace='Bad; sorry')

    def test_affine_transport_reflection_and_shear(self):
        for m in ((0,-1,1,0),(1,2,0,1),(-1,0,0,1),(2,0,0,'1/2')):
            m=tuple(map(Q,m));target=metric([3,1,2]);g=pullback(target,m)
            r,s=compile_energy_certificate({**BASE,'metric':g,'transport':{
                'metric':target,'linear':m,'translation':['3/7',11]}})
            self.assertIn('source_transport',s)
            p,q,a,b=m
            transformed=[[p*Q(x)+q*Q(y)+Q(3,7),a*Q(x)+b*Q(y)+11] for x,y in BASE['vertices']]
            rr,_=compile_energy_certificate({**BASE,'metric':target,'vertices':transformed})
            self.assertEqual(r['energy'],rr['energy'])

    def test_false_and_singular_transport(self):
        for m in ([1,0,0,1],[1,2,2,4]):
            with self.assertRaises(ValueError):compile_energy_certificate({**BASE,'transport':{'metric':[1,0,1],'linear':m}})

    def test_connection_jet_compatibility_and_torsion(self):
        rng=random.Random(20261011)
        for _ in range(80):
            g=metric([2,1,3]);rows=[[Q(rng.randint(-8,8),rng.randint(1,5)) for _ in range(3)] for _ in range(2)]
            d,l,gamma=connection_jet(g,rows);a,b,c=g;gram=((a,b),(b,c))
            for i in range(2):
                for j in range(2):
                    for k in range(2):
                        self.assertEqual(gamma[i][j][k],gamma[j][i][k])
                        self.assertEqual(sum(gram[k][n]*gamma[i][j][n] for n in range(2)),l[i][j][k])
                        self.assertEqual(l[i][j][k]+l[i][k][j],d[i][j][k])
        self.assertEqual(connection_jet(g,[[0,0,0],[0,0,0]])[2],[[[0,0],[0,0]],[[0,0],[0,0]]])
        with self.assertRaises(ValueError):connection_jet(g,[[1,2],[3,4]])

    def test_random_variance_and_rigidity(self):
        rng=random.Random(438)
        for _ in range(100):
            # Rational LDL factor generates positive forms, including a large cross term.
            a=Q(rng.randint(1,8),rng.randint(1,7));b=Q(rng.randint(-20,20),rng.randint(1,5));c=b*b/a+Q(1,rng.randint(1,9))
            vertices=[[Q(rng.randint(-10,10),rng.randint(1,7)) for _ in range(2)] for _ in range(5)]
            times=[Q(rng.randint(1,8),rng.randint(1,7)) for _ in range(4)]
            r,_=compile_energy_certificate({'metric':[a,b,c],'vertices':vertices,'durations':times})
            self.assertGreaterEqual(Q(r['excess']),0)
            velocity=tuple(map(Q,r['velocity']))
            rigid=all(tuple((y-x)/t for x,y in zip(v,w))==velocity for v,w,t in zip(vertices,vertices[1:],times))
            self.assertEqual(r['constant_velocity'],rigid)

    def test_cli_packet(self):
        from perfectpower.belyaev_cli import dispatch
        r=dispatch('metric-energy-proof',BASE)
        self.assertEqual(r['certificate']['energy'],'59/4')
        self.assertIn('all_timed_paths',r['lean_source'])

    def test_source_hashes_change(self):
        a,_=compile_energy_certificate(BASE);changed=copy.deepcopy(BASE);changed['vertices'][1][0]=2
        b,_=compile_energy_certificate(changed)
        self.assertNotEqual(a['proof']['source_sha256'],b['proof']['source_sha256'])
        self.assertNotEqual(a['proof']['packet_sha256'],b['proof']['packet_sha256'])

if __name__=='__main__':unittest.main()
