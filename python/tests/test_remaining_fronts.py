import json,random,unittest
from collections import deque
from fractions import Fraction as Q
from sympy import Matrix, symbols, log, simplify
from perfectpower.semistable_tamagawa import component_group,rational_root_tamagawa
from perfectpower.resonant_frobenius import normal_form,gauge_tail
from perfectpower.http_load import run_load


class TamagawaTests(unittest.TestCase):
    def test_elliptic_split_and_nonsplit_multiplicative(self):
        for d in range(1,6):
            split=rational_root_tamagawa(5,[0,5**d,1])
            twist=rational_root_tamagawa(5,[0,5**d,1],2)
            self.assertEqual(split['geometric_order'],2*d)
            self.assertEqual(split['tamagawa_number'],2*d)
            self.assertEqual(twist['geometric_order'],2*d)
            self.assertEqual(twist['tamagawa_number'],2)

    def test_theta_split_and_twisted(self):
        split=rational_root_tamagawa(3,[0,3,1,4,2,5])
        twist=rational_root_tamagawa(3,[0,3,1,4,2,5],2)
        self.assertEqual(split['invariant_factors'],[2,6])
        self.assertEqual(split['tamagawa_number'],12)
        self.assertEqual(twist['tamagawa_number'],4)

    def test_matrix_tree_and_direct_fixed_cosets(self):
        rng=random.Random(20261008)
        for _ in range(60):
            lengths=[rng.randrange(1,9) for _ in range(3)]
            a=component_group(2,[(0,1,L) for L in lengths],vertex_action=[1,0],edge_action=[(i,-1) for i in range(3)])
            # Subdivide each metric edge into regular unit edges; Kirchhoff is independent of the cycle basis.
            edges=[];nv=2
            for L in lengths:
                path=[0]+list(range(nv,nv+L-1))+[1];nv+=L-1
                edges+=list(zip(path,path[1:]))
            lap=Matrix.zeros(nv,nv)
            for i,j in edges:lap[i,i]+=1;lap[j,j]+=1;lap[i,j]-=1;lap[j,i]-=1
            self.assertEqual(a['geometric_order'],int(lap[:-1,:-1].det()))
            G=Matrix(a['monodromy_pairing']);Gi=G.inv();T=Matrix(a['frobenius_dual_action'])
            gens=[tuple(x%1 for x in Gi[:,i]) for i in range(2)]
            group={(Q(0),Q(0))};queue=deque(group)
            while queue:
                v=queue.popleft()
                for g in gens:
                    w=tuple((x+y)%1 for x,y in zip(v,g))
                    if w not in group:group.add(w);queue.append(w)
            self.assertEqual(len(group),a['geometric_order'])
            action=Gi*T*G
            fixed=sum(tuple(x%1 for x in action*Matrix(v))==v for v in group)
            self.assertEqual(a['tamagawa_number'],fixed)

    def test_scope_and_bad_actions_rejected(self):
        self.assertIsNone(component_group(1,[(0,0,7)])['tamagawa_number'])
        with self.assertRaises(ValueError):component_group(2,[(0,1,1)],vertex_action=[1,0],edge_action=[(0,1)])
        with self.assertRaises(ValueError):rational_root_tamagawa(2,[0,1,2])
        with self.assertRaises(ValueError):rational_root_tamagawa(5,[0,5,25,1,2])
        with self.assertRaises(ValueError):component_group(1,[(0,0,Q(1,2))])


class ResonantTests(unittest.TestCase):
    def test_resonance_chain_has_log_squared_and_solves_ode(self):
        R=Matrix.diag(0,1,2);E=Matrix([[0,0,0],[1,0,0],[0,1,0]])
        a=normal_form(R.tolist(),E.tolist(),0,order=36)
        self.assertEqual(a['logarithm_degree'],2)
        self.assertEqual(Matrix(a['logarithmic_exponent']),E)
        x=symbols('x',positive=True)
        Y=Matrix([[1,0,0],[x*log(x),x,0],[x*x*log(x)**2/2,x*x*log(x),x*x]])
        self.assertEqual((x*Y.diff(x)-(R+x*E)*Y).applyfunc(simplify),Matrix.zeros(3))
        self.assertTrue(gauge_tail(a,Q(1,4))['bound_certified'])

    def test_rank_four_jordan_block_and_positive_resonances(self):
        J=Matrix([[0,1,0,0],[0,0,1,0],[0,0,0,1],[0,0,0,0]])
        zero=Matrix.zeros(4)
        a=normal_form(J.tolist(),zero.tolist(),order=24)
        self.assertEqual(a['logarithm_degree'],3)
        b=normal_form(Matrix.diag(0,1,2,3).tolist(),J.T.tolist(),0,order=64)
        self.assertEqual(b['logarithm_degree'],3)
        self.assertTrue(gauge_tail(b,Q(1,8))['bound_certified'])

    def test_exact_majorant_encloses_known_analytic_tail(self):
        a=normal_form([[Q(1,3)]],[[3]],1,order=32)
        H=[Q(row[0][0]) for row in a['gauge_coefficients']]
        x=Q(1,8);exact=1/(1-x)**3;partial=sum(v*x**n for n,v in enumerate(H))
        bound=Q(gauge_tail(a,x)['tail_max_entry'])
        self.assertLess(abs(exact-partial),bound)
        for n,v in enumerate(H):self.assertEqual(v,Q((n+1)*(n+2),2))

    def test_invalid_jordan_frame_and_order_rejected(self):
        with self.assertRaises(ValueError):normal_form([[0,1],[1,0]],[[0,0],[0,0]])
        with self.assertRaises(ValueError):normal_form([[0,0],[0,9]],[[0,0],[1,0]],order=8)
        with self.assertRaises(ValueError):gauge_tail(normal_form([[0]],[[1]],order=12),1)


class ConcurrencyTests(unittest.TestCase):
    def test_concurrent_http_matches_exact_serial_reference(self):
        a=run_load(clients=4,requests=48)
        self.assertTrue(a['all_replayed'],a)
        self.assertEqual(a['replay_mismatches'],[])
        self.assertEqual(a['transport_failures'],[])


if __name__=='__main__':unittest.main()
