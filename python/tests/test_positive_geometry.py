import itertools
import json
import random
import subprocess
import sys
import unittest
from fractions import Fraction as Q
from perfectpower.connection_polytope import ConnectionGraph, root_channel_graph, algebra_determinant
from perfectpower.degeneration_atlas import (normalized_cover, partitions, collision_atlas,
    associahedron, legendre, interval_form, descartes_variations, triangle_canonical,
    ordered_branch_form, pentagon_collision_chart)
from perfectpower.period_boundary import normalize_periods, residue_contract
from perfectpower.descartes_orbits import reflect, parabolic_family, orbit_packet
from perfectpower.exact_linear import rank


class ConnectionTests(unittest.TestCase):
    def test_theta_determinant_marginals_and_boundaries(self):
        g = ConnectionGraph(2, ((0,1,0),(0,1,2),(0,1,1)), 4)
        p = g.packet()
        self.assertEqual([t['coefficient'] for t in p['terms']], [['4'],['2'],['2']])
        self.assertEqual(p['determinant'], ['8'])
        self.assertEqual(p['edge_marginals'], [['3/4'],['3/4'],['1/2']])
        for weights in itertools.product((0,1), repeat=3):
            p = g.packet(weights)
            self.assertEqual(p['determinant'] != ['0'], sum(weights) >= 2)

    def test_random_graph_gram_vs_forests_and_rational_block_rank(self):
        rng = random.Random(41371)
        for d in (2,3,4,5,6):
            for _ in range(8):
                n = rng.randrange(1,5)
                edges = tuple((rng.randrange(n),rng.randrange(n),rng.randrange(d)) for _ in range(n+2))
                g = ConnectionGraph(n,edges,d)
                weights = [Q(rng.randrange(4), rng.randrange(1,4)) for e in edges]
                p = g.packet(weights)
                a = g.laplacian(weights)
                h = g.field.degree
                block = [[Q(0) for j in range(n*h)] for i in range(n*h)]
                for i in range(n):
                    for j in range(n):
                        b = a[i][j].matrix()
                        for k in range(h):
                            for l in range(h):
                                block[i*h+k][j*h+l] = b[k][l]
                self.assertEqual(rank(block), h*p['positive_support']['rank'])

    def test_gauge_and_orientation_invariance(self):
        edges = ((0,1,1),(1,2,2),(0,2,1),(2,2,3))
        d, potential = 5, (2,4,1)
        a = ConnectionGraph(3,edges,d)
        b = ConnectionGraph(3,tuple((u,v,(r+potential[v]-potential[u])%d) for u,v,r in edges),d)
        c = ConnectionGraph(3,tuple((v,u,-r) for u,v,r in edges),d)
        self.assertEqual(a.packet()['terms'],b.packet()['terms'])
        self.assertEqual(a.packet()['terms'],c.packet()['terms'])

    def test_character_decomposition_counts_sheet_components(self):
        for d in range(2,9):
            for labels in ([1,1,1],[2,4],[d,d],[]):
                g = root_channel_graph(labels,d)
                self.assertEqual(sum(g.support(character=k)['kernel_dimension'] for k in range(d)),
                                 g.support()['lift_components'])
                self.assertEqual(g.support()['lift_components'],normalized_cover(labels,d)['components'])

    def test_minimum_cost_greedy_against_all_bases(self):
        rng = random.Random(85)
        for _ in range(30):
            g = ConnectionGraph(3,tuple((rng.randrange(3),rng.randrange(3),rng.randrange(4)) for i in range(6)),4)
            costs = [rng.randrange(20) for e in g.edges]
            r = g.minimum_cost_basis(costs)
            terms = g.terms()
            if terms:
                self.assertEqual(Q(r['cost']), min(sum(costs[i] for i in xs) for xs,c in terms))
                self.assertEqual(r['rank'],3)
            else:
                self.assertEqual(r['status'],'RANK_DEFICIENT')

    def test_budget_and_bad_inputs(self):
        with self.assertRaises(ValueError):ConnectionGraph(2,((0,2,0),),2)
        with self.assertRaises(ValueError):ConnectionGraph(1,((0,0,True),),2)
        with self.assertRaises(ValueError):root_channel_graph([1]*20,4).terms(10)
        with self.assertRaises(ValueError):root_channel_graph([1],2).packet([-1,1])
        with self.assertRaises(ValueError):root_channel_graph([1],2).packet([1.0,1])
        with self.assertRaises(ValueError):root_channel_graph([1],2).support([0,0])


class DegenerationTests(unittest.TestCase):
    def test_bell_partition_census_and_unique_labels(self):
        for n,bell in enumerate((1,1,2,5,15,52,203,877,4140)):
            ps=list(partitions(n))
            self.assertEqual(len(ps),bell)
            self.assertEqual(len(set(ps)),bell)
            for p in ps:
                self.assertEqual(sorted(i for b in p for i in b),list(range(n)))

    def test_collision_profiles_repeated_and_split(self):
        self.assertEqual(normalized_cover([1]*5,2)['genus_per_component'],2)
        self.assertEqual(normalized_cover([2]*3,2)['components'],2)
        self.assertEqual(normalized_cover([6],4)['components'],2)
        self.assertEqual(normalized_cover([],3)['betti'],[3,0,3])
        a=collision_atlas([1]*5,2)
        self.assertEqual(a['stratum_count'],52)
        for r in a['strata']:
            p=r['normalization']
            self.assertEqual(p['euler_total'],2*p['components']-2*p['genus_sum'])
            self.assertEqual(p['curvature_over_pi'],2*p['euler_total'])

    def test_associahedron_face_vectors_and_incidence(self):
        for n,vector in ((4,[2,1]),(5,[5,5,1]),(6,[14,21,9,1]),(7,[42,84,56,14,1])):
            a=associahedron(n)
            self.assertEqual(a['f_vector'],vector)
            for f in a['faces']:
                if f['dimension']==0:self.assertFalse(f['boundary_faces'])
        self.assertEqual(associahedron(8)['triangulations'],132)

    def test_legendre_maps_discriminant_and_series(self):
        p=legendre('2/7',100)
        self.assertEqual(p['normalization']['genus_per_component'],1)
        self.assertEqual(p['normalized_period_series'][:4],['1','1/4','9/64','25/256'])
        for endpoint in (0,1):
            p=legendre(endpoint)
            self.assertEqual(p['normalization']['euler_total'],2)
            self.assertEqual(p['singular_limit']['singular_euler'],1)
            for v in map(Q,range(-3,4)):
                x=v*v+1 if endpoint==0 else v*v
                y=x*v if endpoint==0 else (x-1)*v
                self.assertEqual(y*y,x*(x-1)*(x-endpoint))
        with self.assertRaises(ValueError):legendre(0.2)

    def test_interval_seam_cancellation_and_triangle_pullback(self):
        for x in (Q(-1),Q(1,3),Q(3,4),Q(2)):
            self.assertEqual(interval_form(0,1,x),interval_form(0,Q(1,2),x)+interval_form(Q(1,2),1,x))
        for a,b,c in ((1,1,1),(2,3,1),(Q(2,7),Q(5,3),Q(7,2))):
            self.assertEqual(Q(triangle_canonical(a,b,c)['canonical_form_pullback']),1/(Q(a)*Q(b)))

    def test_descartes_open_interval_and_multiple_roots(self):
        self.assertEqual(descartes_variations([-1,1],0,2)['exact_root_count'],1)
        self.assertEqual(descartes_variations([1,0,1],0,2)['exact_root_count'],0)
        self.assertEqual(descartes_variations([0,-1,1],0,1)['exact_root_count'],0)
        self.assertEqual(descartes_variations([1,-2,1],0,2)['variations'],2)
        with self.assertRaises(ValueError):descartes_variations([0],0,1)

    def test_ordered_chamber_forms_and_exceptional_boundary(self):
        self.assertEqual(ordered_branch_form(['1/3','2/3'])['coefficient'],'27')
        for u in ('1/3','2/5','6/7'):
            for t in ('1/8','3/7','9/10'):
                p=pentagon_collision_chart(u,t)
                self.assertEqual(Q(p['boundary_residue_coefficient']),interval_form(0,1,Q(u)))
        with self.assertRaises(ValueError):ordered_branch_form(['2/3','1/3'])


class ArithmeticAndPeriodTests(unittest.TestCase):
    def test_descartes_involution_and_all_fixed_pairs(self):
        seed=(-1,2,2,3)
        seeds=[seed]+[reflect(seed,i) for i in range(4)]
        for seed in seeds:
            for i in range(4):self.assertEqual(reflect(reflect(seed,i),i),seed)
            for fixed in itertools.combinations(range(4),2):
                p=orbit_packet(seed,fixed,100,(2,3))
                u,v,s=p['polynomial']
                self.assertEqual(p['prefix'],[u+v*n+s*n*n for n in range(32)])
        p=orbit_packet(stop=10000)
        self.assertEqual(p['hits']['3'],[{'index':5,'curvature':27,'root':3}])
        self.assertEqual(p['hits']['2'],[])
        with self.assertRaises(ValueError):reflect((1,2,3,4),0)

    def test_period_corrections_unique_and_residue_conditions(self):
        self.assertEqual(normalize_periods([[1,0],[0,1]],[3,-2])['correction'],['-3','2'])
        p=normalize_periods([[2,1],[1,1]],[3,-2],[1,4])
        self.assertEqual(p['corrected_periods'],['1','4'])
        self.assertEqual(normalize_periods([],[])['correction'],[])
        with self.assertRaises(ValueError):normalize_periods([[1,1],[2,2]],[1,0])
        self.assertEqual(residue_contract([1,-1],2)['holomorphic_ambiguity_dimension'],2)
        self.assertFalse(residue_contract([1,1],2)['existence_condition_met'])

    def test_console_routes(self):
        commands=[['associahedron','--marks','5'],['legendre','--parameter','1/2'],
                  ['branch-form','--coordinates','["1/3","2/3"]'],
                  ['branch-form','--collision-chart','["2/5","3/7"]'],
                  ['connection-polytope','--vertices','2','--edges','[[0,1,0],[0,1,1]]','--d','2'],
                  ['connection-polytope','--vertices','2','--edges','[[0,1,0],[0,1,1]]','--d','2','--costs','[3,1]'],
                  ['descartes-orbit','--stop','10'],['period-normalize','--matrix','[[1]]','--periods','[2]'],
                  ['branch-signs','--coeff=-1,1','--left','0','--right','2'],
                  ['collision-atlas','--multiplicities','[1,1,1]','--d','2']]
        for cmd in commands:
            output=subprocess.check_output([sys.executable,'-m','perfectpower']+cmd,text=True)
            self.assertIsInstance(json.loads(output),dict)


if __name__=='__main__':unittest.main()
