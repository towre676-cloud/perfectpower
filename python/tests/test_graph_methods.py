import unittest
import random
from itertools import product, combinations
from copy import deepcopy
from fractions import Fraction
from perfectpower.graph_structure import elimination_forest, check_decomposition, machine_structure
from perfectpower.graph_counting import count_cnf, count_factors, cnf_model, check_count, condition, unrank, rank_assignment, predicate_factor
from perfectpower.graph_optimization import matching, check_matching, max_flow, check_flow, distinct_assignment
from perfectpower.graph_topology import cycle_basis, cellular_homology, mesh_homology, winding_number
from perfectpower.divisor_square import WorkLimit


class CountingTests(unittest.TestCase):
    def test_random_cnf_exhaustive(self):
        r=random.Random(71011)
        for n in range(8):
            for _ in range(40):
                clauses=[[r.choice((-1,1))*r.randint(1,n) for _ in range(r.randrange(5))] for _ in range(r.randrange(9))] if n else ([[]] if r.randrange(2) else [])
                expected=sum(all(any(bool(a[abs(l)-1])==(l>0) for l in c) for c in clauses) for a in product((0,1),repeat=n))
                p=count_cnf(n,clauses); self.assertEqual(p['count'],expected); self.assertTrue(check_count(cnf_model(n,clauses),p))
    def test_finite_polynomial_bridge(self):
        ds=[list(range(-3,4)),list(range(10))]
        f=predicate_factor(ds,[0,1],lambda x,y:x*x==y)
        model={'domains':ds,'factors':[f]}
        self.assertEqual(count_factors(model)['count'],7)
        self.assertEqual(count_factors(condition(model,{0:-2}))['count'],1)
        for i in range(7): self.assertEqual(rank_assignment(model,unrank(model,i)),i)
    def test_weighted_unsorted_scopes_and_domains(self):
        r=random.Random(111)
        for _ in range(80):
            ds=[[3,1],[5,2,9],[0,4]]
            fs=[{'scope':[2,0],'values':[r.randrange(4) for _ in range(4)]}, {'scope':[1,2],'values':[r.randrange(4) for _ in range(6)]}, {'scope':[],'values':[3]}]
            expected=0
            for a in product(*ds):
                expected+=3*fs[0]['values'][ds[2].index(a[2])*2+ds[0].index(a[0])]*fs[1]['values'][ds[1].index(a[1])*2+ds[2].index(a[2])]
            self.assertEqual(count_factors({'domains':ds,'factors':fs})['count'],expected)
    def test_large_components_and_cache(self):
        p=count_cnf(200,[[i,i+1] for i in range(1,201,2)])
        self.assertEqual(p['count'],3**100); self.assertGreater(p['message_cache_hits'],100)
        self.assertLess(p['cells_visited'],20)
    def test_invalid_and_tampered(self):
        p=count_cnf(3,[[1,2],[-2,3]])
        for field in ('count','cells_visited'):
            q=deepcopy(p);q[field]+=1
            with self.assertRaises(ValueError):check_count(p['source'],q)
        q=deepcopy(p);q['steps'][0]['values'][0]+=1
        with self.assertRaises(ValueError):check_count(p['source'],q)
        with self.assertRaises(ValueError):count_cnf(2,[[0]])
        with self.assertRaises(WorkLimit):count_cnf(30,[list(range(1,31))],cell_limit=100)
        with self.assertRaises(WorkLimit):count_cnf(8,[[1,2,3,4]],cell_limit=8)
        with self.assertRaises(ValueError):count_factors({'domains':[[0]],'factors':[{'scope':[0],'values':[-1]}]})
    def test_population_and_kernel_emitter(self):
        from perfectpower.graph_counting import GraphPopulation
        from perfectpower.graph_lean import compile_cnf
        model=cnf_model(3,[[1,2],[-2,3]])
        p=GraphPopulation(model)
        self.assertEqual(sum(p.marginal(1).values()),p.count())
        self.assertEqual(p.restrict({1:1}).count(),p.marginal(1)[1])
        self.assertEqual(p.rank(p.select(0)),0)
        self.assertGreaterEqual(p.rank(p.sample(random.Random(1))),0)
        q=p.certificate(); q['count']=99; self.assertNotEqual(p.count(),99)
        emitted=compile_cnf(3,[[1,2],[-2,3]])
        self.assertIn('by decide',emitted['source']);self.assertNotIn('native_decide',emitted['source'])
        self.assertEqual(emitted['count'],p.count())
        with self.assertRaises(WorkLimit):compile_cnf(13,[])
    def test_empty_and_unused(self):
        self.assertEqual(count_cnf(0,[])['count'],1)
        self.assertEqual(count_cnf(0,[[]])['count'],0)
        self.assertEqual(count_cnf(100,[[1,-1]])['count'],2**100)


class OptimizationTests(unittest.TestCase):
    def test_matching_exhaustive(self):
        r=random.Random(222)
        for nl in range(6):
            for nr in range(5):
                for _ in range(8):
                    es=[(a,b) for a in range(nl) for b in range(nr) if r.randrange(2)]
                    best=0
                    for selection in product(range(-1,nr),repeat=nl):
                        used=[b for b in selection if b>=0]
                        if len(set(used))==len(used) and all(b<0 or (a,b) in es for a,b in enumerate(selection)):best=max(best,len(used))
                    p=matching(nl,nr,es);self.assertEqual(len(p['matching']),best);self.assertTrue(check_matching(nl,nr,es,p))
    def test_flow_exhaustive_cuts(self):
        r=random.Random(333)
        for n in range(2,9):
            for _ in range(35):
                arcs=[(a,b,r.randrange(6)) for a in range(n) for b in range(n) if a!=b and r.randrange(3)==0]
                arcs+=arcs[:2] # parallel arcs and antiparallel arcs both supported
                cuts=[{0}|{i+1 for i,x in enumerate(bits) if x} for bits in product((0,1),repeat=n-2)]
                expected=min(sum(w for a,b,w in arcs if a in s and b not in s) for s in cuts)
                p=max_flow(n,arcs,0,n-1);self.assertEqual(p['value'],expected);self.assertTrue(check_flow(n,arcs,0,n-1,p))
    def test_hall_and_tampering(self):
        p=distinct_assignment([[1,2],[1,2],[1,2],[9]])
        self.assertEqual(len(p['deficient_variables']),3);self.assertEqual(p['available_values'],[1,2])
        q=matching(2,2,[(0,0),(1,1)]);q['cover_left']=[]
        with self.assertRaises(ValueError):check_matching(2,2,[(0,0),(1,1)],q)
        q=max_flow(3,[(0,1,2),(1,2,2)],0,2);q['flow'][0][1]=3
        with self.assertRaises(ValueError):check_flow(3,[(0,1,2),(1,2,2)],0,2,q)


class GeometryTests(unittest.TestCase):
    def test_cells_kill_cycles(self):
        edges=[(0,1),(1,2),(2,0)]
        self.assertEqual(cellular_homology(3,edges,[])['betti'],[1,1,0])
        self.assertEqual(cellular_homology(3,edges,[[1,1,1]])['betti'],[1,0,0])
        self.assertEqual(cellular_homology(3,edges,[[1,1,1],[1,1,1]])['betti'],[1,0,1])
        with self.assertRaises(ValueError):cellular_homology(3,edges,[[1,0,0]])
    def test_torus_sphere_disk_empty(self):
        self.assertEqual(cellular_homology(1,[(0,0),(0,0)],[[0,0]])['betti'],[1,2,1])
        sphere={'triangles':[[0,1,2],[0,3,1],[0,2,3],[1,3,2]]}
        self.assertEqual(mesh_homology(sphere)['betti'],[1,0,1])
        self.assertEqual(mesh_homology({'triangles':[[0,1,2]]})['betti'],[1,0,0])
        self.assertEqual(cellular_homology(0,[],[])['betti'],[0,0,0])
        self.assertEqual(cycle_basis(2,[(0,1),(0,1),(1,1)])['cycle_rank'],2)
    def test_integral_torsion(self):
        from perfectpower.integer_lifting import verify_smith
        p=cellular_homology(1,[(0,0)],[[2]])
        self.assertEqual(p['betti'],[1,0,0])
        self.assertEqual(p['integral_h1']['torsion_invariant_factors'],[2])
        self.assertTrue(verify_smith(p['integral_h1']['smith_certificate']))
    def test_winding(self):
        p=[(0,0),(2,0),(2,2),(0,2),(0,0)]
        self.assertEqual(winding_number(p,(1,1)),1)
        self.assertEqual(winding_number(p[::-1],(1,1)),-1)
        self.assertEqual(winding_number(p,(3,1)),0)
        self.assertEqual(winding_number(p+p[1:],(1,1)),2)
        with self.assertRaises(ValueError):winding_number(p,(0,1))
        with self.assertRaises(ValueError):winding_number(p,(1.0,1))


class StructureTests(unittest.TestCase):
    def test_decompositions(self):
        r=random.Random(444)
        for n in range(20):
            es=[e for e in combinations(range(n),2) if r.randrange(5)==0]
            p=elimination_forest(n,es);self.assertTrue(check_decomposition(n,es,p))
        p=elimination_forest(4,[(0,1),(1,2),(2,3)])
        p['parents'][0]=0
        with self.assertRaises(ValueError):check_decomposition(4,[(0,1),(1,2),(2,3)],p)
    def test_structural_work_limit(self):
        with self.assertRaises(WorkLimit):elimination_forest(20,list(combinations(range(20),2)),work_limit=5)
    def test_machine(self):
        p=machine_structure({'observations':[0,0,1,9],'actions':{'go':[1,2,None,3]}})
        self.assertEqual(p['reachable'],[0,1,2]);self.assertEqual(p['unreachable'],[3])
        self.assertEqual(p['shortest_access_words']['2'],['go','go'])


if __name__=='__main__':unittest.main()
