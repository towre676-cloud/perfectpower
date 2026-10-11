import itertools
import random
import unittest
from perfectpower.model_counting import CNF,CNFCounter,exact_decimal
from perfectpower.divisor_square import WorkLimit

def models(f,locks=()):
    return [list(p) for p in itertools.product((0,1),repeat=f.variables) if f.accepts(list(p)) and all(p[abs(x)-1]==int(x>0) for x in locks)]

def xor_clauses(variables,parity):
    return [tuple(-v if bit else v for v,bit in zip(variables,bits)) for bits in itertools.product((0,1),repeat=len(variables)) if sum(bits)%2!=parity]

class ModelCountingTests(unittest.TestCase):
    def test_large_sparse_count_with_free_declared_variables(self):
        # Above the former factor-elimination dimension budget, a star has an
        # independently derived count: x1=true frees 269 variables, while
        # x1=false forces them all. Three declared variables stay free.
        f=CNF(273,tuple((1,v) for v in range(2,271)))
        with CNFCounter(f) as c:
            expected=8*((1<<269)+1)
            self.assertEqual(c.count(),expected)
            self.assertGreater(c.last['extended_plans'],0)
            self.assertEqual(c.count([-2]),1<<271)
            first=[0]+[1]*269+[0]*3
            self.assertEqual(c.select(0),first)
            self.assertEqual(c.rank(first),0)
            self.assertEqual(c.select(expected-1),[1]*273)

    def test_equivalences_emerging_after_conditioning(self):
        # x1=false permits 260 independent bits. With x1=true the 130
        # pairs must agree. The original lexicographic boundary is 2^263
        # after including three free declared variables.
        clauses=tuple(clause for i in range(130) for clause in
                      ((-1,-(2+2*i),3+2*i),(-1,2+2*i,-(3+2*i))))
        f=CNF(264,clauses)
        with CNFCounter(f) as c:
            self.assertEqual(c.count(),8*((1<<260)+(1<<130)))
            self.assertEqual(c.count([1,2,-3]),0)
            self.assertEqual(c.count([-1,2,-3]),1<<261)
            self.assertEqual(c.count([1,2]),1<<132)
            self.assertGreater(c.last['equivalence_variables'],0)
            boundary=[1]+[0]*263
            self.assertEqual(c.select(1<<263),boundary)
            with CNFCounter(f) as fresh:self.assertEqual(fresh.rank(boundary),1<<263)

    def test_unique_gate_projection_and_original_coordinates(self):
        rng=random.Random(9187)
        for case in range(8):
            clauses=[];definitions=[];previous=1
            for v in range(6,266):
                a=previous*rng.choice((-1,1));b=(v%5+1)*rng.choice((-1,1));out=v*rng.choice((-1,1))
                clauses.extend(((-out,a),(-out,b),(out,-a,-b)))
                definitions.append((out,a,b));previous=v
            points=[]
            for bits in itertools.product((0,1),repeat=5):
                point=list(bits)
                for out,a,b in definitions:
                    value=(point[abs(a)-1]==int(a>0)) and (point[abs(b)-1]==int(b>0))
                    point.append(int(value==bool(out>0)))
                points.extend(point+list(free) for free in itertools.product((0,1),repeat=2))
            if case:
                witness=points[rng.randrange(len(points))]
                for _ in range(case):
                    clause=[v*rng.choice((-1,1)) for v in rng.sample(range(1,266),3)]
                    if not any(witness[abs(x)-1]==int(x>0) for x in clause):clause[0]=-clause[0]
                    clauses.append(tuple(clause))
            f=CNF(267,tuple(clauses));expected=[p for p in points if f.accepts(p)]
            with CNFCounter(f,timeout=30) as c:
                self.assertEqual(c.count(),len(expected),case)
                if case==0:self.assertGreater(c.last['gate_variables'],0)
                locks=[1,265];conditional=[p for p in expected if p[0] and p[264]]
                self.assertEqual(c.count(locks),len(conditional),case)
                if case==0:
                    for rank in (0,len(expected)//2,len(expected)-1):
                        self.assertEqual(c.select(rank),expected[rank])
                        with CNFCounter(f,timeout=30) as fresh:self.assertEqual(fresh.rank(expected[rank]),rank)

    def test_large_path_elimination_independent_recurrence(self):
        # No two adjacent bits may both be zero: Fibonacci population.
        n=900;a,b=1,2
        for _ in range(n):a,b=b,a+b
        with CNFCounter(CNF(n,tuple((v,v+1) for v in range(1,n))),timeout=10) as c:
            self.assertEqual(c.count(),a)
            self.assertGreater(c.last['extended_plans'],0)

    def test_signed_equivalence_quotient_and_original_queries(self):
        # Both signs, a transitive SCC, a disappearing tautology, and a
        # declared free variable: the quotient must not multiply by 2^3.
        f=CNF(5,((-1,2),(1,-2),(-2,-3),(2,3),(-3,4),(3,-4),(1,-2,5)))
        expected=models(f)
        with CNFCounter(f) as c:
            self.assertEqual(c.count(),len(expected))
            self.assertEqual(c.last['equivalence_variables'],3)
            for locks in ((),(1,),(-3,),(2,3),(5,)):
                points=models(f,locks);self.assertEqual(c.count(locks),len(points))
                for i,p in enumerate(points):
                    self.assertEqual(c.select(i,locks),p);self.assertEqual(c.rank(p,locks),i)
        # A literal and its complement in the same SCC refute the formula
        # even though there are no unit clauses.
        with CNFCounter(CNF(2,((1,2),(-1,2),(1,-2),(-1,-2)))) as c:
            self.assertEqual(c.count(),0)

    def test_long_unit_chain_and_equivalence_chain(self):
        n=20000
        with CNFCounter(CNF(n,((1,),)+tuple((-v,v+1) for v in range(1,n))),timeout=5) as c:
            self.assertEqual(c.count(),1)
        # Iterative SCC traversal must handle a chain deeper than the
        # counting search depth without overflowing the C++ call stack.
        clauses=tuple(clause for v in range(1,n) for clause in ((-v,v+1),(v,-v-1)))
        with CNFCounter(CNF(n+1,clauses),timeout=5) as c:
            self.assertEqual(c.count(),4)
            self.assertEqual(c.last['equivalence_variables'],n-1)

    def test_parser(self):
        f=CNF.parse('c example\np cnf 4 3\n1 1\n-2 0 2 -2 0\n0\n')
        self.assertEqual(f.variables,4);self.assertEqual(f.clauses,((),(-2,1)))
        for bad in ['1 0','p cnf 2 1\n3 0','p cnf 2 2\n1 0','p cnf 2 1\n1','p cnf 2 0\np cnf 2 0','p cnf 2 0\n0','p wcnf 2 0','p cnf -1 0','p cnf 1 0\nc p weight 1 0.5 0','p cnf 1 0\nc p show 1 0']:
            with self.subTest(bad=bad),self.assertRaises(ValueError):CNF.parse(bad)
        with self.assertRaises(WorkLimit):CNF.parse('p cnf 200001 0')
        with self.assertRaises(ValueError):CNF(2,((True,),))
    def test_exhaustive_random(self):
        rng=random.Random(7481)
        for case in range(240):
            n=rng.randrange(0,10);clauses=[]
            for _ in range(rng.randrange(20)):
                clauses.append(tuple(rng.choice((-1,1))*rng.randrange(1,n+1) for _ in range(rng.randrange(5))) if n else ())
            f=CNF(n,tuple(clauses))
            with CNFCounter(f,cache_bytes=0 if case%2 else 1024**2) as counter:
                locks=tuple(rng.choice((-1,1))*v for v in range(1,n+1) if rng.random()<.3)
                expected=models(f,locks)
                self.assertEqual(counter.count(),len(models(f)),case)
                self.assertEqual(counter.count(locks),len(expected),case)
                for rank in set([0,len(expected)//2,len(expected)-1]) if expected else []:
                    point=counter.select(rank,locks);self.assertEqual(point,expected[rank],case)
                    self.assertEqual(counter.rank(point,locks),rank,case)
                    with CNFCounter(f) as fresh:self.assertEqual(fresh.rank(point,locks),rank,case)
                if expected:
                    self.assertIn(counter.sample(locks,seed=17),expected)
                    self.assertEqual(counter.sample(locks,seed=17),counter.sample(locks,seed=17))
    def test_components_and_large_counts(self):
        f=CNF(180,tuple((3*i+1,3*i+2) for i in range(60)))
        with CNFCounter(f) as c:
            self.assertEqual(c.count(),6**60)
            self.assertGreater(c.last['component_splits'],0)
            self.assertGreater(c.last['cache_hits'],0)
            self.assertEqual(c.count([1,-2]),2*6**59)
            self.assertEqual(c.count([1,-1]),0)
        with CNFCounter(CNF(20000,())) as c:
            self.assertEqual(c.count().bit_length(),20001)
            self.assertEqual(exact_decimal(c.last['count']),1<<20000)
    def test_affine_and_mixed(self):
        for case in range(32):
            clauses=xor_clauses([1,2,3],case%2)+xor_clauses([3,4,5],(case//2)%2)
            if case&4:clauses+=xor_clauses([1,2,4,5],(case//8)%2)
            if case&16:clauses+=[(1,4)]
            f=CNF(6,tuple(clauses))
            with CNFCounter(f) as c:
                self.assertEqual(c.count(),len(models(f)))
                self.assertEqual(c.count([-2,5]),len(models(f,[-2,5])))
        with CNFCounter(CNF(3,tuple(xor_clauses([1,2,3],0)))) as c:
            self.assertEqual(c.count(),4);self.assertEqual(c.last['affine_solves'],1)
    def test_planted_nontrivial_formulas(self):
        rng=random.Random(4269)
        for case in range(100):
            n=rng.randrange(7,12);witness=[rng.randrange(2) for _ in range(n)];clauses=[]
            for _ in range(rng.randrange(12,32)):
                variables=rng.sample(range(1,n+1),3)
                c=[v*rng.choice((-1,1)) for v in variables]
                if not any(witness[abs(x)-1]==int(x>0) for x in c):c[0]=-c[0]
                clauses.append(tuple(c))
            f=CNF(n,tuple(clauses));expected=models(f)
            with CNFCounter(f) as counter:
                self.assertEqual(counter.count(),len(expected))
                for rank in (0,len(expected)//2,len(expected)-1):
                    point=counter.select(rank);self.assertEqual(point,expected[rank]);self.assertEqual(counter.rank(point),rank)
                locks=tuple(v if witness[v-1] else -v for v in (1,n))
                self.assertEqual(counter.count(locks),len(models(f,locks)))
    def test_public_fixture(self):
        from perfectpower.resources import runtime_root
        f=CNF.read(runtime_root()/'data/model_counting/fixtures/mc2024_track1_118.cnf')
        with CNFCounter(f) as counter:
            self.assertEqual(counter.count(),17528422464)
            self.assertEqual(counter.last['elimination_solves'],1)
            point=counter.sample(seed=17);self.assertTrue(f.accepts(point))
            rank=counter.rank(point)
            with CNFCounter(f) as fresh:self.assertEqual(fresh.select(rank),point)
    def test_counting_semantics_and_errors(self):
        # SAT's pure-literal elimination would give the wrong count here.
        with CNFCounter(CNF(3,((1,2),(1,3)))) as c:
            self.assertEqual(c.count(),5)
            for locks in ([0],[4],[True]):
                with self.assertRaises(ValueError):c.count(locks)
            for rank in (-1,True,5):
                with self.assertRaises(ValueError):c.select(rank)
            with self.assertRaises(ValueError):c.rank([0,0,0])
            with self.assertRaises(ValueError):c.rank([1,True,1])
            with self.assertRaises(ValueError):c.sample(seed=True)
            with self.assertRaises(ValueError):c.result(timeout=float('nan'))
            with self.assertRaises(ValueError):c.result(timeout=False)
        with self.assertRaises(ValueError):c.count()
        with CNFCounter(CNF(1,((),))) as c:
            self.assertEqual(c.count(),0)
            with self.assertRaises(ValueError):c.sample()
        with CNFCounter(CNF(0,())) as c:
            self.assertEqual(c.count(),1);self.assertEqual(c.select(0),[]);self.assertEqual(c.rank([]),0)
        for value in ('', '-1', '１', 'abc'):
            with self.assertRaises(ValueError):exact_decimal(value)

if __name__=='__main__':unittest.main()
