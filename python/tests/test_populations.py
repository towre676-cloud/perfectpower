import itertools
import json
from pathlib import Path
import random
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from perfectpower.populations import ExactPopulation
from perfectpower.divisor_square import WorkLimit


def domain(lo, hi, *, predicate=True, fields=None):
    return dict(kind='domain', predicate={'op': 'and', 'args': [
        {'poly': [-lo, 1], 'relation': '>='}, {'poly': [-hi, 1], 'relation': '<='}, predicate]},
        fields=fields or {'n': [0, 1]})


class Populations(unittest.TestCase):
    def test_negative_and_disconnected_rank_roundtrips(self):
        p = ExactPopulation(domain(-20, 20, predicate={'op': 'or', 'args': [
            {'poly': [0, 1], 'modulus': 5, 'relation': '=', 'value': 2},
            {'poly': [0, 1], 'relation': '='}]}))
        expected = [n for n in range(-20, 21) if n % 5 == 2 or n == 0]
        self.assertEqual(p.cardinality, len(expected))
        for i, n in enumerate(expected):
            record = p.select(i)
            self.assertEqual(record['parameter'], n)
            self.assertEqual(p.rank(record), i)
            self.assertEqual(p.locate(parameter=n),i)
        self.assertEqual(p.next(-19)['parameter'],-18)
        self.assertEqual(p.next(-18,inclusive=True)['parameter'],-18)
        self.assertIsNone(p.next(17))
        self.assertEqual(p.page(1,2),[p.select(1),p.select(2)])
        self.assertEqual(p.page(100,2),[])

    def test_independent_random_domains(self):
        rng = random.Random(843)
        for _ in range(60):
            a, b, c = [rng.randrange(-4, 5) for _ in range(3)]
            m = rng.randrange(2, 10)
            r = rng.randrange(m)
            predicate = {'op': 'and', 'args': [
                {'poly': [a, b, c], 'relation': '>='},
                {'poly': [0, 1], 'modulus': m, 'relation': '!=', 'value': r}]}
            p = ExactPopulation(domain(-25, 25, predicate=predicate, fields={'square': [0, 0, 1]}))
            expected = [n for n in range(-25, 26) if a+b*n+c*n*n >= 0 and n % m != r]
            self.assertEqual(p.cardinality, len(expected))
            self.assertEqual([p.select(i)['parameter'] for i in range(p.cardinality)], expected)

    def test_duplicate_projected_values_keep_parameter_identity(self):
        p = ExactPopulation(domain(-2, 2, fields={'square': [0, 0, 1]}))
        self.assertEqual(p.cardinality, 5)
        records = p.sample(5, seed=31)
        self.assertEqual(len({r['parameter'] for r in records}), 5)
        self.assertEqual(len({r['values']['square'] for r in records}), 3)

    def test_curve_original_points_against_exhaustive_box(self):
        for left, right, relation in [([0, 0, 1], [0, 0, 0, 1], lambda x,y:x*x == y**3),
                                     ([0, 0, 2], [0, 0, 0, 3], lambda x,y:2*x*x == 3*y**3),
                                     ([0, 0, 1], [0, 0, 1], lambda x,y:x*x == y*y)]:
            spec = dict(kind='curve', left=left, right=right, predicate={'op': 'and', 'args': [
                {'expr': 'x*x-400', 'relation': '<='}, {'expr': 'y*y-400', 'relation': '<='}]})
            p = ExactPopulation(spec)
            actual = {(x,y) for x in range(-20,21) for y in range(-20,21) if relation(x,y)}
            records = [p.select(i) for i in range(p.cardinality)]
            self.assertEqual({tuple(r['values'][k] for k in ('x','y')) for r in records}, actual)
            self.assertEqual(len(records), len(actual))
            for i, record in enumerate(records):
                self.assertEqual(p.rank(record), i)
                self.assertEqual(p.locate(**record['values']),i)
            self.assertIsNone(p.locate(x=21,y=-20))

    def test_zero_chart_ownership_and_empty_first_chart(self):
        p = ExactPopulation(dict(kind='curve', left=[0,0,1], right=[0,0,0,1], predicate={
            'op':'and','args':[{'expr':'x','relation':'<'},{'expr':'y-9','relation':'<='}]}))
        self.assertEqual([p.select(i)['values'] for i in range(p.cardinality)],
                         [dict(x=-1,y=1),dict(x=-8,y=4),dict(x=-27,y=9)])

    def test_finite_nonlinear_curve(self):
        p = ExactPopulation(dict(kind='curve', left=[1,0,-2,0,1], right=[0,0,0,1]))
        self.assertEqual(p.cardinality, 5)
        self.assertEqual([p.select(i)['values'] for i in range(5)],
                         [dict(x=-3,y=4),dict(x=-1,y=0),dict(x=0,y=1),dict(x=1,y=0),dict(x=3,y=4)])
        for i in range(5):
            self.assertEqual(p.rank(p.select(i)),i)

    def test_huge_curve_population_and_shards(self):
        T = 10**40
        p = ExactPopulation(dict(kind='curve', left=[0,0,2], right=[0,0,0,3],
                                 predicate={'expr':'y-'+str(6*T*T),'relation':'<='}))
        self.assertEqual(p.cardinality,2*T+1)
        self.assertEqual(p.select(T)['values'],dict(x=18*T**3,y=6*T*T))
        self.assertEqual(p.select(2*T)['values'],dict(x=-18*T**3,y=6*T*T))
        for record in p.sample(17,seed=40):
            self.assertEqual(p.rank(record),record['rank'])
            x,y=record['values']['x'],record['values']['y']
            self.assertEqual(2*x*x,3*y**3)
        shards=[p.partition(7,i) for i in range(7)]
        self.assertEqual(shards[0]['start'],0)
        self.assertEqual(shards[-1]['stop'],p.cardinality)
        self.assertTrue(all(a['stop']==b['start'] for a,b in zip(shards,shards[1:])))
        self.assertLessEqual(max(s['stop']-s['start'] for s in shards)-min(s['stop']-s['start'] for s in shards),1)

    def test_exhaustive_sampler_uniform_ordered_triples(self):
        p=ExactPopulation(domain(0,3))
        outcomes=[]
        class Draws:
            def __init__(self, digits):self.digits=iter(digits)
            def randrange(self,n):
                value=next(self.digits)
                assert 0<=value<n
                return value
        for digits in itertools.product(range(4),range(3),range(2)):
            with patch('perfectpower.populations.random.Random',return_value=Draws(digits)):
                outcomes.append(tuple(r['rank'] for r in p.sample(3)))
        self.assertEqual(len(outcomes),24)
        self.assertEqual(set(outcomes),set(itertools.permutations(range(4),3)))

    def test_reproducible_sampling_replacement_and_empty(self):
        p=ExactPopulation(domain(0,100))
        self.assertEqual(p.sample(25,seed=81),p.sample(25,seed=81))
        self.assertEqual(len({r['rank'] for r in p.sample(101)}),101)
        one=ExactPopulation(domain(5,5))
        self.assertEqual([r['parameter'] for r in one.sample(8,replace=True)],[5]*8)
        empty=ExactPopulation(domain(1,0))
        self.assertEqual(empty.sample(0),[])
        with self.assertRaises(ValueError):empty.sample(1)

    def test_restriction_and_optimization_ties(self):
        p=ExactPopulation(domain(-10,10))
        q=p.restrict({'poly':[0,1],'modulus':2,'relation':'=','value':1})
        self.assertEqual(q.cardinality,10)
        optimum=q.optimize([0,0,1])
        self.assertEqual(optimum['value'],1)
        self.assertEqual(optimum['points'],[-1,1])
        c=ExactPopulation(dict(kind='curve',left=[0,0,2],right=[0,0,0,3],predicate={
            'op':'and','args':[{'expr':'y','relation':'>'},{'expr':'y-600','relation':'<='}]}))
        self.assertEqual(c.optimize('x*x+y*y')['optimizer_points'],[(-18,6),(18,6)])

    def test_public_copies_and_invalid_records(self):
        spec=domain(0,5)
        p=ExactPopulation(spec)
        spec['fields'].clear()
        copy=p.specification;copy['fields'].clear()
        evidence=p.evidence();evidence['cells'].clear()
        record=p.select(2);record['values']['n']=3
        with self.assertRaises(ValueError):p.rank(record)
        record=p.select(2);record['population_id']='other'
        with self.assertRaises(ValueError):p.rank(record)
        record=p.select(2);record['values']['n']=True
        with self.assertRaises(ValueError):p.rank(record)
        self.assertEqual(p.select(2)['values'],{'n':2})

    def test_limits_and_unsupported_populations(self):
        p=ExactPopulation(domain(0,2),row_limit=2)
        with self.assertRaises(WorkLimit):p.sample(3)
        with self.assertRaises(ValueError):p.sample(3,replace=True,seed=True)
        with self.assertRaises(ValueError):p.select(True)
        with self.assertRaises(IndexError):p.select(3)
        with self.assertRaises(ValueError):p.partition(2,2)
        with self.assertRaises(ValueError):ExactPopulation({'kind':'domain'})
        with self.assertRaises(ValueError):ExactPopulation({'kind':'curve','left':[0,0,1],'right':[0,0,0,1]})
        with self.assertRaises(ValueError):ExactPopulation(domain(0,1,fields={'_hidden':[1]}))
        tiny=ExactPopulation(domain(0,10,fields={'large':[0,0,0,1]}),bit_limit=4)
        with self.assertRaises(WorkLimit):tiny.select(10)

    def test_dataset_atomic_and_cli(self):
        p=ExactPopulation(domain(-10,10))
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)
            a,b=root/'a.jsonl',root/'b.jsonl'
            first=p.export(a,size=8,seed=91);second=p.export(b,size=8,seed=91)
            self.assertEqual(a.read_bytes(),b.read_bytes())
            self.assertEqual(first['sha256'],second['sha256'])
            rows=[json.loads(line) for line in a.read_text().splitlines()]
            self.assertEqual(rows[0]['metadata']['population']['cardinality'],21)
            for row in rows[1:]:self.assertEqual(p.rank(row),row['rank'])
            old=a.read_bytes()
            with self.assertRaises(ValueError):p.export(a,size=22)
            self.assertEqual(a.read_bytes(),old)
            spec=root/'spec.json';spec.write_text(json.dumps(domain(-10,10)))
            run=subprocess.run([sys.executable,'-m','perfectpower','population','--spec',str(spec),'--rank','0'],
                               check=True,capture_output=True,text=True)
            self.assertEqual(json.loads(run.stdout)['parameter'],-10)


if __name__=='__main__':unittest.main()
