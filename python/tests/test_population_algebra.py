import json
import io
from pathlib import Path
import random
import subprocess
import sys
import tempfile
import threading
import unittest
from urllib.request import Request, urlopen

from perfectpower.population_algebra import PopulationComparison
from perfectpower.catalogue import Catalogue
from perfectpower.query_service import dispatch, serve
from perfectpower.http_service import QueryHTTPServer
from perfectpower.divisor_square import WorkLimit


def domain(lo=-12, hi=12, fields=None):
    return dict(kind='domain', fields=fields or {'n': [0, 1]}, predicate={
        'op': 'and', 'args': [{'poly': [-lo, 1], 'relation': '>='},
                             {'poly': [-hi, 1], 'relation': '<='}]})


def spec(universe=None, left=True, right=False):
    return dict(universe=universe or domain(), left=left, right=right)


def curve(T):
    return dict(kind='curve', left=[0, 0, 2], right=[0, 0, 0, 3],
                predicate={'expr': 'y-'+str(6*T*T), 'relation': '<='})


class PopulationAlgebra(unittest.TestCase):
    def check_parts(self, comparison, expected):
        summary = comparison.summary()
        for part, members in expected.items():
            with self.subTest(part=part):
                rows = comparison.page(part, size=len(members)+1)
                identities = [r['record']['parameter'] if comparison.specification['universe']['kind']=='domain'
                              else tuple(r['record']['values'][k] for k in ('x', 'y')) for r in rows]
                self.assertEqual(set(identities), members)
                self.assertEqual(len(rows), len(members))
                self.assertEqual(summary['counts'][part], len(members))
                self.assertEqual(comparison.count(part), len(members))
                for i, row in enumerate(rows):
                    self.assertEqual(row['addresses'][part], i)
                    universe_rank = row['addresses']['universe']
                    self.assertEqual(comparison.transport(part, i, 'universe')['object_id'], row['object_id'])
                    self.assertEqual(comparison.transport('universe', universe_rank, part)['addresses'][part], i)

    def test_random_polynomial_and_modular_partitions_against_integer_sets(self):
        rng = random.Random(92)
        for _ in range(24):
            a, b, c = [rng.randrange(-4, 5) for _ in range(3)]
            modulus = rng.randrange(2, 8)
            residue = rng.randrange(modulus)
            comparison = PopulationComparison(spec(left={'poly': [a,b,c], 'relation': '>='},
                right={'poly': [0,1], 'modulus': modulus, 'relation': '=', 'value': residue}))
            U = set(range(-12, 13)); A = {n for n in U if a+b*n+c*n*n >= 0}
            B = {n for n in U if n % modulus == residue}
            self.check_parts(comparison, dict(universe=U,left=A,right=B,both=A&B,
                left_only=A-B,right_only=B-A,neither=U-(A|B),union=A|B,symmetric_difference=A^B))

    def test_empty_equal_and_disjoint_sides(self):
        for left, right in ((True,True),(False,False),(True,False),(False,True)):
            comparison = PopulationComparison(spec(left=left,right=right))
            U = set(range(-12,13)); A = U if left else set(); B = U if right else set()
            self.check_parts(comparison,dict(universe=U,left=A,right=B,both=A&B,left_only=A-B,
                right_only=B-A,neither=U-(A|B),union=A|B,symmetric_difference=A^B))
        comparison=PopulationComparison(spec(universe=domain(1,0)))
        self.assertEqual(set(comparison.summary()['counts'].values()),{0})
        self.assertIsNone(comparison.locate(parameter=0))

    def test_curve_partition_matches_independent_box(self):
        comparison=PopulationComparison(spec(curve(3),left={'expr':'x','relation':'>='},
            right={'expr':'y-24','relation':'<='}))
        U={(x,y) for x in range(-486,487) for y in range(55) if 2*x*x==3*y**3}
        A={p for p in U if p[0]>=0}; B={p for p in U if p[1]<=24}
        self.check_parts(comparison,dict(universe=U,left=A,right=B,both=A&B,left_only=A-B,
            right_only=B-A,neither=U-(A|B),union=A|B,symmetric_difference=A^B))
        self.assertEqual(comparison.locate(x=0,y=0)['category'],'both')
        self.assertIsNone(comparison.locate(x=1,y=1))

    def test_literal_finite_nonlinear_curve(self):
        universe=dict(kind='curve',left=[1,0,-2,0,1],right=[0,0,0,1])
        comparison=PopulationComparison(spec(universe,left={'expr':'x','relation':'>='},
            right={'expr':'y','relation':'='}))
        U={(-3,4),(-1,0),(0,1),(1,0),(3,4)}; A={p for p in U if p[0]>=0}; B={(-1,0),(1,0)}
        self.check_parts(comparison,dict(universe=U,left=A,right=B,both=A&B,left_only=A-B,
            right_only=B-A,neither=U-(A|B),union=A|B,symmetric_difference=A^B))

    def test_huge_exact_counts_and_transport_without_materialization(self):
        T=10**40
        comparison=PopulationComparison(spec(curve(T),left={'expr':'x','relation':'>='},
            right={'expr':'y-600','relation':'<='}))
        self.assertEqual(comparison.summary()['counts'],dict(universe=2*T+1,left=T+1,right=21,
            both=11,left_only=T-10,right_only=10,neither=T-10,union=T+11,symmetric_difference=T))
        row=comparison.select('right_only',0)
        self.assertEqual(row['record']['values'],dict(x=-18,y=6))
        self.assertEqual(row['addresses']['universe'],T+1)
        self.assertEqual(row['addresses']['right'],11)
        self.assertIsNone(comparison.transport('right_only',0,'left'))
        for part in comparison.PARTS:
            for row in comparison.sample(part,min(3,comparison.count(part)),seed=44):
                x,y=row['record']['values']['x'],row['record']['values']['y']
                self.assertEqual(2*x*x,3*y**3)
                self.assertEqual(comparison.locate(x=x,y=y)['object_id'],row['object_id'])

    def test_duplicate_projections_do_not_merge_original_objects(self):
        comparison=PopulationComparison(spec(domain(-2,2,{'square':[0,0,1]}),
            left={'poly':[0,1],'relation':'>='},right=True))
        negative=comparison.locate(parameter=-2); positive=comparison.locate(parameter=2)
        self.assertEqual(negative['record']['values'],positive['record']['values'])
        self.assertNotEqual(negative['object_id'],positive['object_id'])
        self.assertIsNone(comparison.transport('universe',0,'left'))

    def test_identity_survives_bounds_but_not_changed_definitions(self):
        a=PopulationComparison(spec(curve(4))); b=PopulationComparison(spec(curve(40)))
        self.assertEqual(a.locate(x=18,y=6)['object_id'],b.locate(x=18,y=6)['object_id'])
        self.assertNotEqual(a.comparison_id,b.comparison_id)
        c=PopulationComparison(spec(domain(fields={'different':[0,1]})))
        d=PopulationComparison(spec(domain()))
        self.assertNotEqual(c.family_id,d.family_id)

    def test_foreign_and_forged_records_rejected_copies_isolated(self):
        specification=spec(); comparison=PopulationComparison(specification)
        specification['universe']['fields'].clear()
        row=comparison.select('universe',0)['record']
        self.assertEqual(comparison.classify(row)['addresses']['universe'],0)
        row['values']['n']=123
        with self.assertRaises(ValueError):comparison.classify(row)
        foreign=PopulationComparison(spec(domain(0,10))).select('universe',0)['record']
        with self.assertRaises(ValueError):comparison.classify(foreign)
        copy=comparison.specification;copy['left']=False
        self.assertEqual(comparison.count('left'),25)

    def test_limits_and_invalid_inputs(self):
        comparison=PopulationComparison(spec(),row_limit=2)
        with self.assertRaises(WorkLimit):comparison.page('universe',size=3)
        with self.assertRaises(ValueError):comparison.select('universe',True)
        with self.assertRaises(ValueError):comparison.count('outside')
        with self.assertRaises(IndexError):comparison.transport('universe',25,'left')
        with self.assertRaises(ValueError):PopulationComparison({'universe':domain()})
        with self.assertRaises(ValueError):PopulationComparison(spec(left={'op':'not','args':[]}))

    def test_catalogue_reopen_and_protocol_methods(self):
        with tempfile.TemporaryDirectory() as directory:
            database=Path(directory)/'catalogue.sqlite'
            with Catalogue(database) as cat:
                dispatch(cat,dict(op='register',kind='population_comparison',name='compare',specification=spec()))
            with Catalogue(database) as cat:
                call=lambda method,**args:dispatch(cat,dict(op='call',object='compare',method=method,args=args))
                self.assertEqual(call('summary')['counts']['left'],25)
                row=call('transport',source='left',rank=12,target='universe')
                self.assertEqual(row['record']['parameter'],0)
                self.assertEqual(call('classify',record=row['record'])['object_id'],row['object_id'])
                requests=[dict(request_id=i,op='call',object='compare',method=method,args=args)
                    for i,(method,args) in enumerate([('count',dict(part='outside')),
                        ('population',dict(part='universe')),('select',dict(part='left',rank=0))])]
                output=io.StringIO();serve(cat,io.StringIO('\n'.join(json.dumps(r) for r in requests)),output)
                responses=[json.loads(line) for line in output.getvalue().splitlines()]
                self.assertEqual([r['ok'] for r in responses],[False,False,True])
                self.assertEqual([r['request_id'] for r in responses],[0,1,2])

    def test_cli_and_http_preserve_huge_integer_digits(self):
        T=10**40
        specification=spec(curve(T),left={'expr':'x','relation':'>='},right={'expr':'y-600','relation':'<='})
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'spec.json';path.write_text(json.dumps(specification))
            result=subprocess.run([sys.executable,'-m','perfectpower','population-compare','--spec',str(path),
                '--transport','["right_only",0,"universe"]'],check=True,capture_output=True,text=True)
            self.assertEqual(json.loads(result.stdout)['addresses']['universe'],T+1)
            with QueryHTTPServer(Path(directory)/'http.sqlite') as server:
                thread=threading.Thread(target=server.serve_forever,daemon=True);thread.start()
                url='http://127.0.0.1:'+str(server.server_port)
                def query(request):
                    with urlopen(Request(url+'/query',data=json.dumps(request).encode(),
                        headers={'Content-Type':'application/json'})) as response:return response.read()
                try:
                    with urlopen(url+'/atlas') as response:
                        self.assertIn(b'exact-comparison-title',response.read())
                    query(dict(op='register',kind='population_comparison',name='comparison',specification=specification))
                    raw=query(dict(op='call',object='comparison',method='summary'))
                    self.assertIn(str(2*T+1).encode(),raw)
                    self.assertEqual(json.loads(raw)['result']['counts']['universe'],2*T+1)
                finally:server.shutdown();thread.join()


if __name__=='__main__':unittest.main()
