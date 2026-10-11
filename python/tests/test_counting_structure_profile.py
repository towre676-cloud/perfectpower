import itertools
import io
import random
import sys
import tarfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from profile_counting_structure import normalize, profile, propagate
from trace_counting_origins import identity, members
from select_counting_advantage import round_robin


class StructureProfileTests(unittest.TestCase):
    def test_nested_sources_are_read_without_extraction(self):
        def archive(name, payload):
            buffer=io.BytesIO()
            with tarfile.open(fileobj=buffer,mode='w') as tar:
                info=tarfile.TarInfo(name);info.size=len(payload)
                tar.addfile(info,io.BytesIO(payload))
            return buffer.getvalue()
        inner=archive('../../example.cnf',b'p cnf 1 1\n1 0\n')
        outer=archive('collection/family.tar',inner)
        with tarfile.open(fileobj=io.BytesIO(outer)) as tar:
            result=list(members(tar))
        self.assertEqual(result,[('collection/family.tar!../../example.cnf',b'p cnf 1 1\n1 0\n')])

    def test_selection_ignores_order_and_timing(self):
        rows=[{'family':f,'sha256':str(i),'member':f+str(i),'seconds':100-i}
              for f in ('A','B') for i in (3,1,2)]
        selected=[r['member'] for r in round_robin(rows,4)]
        random.Random(4269).shuffle(rows)
        for r in rows:r['seconds']=random.Random(r['member']).random()
        self.assertEqual(selected,[r['member'] for r in round_robin(rows,4)])
        self.assertEqual(selected,['A1','B1','A2','B2'])

    def test_origin_identity_preserves_declared_universe(self):
        a = identity('p cnf 4 2\n1 -2 0\n3 0\n')
        b = identity('c source\np cnf 4 3\n3 0\n-2 1 1 0\n1 -2 0\n')
        self.assertEqual(a, b)
        self.assertNotEqual(a, identity('p cnf 5 2\n1 -2 0\n3 0\n'))
        self.assertNotEqual(a, identity('p cnf 4 2\n-1 -2 0\n3 0\n'))
    def test_unit_reduction_preserves_models_on_original_coordinates(self):
        rng = random.Random(4269)
        for _ in range(150):
            n = 6
            clauses = normalize([tuple(rng.choice((-1, 1)) * rng.randint(1, n)
                                       for _ in range(rng.randint(0, 4)))
                                 for _ in range(rng.randint(0, 12))])
            residual, fixed, contradiction = propagate(clauses)
            for bits in itertools.product((False, True), repeat=n):
                accepts = lambda f: all(any(bits[abs(x)-1] == (x > 0) for x in c) for c in f)
                expected = accepts(clauses)
                actual = not contradiction and all(bits[v-1] == b for v, b in fixed.items()) and accepts(residual)
                self.assertEqual(expected, actual)

    def test_path_and_clique_scopes(self):
        path = 'p cnf 900 899\n' + ''.join(f'{i} {i+1} 0\n' for i in range(1, 900))
        d = profile(path)
        self.assertTrue(d['all_components_accepted'])
        self.assertEqual(d['components'][0]['max_scope'], 2)
        self.assertEqual(d['components'][0]['estimated_states'], 899*4+2)
        clique = 'p cnf 19 171\n' + ''.join(f'{i} {j} 0\n' for i in range(1, 20) for j in range(i+1, 20))
        d = profile(clique)
        self.assertFalse(d['all_components_accepted'])
        self.assertEqual(d['components'][0]['status'], 'SCOPE_LIMIT')

    def test_free_variables_and_contradiction(self):
        d = profile('p cnf 10 2\n1 0\n-1 2 0\n')
        self.assertEqual(d['unit_fixed_variables'], 2)
        self.assertEqual(d['residual_free_variables'], 8)
        self.assertTrue(profile('p cnf 1 2\n1 0\n-1 0\n')['unit_contradiction'])


if __name__ == '__main__':
    unittest.main()
