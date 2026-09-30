"""The definition language (oeis_dsl), the generated Lean pipeline, and the Mordell obstruction
classifier.  Uses only the committed snapshot `data/oeis/`."""
import hashlib
import json
import unittest
from pathlib import Path

from perfectpower import oeis_dsl as S
from perfectpower.descent import diagnose, field_class_number
from perfectpower.oeis_orbit import ORBITS, PROVED_OUTCOMES, atlas, load_auto, transport
from perfectpower.oeis_source import Entry, SeqDir, parse_seq

ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / 'data' / 'oeis'


def entry(aid):
    return parse_seq(SeqDir(DATA).text(aid))


class Language(unittest.TestCase):
    def test_strides_are_traces(self):
        self.assertEqual(S.strides('fib'), {1: (1, 1), 2: (3, -1), 3: (4, 1), 4: (7, -1),
                                            5: (11, 1), 6: (18, -1)})
        self.assertEqual(S.strides('pell2')[2], (6, -1))
        self.assertEqual(S.strides('sqrt3'), {1: (4, -1), 2: (14, -1), 3: (52, -1), 4: (194, -1)})

    def test_family_orbits_match_discovery_orbits(self):
        for fam, orb in (('fib', 'phi'), ('pell2', 'sqrt2'), ('sqrt3', 'sqrt3')):
            A, B = ORBITS[orb](30)
            self.assertEqual(S.family_seq(fam, 'X', 30), A)
            self.assertEqual(S.family_seq(fam, 'Y', 30), B)

    def test_rational_functions_in_lowest_terms(self):
        self.assertEqual(S.parse_ratfun('1/((1 - x)*(1 - 2*x - x^2))'), ([1], [1, -3, 1, 1]))
        self.assertEqual(S.parse_ratfun('(1-x^2)/((1-x)*(1-x-x^2))'), ([1, 1], [1, -1, -1]))
        self.assertIsNone(S.parse_ratfun('x^sqrt(2)'))

    def test_recurrence_reading(self):
        lr = S.parse_linrec('a(n) = 2*a(n-1) + a(n-2) for n > 2, a(0) = a(1) = 1, a(2) = 3.')
        self.assertEqual((lr.coeffs, lr.const, lr.start), ([2, 1], 0, 3))
        lr = S.parse_linrec('a(n+1) = 6*a(n) - a(n-1) + 2, a(0) = 0, a(1) = 2.')
        self.assertEqual((lr.coeffs, lr.const), ([6, -1], 2))

    def test_set_reading_and_domain(self):
        self.assertEqual(S.parse_setsq('Numbers k such that 2*k^2 - 1 is a square.'), S.SetSquare(2, -1, 0))
        self.assertEqual(S.parse_setsq('Positive integers k such that 24*k^2 - 23 is a square.').lo, 1)
        self.assertIsNone(S.parse_setsq('Numbers k such that 4*k^2 + 1 is a square.'))   # D square
        # "Numbers n" whose terms exclude the solution n = 0: read as positive n, recorded
        t = S.translate(entry('A239365'))
        self.assertEqual((t.encoding.lo, bool(t.encoding.domain_note)), (1, True))

    def test_translation_reproduces_every_term(self):
        for aid in ('A001519', 'A048739', 'A075870', 'A001906', 'A011944'):
            e = entry(aid)
            t = S.translate(e)
            self.assertIsNotNone(t, aid)
            if not isinstance(t.encoding, S.SetSquare):
                self.assertEqual(t.encoding.values(e.offset, len(e.terms)), e.terms, aid)

    def test_a_changed_term_is_not_translated(self):
        e = entry('A001519')
        bad = Entry(e.id, e.offset, e.terms[:5] + [e.terms[5] + 1] + e.terms[6:], e.name)
        self.assertIsNone(S.translate(bad))

    def test_seed_certificate_is_complete(self):
        from math import isqrt
        for D, c in ((2, -1), (10, 4), (13, 52), (2, 41)):
            u, v, seeds, Ymax = S.seeds_for(D, c)
            orbit = set()
            for x, y in seeds:
                for _ in range(8):
                    orbit.add(y)
                    x, y = u * x + D * v * y, v * x + u * y
            brute = [k for k in range(0, 5000) if D * k * k + c > 0 and isqrt(D * k * k + c) ** 2 == D * k * k + c]
            self.assertEqual([k for k in sorted(orbit) if k < 5000], brute, (D, c))
            self.assertTrue(S.order_ok(D, u, v, seeds))


class Pipeline(unittest.TestCase):
    def test_generated_blocks_are_the_accepted_ones(self):
        acc = json.loads((DATA / 'auto_accepted.json').read_text())
        self.assertEqual(acc['failed_to_compile'], {})
        for aid in ('A001075', 'A052542', 'A239365', 'A373566'):
            r = S.compile_entry(entry(aid))
            self.assertEqual(hashlib.sha256(r['lean'].encode()).hexdigest(), acc['accepted'][aid], aid)

    def test_generated_file_contains_every_accepted_entry(self):
        text = (ROOT / 'PerfectPower' / 'Generated' / 'OEISAuto.lean').read_text()
        acc = json.loads((DATA / 'auto_accepted.json').read_text())['accepted']
        for aid in acc:
            self.assertIn(f'def {aid} ', text)
        self.assertNotIn('sorry', text)

    def test_shifted_equivalence_is_recorded(self):
        r = S.compile_entry(entry('A052542'))          # a(0) = 1 is a convention; 2 B_n from n = 1
        self.assertEqual((r['family'], r['shift'], r['relation']), ('pell2', 1, 'exact from index 1'))

    def test_withheld_family(self):
        rec = json.loads((ROOT / 'receipts' / 'oeis_auto.json').read_text())
        rows = rec['withheld_sqrt3']
        proved = [r for r in rows if r['status'] == 'PROVED']
        self.assertGreaterEqual(len(proved), 8)
        self.assertTrue(all(r['proved_family'] == 'sqrt3' and r['mechanism_agrees'] for r in proved))

    def test_duplicate_transport_needs_equal_terms(self):
        src = SeqDir(DATA)
        cands = json.loads((DATA / 'discovery_sqrt2.json').read_text())
        rows = atlas(src, cands, auto=load_auto())
        transport(src, rows)
        out = {r['oeis']: r for r in rows}
        self.assertEqual(out['A090757']['outcome'], 'TRANSPORTED_FROM_DUPLICATE')
        self.assertIn(out['A048739']['outcome'], PROVED_OUTCOMES)
        # not an equal-index duplicate; the terms fix a unique shift, recorded as such
        self.assertEqual(out['A048624']['outcome'], 'TRANSPORTED_WITH_SHIFT')
        self.assertEqual(out['A048624']['proof']['shift_from_terms'], 2)


class Obstructions(unittest.TestCase):
    def test_categories(self):
        d = diagnose(1)                                                        # y^2 = x^3 - 1
        self.assertEqual(d['categories'], ['ELEMENT_CUBE', 'UNIT_BEYOND_PM1'])
        self.assertTrue(d['units']['all_cubes'])                               # i = (-i)^3
        self.assertEqual(diagnose(26)['categories'], ['CLASS_3'])
        self.assertEqual(diagnose(7)['categories'], ['NOT_COPRIME'])
        self.assertEqual(diagnose(5)['categories'], ['CERTIFIED'])
        self.assertIn('NONMAXIMAL_CUBE', diagnose(11)['categories'])

    def test_field_class_numbers(self):
        self.assertEqual([field_class_number(D) for D in (1, 2, 5, 23, 26, 47)], [1, 1, 2, 3, 6, 5])


if __name__ == '__main__':
    unittest.main()
