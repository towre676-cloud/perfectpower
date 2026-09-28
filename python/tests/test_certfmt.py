"""pp-cert/1: round trip JSON -> Lean -> JSON, and rejection of malformed certificates."""
import copy
import json
import unittest
from pathlib import Path

from perfectpower.certfmt import CertError, from_lean, statement_hash, to_lean, validate

ROOT = Path(__file__).resolve().parents[2]


def load_all():
    return [json.loads(p.read_text()) for p in sorted((ROOT / 'certs').glob('*/*.json'))]


class RoundTrip(unittest.TestCase):
    def test_all_committed_certificates_validate(self):
        certs = load_all()
        self.assertEqual(len(certs), 19)
        for c in certs:
            validate(c)

    def test_json_lean_json(self):
        for c in load_all():
            back = from_lean(to_lean(c))
            for key in ('kind', 'name', 'statement', 'statement_sha256', 'data'):
                self.assertEqual(back[key], c[key], (c['name'], key))

    def test_generated_files_are_the_import_of_the_json(self):
        for sub, lean in (('runge', 'Runge.lean'), ('sandwich', 'Sandwich.lean')):
            text = (ROOT / 'PerfectPower' / 'Generated' / lean).read_text()
            for p in sorted((ROOT / 'certs' / sub).glob('*.json')):
                self.assertIn(to_lean(json.loads(p.read_text())), text, p.name)


class Rejects(unittest.TestCase):
    def setUp(self):
        certs = {c['name']: c for c in load_all()}
        self.sw = certs['consecutive12_fourth_power_hits']
        self.rg = certs['ljunggren_quartic_hits']

    def rejects(self, cert):
        with self.assertRaises(CertError):
            validate(cert)

    def mutate(self, cert, f, rehash=True):
        c = copy.deepcopy(cert)
        f(c)
        if rehash:
            c['statement_sha256'] = statement_hash(c['statement'])
        return c

    def test_changed_polynomial_without_rehash(self):
        c = copy.deepcopy(self.sw)
        c['statement']['F'][0] += 1
        self.rejects(c)

    def test_changed_polynomial_with_rehash(self):
        # the producer silently changed F and rehashed: the witnesses no longer fit
        self.rejects(self.mutate(self.rg, lambda c: c['statement']['F'].__setitem__(0, 2)))

    def test_gap_and_overlap(self):
        self.rejects(self.mutate(self.sw, lambda c: c['data']['segments'].pop(3)))
        self.rejects(self.mutate(self.sw, lambda c: c['data']['segments'].insert(4, c['data']['segments'][3])))

    def test_off_by_one_end(self):
        self.rejects(self.mutate(self.sw, lambda c: c['data'].__setitem__('tail_start', c['data']['tail_start'] + 1)))
        self.rejects(self.mutate(self.rg, lambda c: c['data'].__setitem__('x0', c['data']['x0'] - 1)))

    def test_bad_exponent_and_hits(self):
        self.rejects(self.mutate(self.rg, lambda c: c['statement'].__setitem__('d', 1)))
        self.rejects(self.mutate(self.rg, lambda c: c['statement'].__setitem__('hits', [])))

    def test_bad_witness_and_signs(self):
        def bad_gap(c):
            s = next(s for s in c['data']['segments'] if s['k'] == 'gap')
            s['a'] += 1
        self.rejects(self.mutate(self.sw, bad_gap))
        self.rejects(self.mutate(self.rg, lambda c: c['data']['signs'].append(1)))

    def test_ival_not_allowed_in_runge(self):
        self.rejects(self.mutate(self.rg, lambda c: c['data']['segments'].__setitem__(
            0, {'k': 'ival', 'lo': 1, 'hi': 1, 't': 0})))


if __name__ == '__main__':
    unittest.main()
