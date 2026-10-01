"""OEIS ingestion: adapters, parser, discovery, the promotion rule, the Mordell check.

Uses only the committed snapshot `data/oeis/` (unmodified `.seq` files from the official
`oeisdata` export, CC BY-SA 4.0) and synthetic inputs."""
import copy
import hashlib
import json
import tempfile
import unittest
from pathlib import Path

from perfectpower.oeis_orbit import PROVED, atlas, check_proved, discover, mordell_check, orbit
from perfectpower.oeis_source import Entry, GitExport, SeqDir, load_global_index, parse_seq, seq_path

ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / 'data' / 'oeis'


class Snapshot(unittest.TestCase):
    def test_manifest_and_hashes(self):
        man = json.loads((DATA / 'manifest.json').read_text())
        self.assertEqual(man['adapter'], 'GitExport')
        self.assertEqual(len(man['commit']), 40)
        self.assertTrue(man['time_txt'])
        src = SeqDir(DATA)
        for aid, sha in man['files'].items():
            self.assertEqual(hashlib.sha256(src.text(aid).encode()).hexdigest(), sha, aid)

    def test_parser_reads_definitions_and_offsets(self):
        e = parse_seq(SeqDir(DATA).text('A001110'))
        self.assertEqual((e.id, e.offset), ('A001110', 0))
        self.assertEqual(e.terms[:4], [0, 1, 36, 1225])
        self.assertIn('both triangular and square', e.name)
        e = parse_seq(SeqDir(DATA).text('A001653'))
        self.assertEqual((e.offset, e.term(1), e.term(2)), (1, 1, 5))

    def test_seq_path(self):
        self.assertEqual(seq_path('A123456'), 'seq/A123/A123456.seq')
        self.assertEqual(GitExport('/nonexistent').url, 'https://github.com/oeis/oeisdata.git')

    def test_index_drops_truncated_last_term(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / 'idx.tsv'
            p.write_text('id\toffset\tname\tinitial_terms\n'
                         'A900001\t0,2\tx\t1,2,3,45\nA900002\t1,1\ty\t1,2,3,\n')
            idx = load_global_index(p)
            self.assertEqual(idx['A900001'], (0, 'x', [1, 2, 3]))
            self.assertEqual(idx['A900002'], (1, 'y', [1, 2, 3]))


class Promotion(unittest.TestCase):
    def test_every_proved_entry_passes(self):
        src = SeqDir(DATA)
        for aid in PROVED:
            self.assertTrue(check_proved(parse_seq(src.text(aid)))['ok'], aid)

    def test_promotion_needs_terms_offset_and_lean(self):
        e = parse_seq(SeqDir(DATA).text('A001541'))
        bad_term = copy.deepcopy(e)
        bad_term.terms[5] += 1
        self.assertFalse(check_proved(bad_term)['ok'])
        bad_off = copy.deepcopy(e)
        bad_off.offset = 1
        self.assertFalse(check_proved(bad_off)['ok'])
        self.assertFalse(check_proved(e, lean_names=set())['ok'])

    def test_atlas_outcomes(self):
        cands = json.loads((DATA / 'discovery_sqrt2.json').read_text())
        out = {r['oeis']: r for r in atlas(SeqDir(DATA), cands)}
        # hand-written proofs only (SqrtTwoOrbit, SqrtTwoBatch, SqrtTwoBridges, SqrtTwoDefs);
        # generated ones need `auto`
        self.assertEqual(sum(r['outcome'] == 'DEFINITION_PROVED_EQUIVALENT' for r in out.values()), 28)
        for aid in ('A024537', 'A171842', 'A163271', 'A069306'):
            self.assertEqual(out[aid]['outcome'], 'DEFINITION_PROVED_EQUIVALENT', aid)
        self.assertEqual(out['A001333']['outcome'], 'DEFINITION_PROVED_EQUIVALENT')   # convergents (SqrtTwoBridges)
        self.assertEqual(out['A052542']['outcome'], 'REJECTED')              # a(0) = 1, not 0
        self.assertEqual(out['A052542']['agrees_from_term'], 1)


class Discovery(unittest.TestCase):
    def test_finds_coordinates_in_a_synthetic_index(self):
        A, B = orbit(40)
        idx = {'A900001': (0, 'even B', B[0::2][:20]),
               'A900002': (1, 'odd A', A[1::2][:20]),
               'A900003': (0, 'noise', [1, 2, 3, 5, 8, 13, 21, 34, 55, 89])}
        from perfectpower.oeis_orbit import coordinate
        got = {c['oeis']: c for c in discover(idx)}
        self.assertNotIn('A900003', got)
        # whichever equivalent map is reported (B_{2k} is also 2 A_k B_k), it reproduces the terms
        for aid in ('A900001', 'A900002'):
            c = got[aid]
            terms = idx[aid][2]
            self.assertEqual([coordinate(c['filter'], c['map'], c['power_index_of_first_term'] + i)
                              for i in range(len(terms))], terms)


class Mordell(unittest.TestCase):
    def test_certified_lists_match_published_counts(self):
        m = mordell_check(SeqDir(DATA))
        self.assertEqual(m['disagreements'], [])
        by_k = {c['k']: c for c in m['checks']}
        self.assertEqual((by_k[-74]['certified_points'], by_k[-74]['published']), (2, 2))
        self.assertEqual((by_k[-13]['certified_points'], by_k[-13]['published']), (2, 2))
        self.assertGreaterEqual(m['certified_checked'], 40)


if __name__ == '__main__':
    unittest.main()
