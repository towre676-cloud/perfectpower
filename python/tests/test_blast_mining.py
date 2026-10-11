"""Independent subset/path/string oracles for the new BLAST mining adapters."""
import json
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import random
import tempfile
import unittest

from perfectpower.blast_alignment import weights
from perfectpower.blast_chains import chain_population
from perfectpower.blast_io import fasta, tabular
from perfectpower.blast_mining import (ChainIndex, HSPSelectionPopulation, selection_model,
    motif_series, motif_values, similarity_topology, assignment_diagnosis, capacity_assignment, mine, verify_mining)
from perfectpower.blast_report import json_ready
from perfectpower.divisor_square import WorkLimit
from test_blast_atlas import hit


class ChainTests(unittest.TestCase):
    def test_dag_matches_complete_enumerator_with_guards(self):
        hs = [hit(qs=1, ss=1), hit(qs=5, ss=5), hit(qs=9, ss=9), hit(qs=5, ss=9)]
        for minimum in (0, 4, 8, 12, 13):
            for gap in (None, 0, 3):
                options = dict(min_coverage=minimum, max_query_gap=gap)
                expected = chain_population(hs, weights(), **options)
                index = ChainIndex(hs, **options)
                self.assertEqual(index.count, expected['count'])
                actual = {tuple(index.select(r)) for r in range(index.count)}
                self.assertEqual(actual, {tuple(x['hits']) for x in expected['chains']})
                for r in range(index.count): self.assertEqual(index.rank(index.select(r)), r)
                if actual:
                    value = max(Q(x['score']) for x in expected['chains'])
                    self.assertEqual(Q(index.optimum['score']), value)
                    self.assertEqual(index.optimum['count'], sum(Q(x['score']) == value for x in expected['chains']))
                else: self.assertIsNone(index.optimum)

    def test_exponential_path_population_without_enumeration(self):
        hs = [hit(trace='1', qs=i+1, ss=i+1, qlen=80, slen=80) for i in range(80)]
        index = ChainIndex(hs)
        self.assertEqual(index.count, 2**80-1)
        self.assertEqual(index.optimum['hits'], list(range(80)))
        for r in (0, 1, 123456789, index.count-1): self.assertEqual(index.rank(index.select(r)), r)
        self.assertLess(index.work, 200000)

    def test_reverse_axes_and_frames(self):
        hs = [hit(qs=12, qe=9, ss=12, se=9), hit(qs=8, qe=5, ss=8, se=5), hit(qs=4, qe=1, ss=4, se=1)]
        self.assertEqual(ChainIndex(hs, frame_modulus=3).count, 7)
        with self.assertRaises(ValueError): ChainIndex(hs+[hit()])
        with self.assertRaises(WorkLimit): ChainIndex(hs, cell_limit=1)
        with self.assertRaises(ValueError): ChainIndex(hs, frame_modulus=0)

    def test_score_ties_and_negative_scores(self):
        hs = [hit(trace='1', qs=1, ss=1), hit(trace='1', qs=2, ss=2)]
        self.assertEqual(ChainIndex(hs, scoring=(0,0,0,0)).optimum['count'], 3)
        self.assertEqual(ChainIndex(hs, scoring=(-1,0,0,0)).optimum['count'], 2)
        with self.assertRaises(ValueError): ChainIndex(hs).rank([1,0])


class SelectionTests(unittest.TestCase):
    def test_separator_and_native_against_independent_subsets(self):
        rng = random.Random(2701)
        for trial in range(12):
            hs = [hit(trace='2', qs=rng.randrange(1,9), ss=rng.randrange(1,9)) for _ in range(6)]
            valid = []
            for bits in product((0,1), repeat=len(hs)):
                if not any(bits): continue
                selected = sorted([h for h, b in zip(hs,bits) if b], key=lambda h: h.fields['qstart'])
                if all(a.fields['qend'] < b.fields['qstart'] and a.fields['send'] < b.fields['sstart'] for a,b in zip(selected,selected[1:])):
                    valid.append(list(bits))
            for backend in ('separator', 'native'):
                with HSPSelectionPopulation(hs, backend=backend) as population:
                    self.assertEqual(population.count, len(valid))
                    for r, bits in enumerate(valid):
                        self.assertEqual(population.select(r), bits)
                        self.assertEqual(population.rank(bits), r)
                    for v in range(len(hs)):
                        self.assertEqual(population.marginal(v), {b: sum(x[v]==b for x in valid) for b in (0,1)})
                    self.assertEqual(population.count_where({0:1}), sum(x[0] for x in valid))
                    self.assertIn(population.sample(seed=trial), valid)
                self.assertEqual(ChainIndex(hs).count, len(valid))

    def test_empty_carrier_and_empty_assignment(self):
        for backend in ('separator', 'native'):
            for nonempty in (False,True):
                with HSPSelectionPopulation([], backend=backend, nonempty=nonempty) as p:
                    self.assertEqual(p.count, int(not nonempty))
                    if p.count: self.assertEqual(p.select(0), [])
                    with self.assertRaises(ValueError): p.select(p.count)
        with HSPSelectionPopulation([hit()]) as p:
            with self.assertRaises(ValueError): p.rank([0])

    def test_opposite_strand_conflicts_and_budget(self):
        hs = [hit(qs=1,ss=1), hit(qs=5,ss=8,se=5)]
        self.assertEqual(selection_model(hs)['conflicts'], [[0,1]])
        with HSPSelectionPopulation(hs) as p: self.assertEqual(p.count, 2)
        with self.assertRaises(WorkLimit): HSPSelectionPopulation(hs, cell_limit=1)


class MotifTests(unittest.TestCase):
    def test_overlapping_union_and_occurrences_against_all_words(self):
        probabilities = {'A':Q(1,3),'C':Q(2,3)}
        for motifs in (['AA'], ['A','AA'], ['ACA','CA']):
            packet = motif_series(motifs, alphabet='AC', probabilities=probabilities)
            for n in range(7):
                anywhere = expected = Q(0)
                for letters in product('AC',repeat=n):
                    word = ''.join(letters); probability = Q(1)
                    for a in letters: probability *= probabilities[a]
                    occurrences = sum(word.startswith(m,i) for m in motifs for i in range(n-len(m)+1))
                    anywhere += probability*bool(occurrences); expected += probability*occurrences
                result = motif_values(packet,n)
                self.assertEqual(Q(result['hit_probability']), anywhere)
                self.assertEqual(Q(result['expected_occurrences']), expected)

    def test_source_binding_serialization_and_modular_coefficients(self):
        packet = motif_series(['AA'], alphabet='AC')
        serialized = json.loads(json.dumps(json_ready(packet)))
        self.assertEqual(motif_values(packet,20), motif_values(serialized,20))
        self.assertEqual(motif_values(packet,1000000,modulus=101)['modulus'],101)
        serialized['motifs'] = ['AC']
        with self.assertRaises(ValueError): motif_values(serialized,3)
        with self.assertRaises(ValueError): motif_values(packet,3,modulus=2)
        with self.assertRaises(ValueError): motif_series(['A'],alphabet='AC',probabilities={'A':0.5,'C':0.5})
        with self.assertRaises(ValueError): motif_series(['A'],alphabet='AC',probabilities={'A':1,'C':1})

    def test_long_probability_series_against_direct_prefix_dp(self):
        packet = motif_series(['ACG','CGT'])
        result = motif_values(packet,483)
        # Independent prefix DP over all proper prefixes, removing trajectories
        # at the first occurrence; no production automaton/resolvent helpers.
        states = {'':Q(1)}; prefixes = ('','A','AC','C','CG')
        for _ in range(483):
            nxt = {}
            for prefix, mass in states.items():
                for a in 'ACGT':
                    word = prefix+a
                    if word.endswith('ACG') or word.endswith('CGT'): continue
                    target = max((p for p in prefixes if word.endswith(p)),key=len)
                    nxt[target] = nxt.get(target,Q(0))+mass/4
            states = nxt
        self.assertEqual(Q(result['hit_probability']),1-sum(states.values()))
        self.assertEqual(Q(result['expected_occurrences']),Q(2*(483-2),64))


class MiningTests(unittest.TestCase):
    def test_flow_capacity_assignment_against_all_assignments(self):
        hs = [hit(q='q1',s='s1'),hit(q='q1',s='s2'),hit(q='q2',s='s1'),hit(q='q3',s='s1')]
        for capacity in (0,1,2,3):
            result = capacity_assignment(hs,{'s1':capacity,'s2':1},query_ids=['q1','q2','q3','q4'])
            best = 0
            for choices in product((None,'s1','s2'),repeat=4):
                if any(s is not None and not any(h.fields['qseqid']==q and h.fields['sseqid']==s for h in hs) for q,s in zip(result['queries'],choices)): continue
                if choices.count('s1') <= capacity and choices.count('s2') <= 1:
                    best = max(best,sum(s is not None for s in choices))
            self.assertEqual(result['certificate']['value'],best)
            self.assertEqual(len(result['assignment']),best)

    def test_hall_witness_preserves_queries_without_hits(self):
        result = assignment_diagnosis([hit(q='q1',s='s'),hit(q='q2',s='s')], query_ids=['q1','q2','q3'],subject_ids=['s'])
        certificate = result['certificate']
        self.assertEqual(len(certificate['matching']),1)
        self.assertGreater(len(certificate['hall_left']),len(certificate['hall_neighbors']))
        self.assertIn('q3',result['queries'])

    def test_triangle_filling_removes_graph_cycle(self):
        triangle = [(0,1,Q(1),1),(1,2,Q(1),1),(0,2,Q(1),1)]
        row = similarity_topology(4,triangle)['snapshots'][0]
        self.assertEqual(row['homology']['betti'],[2,0,0])
        square = [(0,1,1,1),(1,2,1,1),(2,3,1,1),(0,3,1,1)]
        self.assertEqual(similarity_topology(4,square)['snapshots'][0]['homology']['betti'],[1,1,0])
        tetra = [(a,b,1,1) for a in range(4) for b in range(a+1,4)]
        self.assertEqual(similarity_topology(4,tetra)['snapshots'][0]['homology']['betti'],[1,0,1])
        with self.assertRaises(WorkLimit): similarity_topology(4,triangle,face_limit=0)

    def test_real_retained_blast_and_explicit_budget_status(self):
        root = Path(__file__).resolve().parents[2]
        records = fasta((root/'examples/blast/NM_000207.3.fasta').read_text())
        subjects = fasta((root/'examples/blast/XM_043971863.1.fasta').read_text())
        hits = tabular((root/'examples/blast/insulin_blast.tsv').read_text())
        result = mine(hits,records,subjects,motifs=['ACG'])
        self.assertEqual(len(result['tracebacks']),17)
        self.assertTrue(all(x['source_replayed'] for x in result['tracebacks']))
        self.assertTrue(verify_mining(result,hits,records,subjects))
        saved = json.loads(json.dumps(json_ready(result)))
        self.assertTrue(verify_mining(saved,hits,records,subjects))
        saved['retained_hit_indices'] = []
        with self.assertRaises(ValueError): verify_mining(saved,hits,records,subjects)
        result2 = mine(hits,records,subjects,cell_limit=1)
        self.assertTrue(any(x.get('status')=='WORK_LIMIT' for x in result2['selections']))
        damaged = {k:'A'*len(v) for k,v in records.items()}
        with self.assertRaises(ValueError): mine(hits,damaged,subjects)
        short = {k:v[:-1] for k,v in records.items()}
        with self.assertRaises(ValueError): mine(hits,short,subjects)

    def test_cli_mine_and_motif(self):
        from perfectpower.blast_cli import main
        root = Path(__file__).resolve().parents[2]
        with tempfile.TemporaryDirectory() as tmp:
            output = str(Path(tmp)/'mine.json')
            main(['mine',str(root/'examples/blast/insulin_blast.tsv'),'--query-fasta',str(root/'examples/blast/NM_000207.3.fasta'),
                  '--subject-fasta',str(root/'examples/blast/XM_043971863.1.fasta'),'--output',output])
            self.assertEqual(json.loads(Path(output).read_text())['schema'],'pp-blast-mining/2')
            main(['motif','AA','--alphabet','AC','--length','3','--output',output])
            self.assertEqual(Q(json.loads(Path(output).read_text())['values']['hit_probability']),Q(3,8))

    def test_offline_report_large_counts_and_escaping(self):
        from perfectpower.blast_mining_report import write_mining_report
        hs = [hit(q='</script><script>alert(1)</script>',s='s')]
        # Identifiers cannot contain whitespace; all residues are replayable.
        result = mine(hs,{hs[0].fields['qseqid']:'A'*12},{'s':'A'*12})
        result['selections'][0]['population']['count'] = 2**80-1
        with tempfile.TemporaryDirectory() as tmp:
            output = str(Path(tmp)/'report.html');write_mining_report(result,output)
            html = Path(output).read_text()
            self.assertNotIn('</script><script>alert(1)',html)
            self.assertIn('"count": "1208925819614629174706175"',html)
            self.assertIn('"count": 1208925819614629174706175',html)
            result['scope'] = '__RAW_RECEIPT__'
            write_mining_report(result,output)
            html = Path(output).read_text()
            import re
            raw = re.search('<script id="rawReceipt" type="application/json">(.*?)</script>',html,re.S).group(1)
            self.assertEqual(json.loads(raw)['scope'],'__RAW_RECEIPT__')


if __name__ == '__main__': unittest.main()
