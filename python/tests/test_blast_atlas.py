"""Independent enumerations and adversarial checks for the BLAST exploration layer."""
import unittest
from collections import Counter
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import tempfile
import json
from perfectpower.blast_alignment import AlignmentFamily, exact_alignment, weights, score
from perfectpower.blast_parameters import line_atlas, plane_atlas, robustness, integer_grid
from perfectpower.blast_io import fasta, tabular, BlastHit, btop_features, replay, FIELDS
from perfectpower.blast_chains import chain_population, distinguishing_features
from perfectpower.blast_explore import identity_correlation, query_family, similarity_edges, graph_filtration
from perfectpower.blast_machinery import partition_statistics, sensitivity_jet, fixed_alignment_null, alignment_machine, motif_machine, soe_packet, motif_count_machine, similarity_geometry, feature_diagnostic
from perfectpower.blast_client import NCBIClient
from perfectpower.blast_report import write_report
from perfectpower.divisor_square import WorkLimit


def exhaustive(q, s):
    """Independent recursive string alignment enumeration, no production helpers."""
    rows = []
    def visit(i, j, operations, first, second):
        if i == len(q) and j == len(s):
            matches = sum(a == b and a != '-' for a, b in zip(first, second))
            mismatches = sum(a != b and a != '-' and b != '-' for a, b in zip(first, second))
            gaps = sum(a == '-' or b == '-' for a, b in zip(first, second))
            openings = sum(op in 'DI' and (k == 0 or operations[k-1] != op) for k, op in enumerate(operations))
            rows.append((operations, (matches, mismatches, openings, gaps)))
            return
        if i < len(q) and j < len(s):
            visit(i+1, j+1, operations+'M', first+q[i], second+s[j])
        if i < len(q) and (not operations or operations[-1] != 'I'):
            visit(i+1, j, operations+'D', first+q[i], second+'-')
        if j < len(s) and (not operations or operations[-1] != 'D'):
            visit(i, j+1, operations+'I', first+'-', second+s[j])
    visit(0, 0, '', '', '')
    return rows


def hit(q='q', s='s', trace='4', qs=1, ss=1, qe=None, se=None, qlen=12, slen=12):
    info = btop_features(trace); m, u, o, l = info['features']
    f = dict(zip(FIELDS, (q, s, str(round(100*m/info['length'], 3)), info['length'], u, o,
                            qs, qe or qs+info['query_span']-1, ss, se or ss+info['subject_span']-1,
                            '1e-20', '50', trace, qlen, slen, '9606')))
    return BlastHit(f)


class AlignmentTests(unittest.TestCase):
    def test_complete_populations_against_independent_enumerator(self):
        strings = ['', 'A', 'C', 'AA', 'AC', 'CA', 'AAC', 'ACA']
        for q, s in product(strings, repeat=2):
            with self.subTest(q=q, s=s):
                expected = exhaustive(q, s)
                family = AlignmentFamily(q, s)
                self.assertEqual(family.terms, Counter(f for _, f in expected))
                grouped = {}
                for operations, f in expected:
                    grouped.setdefault(f, []).append(operations)
                for f, operations in grouped.items():
                    for index, path in enumerate(operations):
                        self.assertEqual(family.select(f, index)['operations'], path)
                        self.assertEqual(family.rank(path), index)
                for w in (weights(), weights(1, 0, 0, 0), weights(3, 2, 1, 2)):
                    optimum = max(score(f, w) for _, f in expected)
                    self.assertEqual(Q(family.optimal(w)['score']), optimum)
                    self.assertEqual(Q(exact_alignment(q, s, w, local=False)['score']), optimum)

    def test_local_score_against_all_substrings(self):
        for q, s in [('ACGT', 'CGTA'), ('AAAA', 'CCAA'), ('ACA', 'CAC'), ('A', 'C')]:
            w = weights(2, 3, 2, 1)
            best = Q(0)
            for a in range(len(q)):
                for b in range(a+1, len(q)+1):
                    for c in range(len(s)):
                        for d in range(c+1, len(s)+1):
                            best = max(best, *(score(f, w) for _, f in exhaustive(q[a:b], s[c:d])))
            self.assertEqual(Q(exact_alignment(q, s, w)['score']), best)

    def test_substitution_table_and_model_errors(self):
        result = exact_alignment('AC', 'AC', substitution={'AA':4,'AC':-5,'CA':-5,'CC':7})
        self.assertEqual(result['score'], '11')
        with self.assertRaises(ValueError): exact_alignment('AC', 'AC', substitution={'AA':4})
        with self.assertRaises(ValueError): exact_alignment('A', 'A', weights(2,3,0,0))
        with self.assertRaises(ValueError): AlignmentFamily('A-', 'A')
        with self.assertRaises(WorkLimit): AlignmentFamily('AAA', 'AAA', work_limit=1)
        with self.assertRaises(WorkLimit): exact_alignment('AAA', 'AAA', cell_limit=1)
        with self.assertRaises(ValueError): AlignmentFamily('A','A').select((1,0,0,0), 1)

    def test_psg_partition_moments_and_jets(self):
        family = AlignmentFamily('ACGT', 'CGTA')
        stats = partition_statistics(family)
        for i in range(4):
            self.assertEqual(Q(stats['means'][i]), Q(sum(f[i]*c for f,c in family.terms.items()), family.count))
        jet = sensitivity_jet(family, (1,1,1,1), (1,0,0,0), 4)
        poly = family.polynomial()
        self.assertEqual(Q(jet['coefficients'][0]), family.count)
        self.assertEqual(Q(jet['coefficients'][1]), poly.derivative('matches').evaluate((1,1,1,1)))
        self.assertEqual(Q(fixed_alignment_null(4,4)['tail_probability']), Q(1,256))


class ParameterTests(unittest.TestCase):
    def setUp(self): self.family = AlignmentFamily('ACGTACGT', 'CGTACGTA')

    def test_line_envelope_exact_and_ties(self):
        atlas = line_atlas(self.family.terms, (2,-3,0,-1), (0,0,-1,0), (0,30))
        for t in [Q(i,2) for i in range(61)]:
            w = (2,-3,-t,-1); best = max(score(f,w) for f in self.family.terms)
            expected = {f for f in self.family.terms if score(f,w)==best}
            actual = {tuple(r['feature']) for r in atlas['regions'] if Q(r['interval'][0])<=t<=Q(r['interval'][1])}
            self.assertEqual(actual, expected)
        degenerate = line_atlas([(1,0,0,0),(0,1,0,0)], (0,0,0,0), (1,0,0,0), (-1,1))
        self.assertEqual(len(degenerate['regions']), 2)

    def test_plane_vertices_and_area(self):
        atlas = plane_atlas(self.family.terms, (2,0,0,-1), [(0,-1,0,0),(0,0,-1,0)], [(0,8),(0,12)])
        self.assertEqual(sum(Q(r['area']) for r in atlas['regions']), 96)
        for region in atlas['regions']:
            f = tuple(region['feature'])
            for x,y in region['vertices']:
                w=(2,-Q(x),-Q(y),-1)
                self.assertTrue(all(score(f,w)>=score(g,w) for g in self.family.terms))
        tied=plane_atlas([(1,0,0,0),(0,1,0,0),(0,0,1,0)], (0,0,0,0), [(1,0,0,0),(0,1,0,0)], [(-1,1),(-1,1)])
        self.assertEqual(len(tied['regions']),3)

    def test_robust_radius_and_grid(self):
        r = robustness([(1,0,0,0),(0,1,0,0)], (3,1,0,0))
        self.assertEqual(r['winners'][0]['linfinity_radius'], '1')
        rows = integer_grid(self.family.terms, [(2,2),(-3,-1),(-2,0),(-1,-1)], residue_filters=[(2,2,[0])])
        self.assertEqual(rows['count'],6)
        query = query_family(self.family, min_matches=7, max_gap_openings=2, residues=[(3,2,[0])])
        self.assertEqual(query['alignment_count'], 1)


class InputTests(unittest.TestCase):
    def test_btop_and_source_replay(self):
        h=hit(trace='2G-3',qlen=6,slen=5)
        self.assertEqual(h.features,(5,0,1,1))
        self.assertEqual(replay(h,'ACGTCG','ACTCG')['query'],'ACGTCG')
        with self.assertRaises(ValueError): replay(h,'ACATCG','ACTCG')
        self.assertEqual(btop_features('1-A-C1')['features'],[2,0,1,2])
        self.assertEqual(btop_features('1-A0-C1')['features'],[2,0,1,2])
        for invalid in ['AA','--','1A','1?C','1 A-']:
            with self.assertRaises(ValueError): btop_features(invalid)

    def test_reverse_complement_replay(self):
        h=hit(trace='4',qs=1,ss=4,se=1,qlen=4,slen=4)
        self.assertEqual(h.strand,-1)
        self.assertTrue(replay(h,'ACGT','ACGT')['source_replayed'])
        with self.assertRaises(ValueError): replay(h,'ACGT','ACGT',nucleotide=False)

    def test_header_and_invalid_fields(self):
        h=hit(); columns='\t'.join(str(h.fields[k]) for k in FIELDS)
        self.assertEqual(len(tabular(columns)),1)
        for key,value in [('length',5),('qend',99),('evalue','NaN'),('pident','90.0')]:
            changed=dict(h.fields);changed[key]=value
            with self.assertRaises(ValueError): BlastHit(changed)
        with self.assertRaises(ValueError): fasta('ACGT')
        with self.assertRaises(ValueError): fasta('>a\nA\n>a\nC')
        self.assertEqual(fasta('>a title\nac\ngt\n'),{'a':'ACGT'})

    def test_correlations_against_direct_offsets(self):
        for q,s in [('ACGT','CG'),('ACA','ACA'),('A','TT')]:
            for row in identity_correlation(q,s)['rows']:
                offset=row['offset']
                expected=sum(q[j+offset]==s[j] for j in range(len(s)) if 0<=j+offset<len(q))
                self.assertEqual(row['matches'],expected)

    def test_client_cache_and_pacing(self):
        clock=[100.0];calls=[]
        def transport(url,data=None):
            calls.append((url,data))
            return '>NM_000207.3\nACGT\n' if 'efetch' in url else 'RID = ABC123\n'
        with tempfile.TemporaryDirectory() as directory:
            client=NCBIClient(directory,email='test@example.org',transport=transport,clock=lambda:clock[0])
            first=client.fetch_sequences(['NM_000207.3']);second=client.fetch_sequences(['NM_000207.3'])
            self.assertFalse(first['cache_hit']);self.assertTrue(second['cache_hit']);self.assertEqual(len(calls),1)
            self.assertEqual(client.submit('>q\nACGT')['rid'],'ABC123')
            with self.assertRaises(WorkLimit): client.retrieve('ABC123')
            clock[0]+=10;client.retrieve('ABC123')
            clock[0]+=10
            with self.assertRaises(WorkLimit): client.retrieve('ABC123')


class MachineryTests(unittest.TestCase):
    def test_chain_population_complete_and_reverse(self):
        hits=[hit(qs=1,ss=1),hit(qs=5,ss=5),hit(qs=9,ss=9)]
        self.assertEqual(chain_population(hits,weights())['count'],7)
        self.assertEqual(chain_population(hits,weights(),min_coverage=12)['count'],1)
        reverse=[hit(qs=1,ss=12,se=9),hit(qs=5,ss=8,se=5)]
        self.assertEqual(chain_population(reverse,weights())['count'],3)
        with self.assertRaises(WorkLimit): chain_population(hits,weights(),work_limit=1)

    def test_soe_and_linear_motif_counts(self):
        model,states=alignment_machine('AC','AG');packet=soe_packet(model,compile_lean=True)
        self.assertLess(packet['class_count'],packet['state_count'])
        self.assertIn('quotient_complete',packet['lean_compilation']['lean'])
        from perfectpower.observable_machine import power_outputs
        receipt=motif_count_machine(['AC','CG'])
        for n in range(5):
            expected=sum(any(''.join(w).endswith(m) for m in ('AC','CG')) for w in product('ACGT',repeat=n))
            self.assertEqual(power_outputs(receipt['machine'],n)[0],expected)

    def test_hodge_and_strand_cycles(self):
        edges=[(0,1,1,1),(1,2,1,1),(0,2,1,-1)]
        filled=similarity_geometry(3,edges)
        graph=similarity_geometry(3,edges,fill_triangles=False)
        self.assertEqual(filled['hodge']['dimensions'],(2,1,0))
        self.assertEqual(graph['hodge']['dimensions'],(2,0,1))
        self.assertFalse(filled['strand_transport']['components'][0]['balanced'])
        levels=graph_filtration(3,edges)['levels']
        self.assertEqual(len(levels),1);self.assertEqual(levels[0]['graph_cycle_rank'],1)

    def test_network_reciprocity_and_policy(self):
        hits=[hit('a','b',qlen=4,slen=4),hit('b','a',qlen=4,slen=4)]
        self.assertEqual(len(similarity_edges(hits)['edges']),1)
        self.assertEqual(similarity_edges(hits[:1])['edges'],[])
        hypotheses={'a':[1,0,1,1],'b':[1,1,0,0],'c':[2,0,0,1]}
        own=distinguishing_features(hypotheses)
        existing=feature_diagnostic(hypotheses)
        self.assertEqual(Q(own['worst_case_cost']),existing['worst_case_cost'])


class ProductModelTests(unittest.TestCase):
    def test_motif_constraints_against_independent_alignment_scan(self):
        from perfectpower.blast_motif_alignment import MotifAlignmentFamily
        for q,s,motifs in [('ACGT','ACGT',['CG']),('ACAC','ACAC',['AC','CA']),('AC','CA',['AC'])]:
            expected=Counter()
            base=AlignmentFamily(q,s)
            for operations,f in exhaustive(q,s):
                rendered=base.render(operations)
                runs=[];current=''
                for a,b in zip(rendered['query'],rendered['subject']):
                    if a==b and a!='-':current+=a
                    else:
                        runs.append(current);current=''
                runs.append(current)
                if all(any(m in run for run in runs) for m in motifs):expected[f]+=1
            constrained=MotifAlignmentFamily(q,s,motifs)
            self.assertEqual(constrained.terms,expected)
            for f,c in constrained.terms.items():
                self.assertEqual(constrained.select(f,c-1)['features'],list(f))

    def test_three_transport_semirings_agree(self):
        from perfectpower.blast_machinery import semiring_alignment
        for q,s in [('AC','AG'),('ACG','CG'),('','A'),('','')]:
            family=AlignmentFamily(q,s)
            result=semiring_alignment(q,s,activities=(2,1,1,1))
            self.assertEqual(result['count'],family.count)
            self.assertEqual(Q(result['partition_mass']),family.polynomial().evaluate((2,1,1,1)))
            self.assertEqual(-Q(result['minimum_negative_score']),Q(family.optimal(weights())['score']))

    def test_full_weight_normal_region_descriptions(self):
        from perfectpower.blast_parameters import normal_regions
        family=AlignmentFamily('AC','CA');regions=normal_regions(family.terms)
        for w in product((-1,0,1),repeat=4):
            actual={tuple(r['feature']) for r in regions['regions'] if all(score(c,w)>=0 for c in r['inequalities'])}
            best=max(score(f,w) for f in family.terms)
            self.assertEqual(actual,{f for f in family.terms if score(f,w)==best})

    def test_retained_real_blast_tracebacks(self):
        root=Path(__file__).resolve().parents[2]
        hits=tabular((root/'examples/blast/insulin_blast.tsv').read_text())
        q=fasta((root/'examples/blast/NM_000207.3.fasta').read_text())
        s=fasta((root/'examples/blast/XM_043971863.1.fasta').read_text())
        self.assertEqual(len(hits),17)
        for h in hits:self.assertTrue(replay(h,q[h.fields['qseqid']],s[h.fields['sseqid']])['source_replayed'])
        self.assertEqual(score(hits[0].features,weights(2,3,5,2)),174)

    def test_offline_report_and_script_injection_encoding(self):
        from perfectpower.blast_parameters import plane_atlas
        family=AlignmentFamily('AC','CA')
        receipt={'family':family.packet(),'plane':plane_atlas(family.terms,(2,0,0,-1),[(0,-1,0,0),(0,0,-1,0)],[(0,8),(0,12)]),'example_label':'</script><script>alert(1)</script>'}
        with tempfile.TemporaryDirectory() as d:
            path=Path(d)/'atlas.html';write_report(receipt,path)
            text=path.read_text()
            self.assertNotIn('__ATLAS_DATA__',text)
            self.assertNotIn('</script><script>alert(1)</script>',text)
            self.assertIn('\\u003c/script',text)


if __name__=='__main__': unittest.main()
