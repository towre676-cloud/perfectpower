import unittest
from collections import Counter
from fractions import Fraction
from itertools import combinations
from perfectpower.blast_io import BlastHit, FIELDS, replay
from perfectpower.blast_mining import ChainIndex
from perfectpower.blast_benchmark import aligned_fasta, evaluate, residue_pairs, union_coverage, coverage_chain, load_dataset, stream_hits


def hsp(qstart,qend,sstart,send,trace=None,query='q',subject='s',qlen=8,slen=8,bits='20'):
    length=qend-qstart+1
    return BlastHit(dict(zip(FIELDS, [query,subject,'100',str(length),'0','0',str(qstart),str(qend),str(sstart),str(send),'1e-9',bits,trace or str(length),str(qlen),str(slen),'0'])))

class BenchmarkTests(unittest.TestCase):
    def test_chaining_improves_coverage_without_label_access(self):
        hits=[hsp(1,2,1,2),hsp(5,6,5,6)]
        records={'q':'AAAAAAAA','s':'AAAAAAAA'}
        refs={k:{i:i for i in range(1,9)} for k in records}
        result=evaluate(records,{'F':['q','s']},refs,hits)
        self.assertEqual(result['directed_positive_pairs'],2)
        self.assertEqual(result['totals']['any_hsp']['retrieved_pairs'],0)
        self.assertEqual(result['totals']['exact_chain']['retrieved_pairs'],1)
        self.assertEqual(result['totals']['exact_chain']['pair_recall'],0.5)
        self.assertEqual(result['reference_residue_pairs'],16)

    def test_crossing_union_is_not_coherent_chain(self):
        hits=[hsp(1,2,5,6),hsp(5,6,1,2)]
        records={'q':'AAAAAAAA','s':'AAAAAAAA'};refs={k:{i:i for i in range(1,9)} for k in records}
        result=evaluate(records,{'F':['q','s']},refs,hits)
        self.assertEqual(result['totals']['hsp_union']['retrieved_pairs'],1)
        self.assertEqual(result['totals']['exact_chain']['retrieved_pairs'],0)
        self.assertEqual(result['totals']['hsp_union']['correct_reference_residue_pairs'],0)

    def test_no_hits_in_denominator(self):
        result=evaluate({'q':'AAAA','s':'AAAA'},{'F':['q','s']},{'q':{1:1},'s':{1:1}},[])
        self.assertEqual(result['directed_positive_pairs'],2)
        self.assertEqual(result['totals']['exact_chain']['pair_recall'],0)

    def test_limit_is_unknown_not_zero(self):
        records={'q':'AAAAAAAA','s':'AAAAAAAA'};refs={k:{i:i for i in range(1,9)} for k in records}
        result=evaluate(records,{'F':['q','s']},refs,[hsp(1,2,1,2),hsp(5,6,5,6)],cell_limit=1)
        row=result['pairs'][0]
        self.assertIsNone(row['chain_count']);self.assertIsNone(row['methods']['exact_chain']['retrieved'])
        self.assertEqual(result['chain_work_limits'],1)

    def test_source_mutation_rejected(self):
        with self.assertRaises(ValueError):replay(hsp(1,2,1,2),'AAAAAAAA','CAAAAAAA',nucleotide=False)

    def test_declared_length_mutation_rejected(self):
        with self.assertRaises(ValueError):evaluate({'q':'AAAA','s':'AAAA'},{'F':['q','s']},{'q':{},'s':{}},[hsp(1,2,1,2)])

    def test_uppercase_annotation_only(self):
        self.assertEqual(aligned_fasta(b'>a\nACd.\n>b\nAC.e\n'),{'a':'ACd.','b':'AC.e'})
        with self.assertRaises(ValueError):aligned_fasta(b'>a\nA\n>b\nAA\n')
        with self.assertRaises(ValueError):aligned_fasta(b'>a\nA\n>a\nA\n')

    def test_reference_misalignment_not_counted(self):
        result=evaluate({'q':'AAAA','s':'AAAA'},{'F':['q','s']},{'q':{1:0,2:1},'s':{1:1,2:0}},[hsp(1,2,1,2,qlen=4,slen=4)])
        self.assertEqual(result['totals']['best_hsp']['eligible_residue_precision'],0)

    def test_independent_exhaustive_subsets(self):
        # Coverage and every polynomial coefficient, not just total counts.
        for n in range(1,9):
            hits=[hsp(2*i+1,2*i+1,2*i+1,2*i+1,qlen=20,slen=20) for i in range(n)]
            index=ChainIndex(hits)
            brute=Counter()
            for k in range(1,n+1):
                for subset in combinations(range(n),k):brute[k,k]+=1
            got=Counter()
            for terms in index.suffix.values():got.update(terms)
            self.assertEqual(got,brute)
            self.assertEqual(coverage_chain(index)[0],n)
            for rank in range(index.count):self.assertEqual(index.rank(index.select(rank)),rank)

    def test_union_deduplicates_overlap(self):
        self.assertEqual(union_coverage([hsp(1,3,1,3),hsp(2,4,2,4)]),4)
        self.assertEqual(residue_pairs(hsp(1,3,1,3)),{(1,1),(2,2),(3,3)})

    def test_stream_resource_limits(self):
        import tempfile,gzip
        from pathlib import Path
        from perfectpower.divisor_square import WorkLimit
        with tempfile.TemporaryDirectory() as d:
            path=Path(d)/'hits.gz'
            row='\t'.join(str(hsp(1,2,1,2).fields[k]) for k in FIELDS)+'\n'
            path.write_bytes(gzip.compress((row*2).encode()))
            self.assertEqual(len(list(stream_hits(path))),2)
            with self.assertRaises(WorkLimit):list(stream_hits(path,row_limit=1))
            with self.assertRaises(WorkLimit):list(stream_hits(path,byte_limit=1))

    def test_pinned_full_inventory(self):
        from pathlib import Path
        root=Path(__file__).resolve().parents[2]
        manifest,records,groups,refs,mapping=load_dataset(root/'data/oxbench')
        self.assertEqual(len(groups),395);self.assertEqual(len(records),3292)
        self.assertEqual(sum(len(v)*(len(v)-1) for v in groups.values()),101750)
        self.assertEqual(len(mapping),len(records))

    def test_bounded_uncompressed_digest(self):
        import tempfile,lzma
        from hashlib import sha256
        from pathlib import Path
        from benchmark_blast_oxbench import uncompressed_digest
        from perfectpower.divisor_square import WorkLimit
        with tempfile.TemporaryDirectory() as d:
            path=Path(d)/'hits.tsv.xz';raw=b'row\n'*300000
            path.write_bytes(lzma.compress(raw))
            self.assertEqual(uncompressed_digest(path),sha256(raw).hexdigest())
            with self.assertRaises(WorkLimit):uncompressed_digest(path,byte_limit=len(raw)-1)

if __name__=='__main__':unittest.main()
