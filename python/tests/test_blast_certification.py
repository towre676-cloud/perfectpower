import copy
from hashlib import sha256
import json
from pathlib import Path
import tempfile
import unittest
import subprocess
import sys
from perfectpower.blast_annotation import genbank, load_corpus, project, coding_audit
from perfectpower.blast_certification import independent_trace, certify
from perfectpower.blast_io import BlastHit
from perfectpower.blast_recall import recall_audit
from unittest.mock import patch
from perfectpower.divisor_square import WorkLimit

ROOT=Path(__file__).resolve().parents[2]


def record_xml(accession='NM_1.1'):
    return f'''<GBSet><GBSeq><GBSeq_accession-version>{accession}</GBSeq_accession-version>
      <GBSeq_length>6</GBSeq_length><GBSeq_sequence>acgtac</GBSeq_sequence>
      <GBSeq_organism>fixture</GBSeq_organism><future-field>retained</future-field>
      <GBSeq_feature-table><GBFeature><GBFeature_key>CDS</GBFeature_key>
      <GBFeature_location>join(1..3,3..5)</GBFeature_location><GBFeature_intervals>
      <GBInterval><GBInterval_from>1</GBInterval_from><GBInterval_to>3</GBInterval_to></GBInterval>
      <GBInterval><GBInterval_from>3</GBInterval_from><GBInterval_to>5</GBInterval_to>
      <GBInterval_iscomp value="true"/></GBInterval></GBFeature_intervals><GBFeature_quals>
      <GBQualifier><GBQualifier_name>note</GBQualifier_name><GBQualifier_value>one</GBQualifier_value></GBQualifier>
      <GBQualifier><GBQualifier_name>note</GBQualifier_name><GBQualifier_value>two</GBQualifier_value></GBQualifier>
      </GBFeature_quals></GBFeature></GBSeq_feature-table></GBSeq></GBSet>'''.encode()


def simple_hit(**changes):
    fields=dict(qseqid='q',sseqid='s',pident='100',length=4,mismatch=0,gapopen=0,
                qstart=1,qend=4,sstart=1,send=4,evalue='0',bitscore='1',btop='4',qlen=4,slen=4)
    fields.update(changes)
    return BlastHit(fields)


class AnnotationTests(unittest.TestCase):
    def test_coding_translation_unknown_and_discrepancy(self):
        record={'sequence':'ATGGCTTAA','features':[{'key':'CDS','location':'1..9',
              'intervals':[{'status':'local','start':0,'end':9,'strand':1}],
              'qualifiers':[{'name':'translation','value':'MA'}]}]}
        self.assertEqual(coding_audit(record)[0]['status'],'literal_translation_agrees')
        record['features'][0]['qualifiers'][0]['value']='MB'
        self.assertEqual(coding_audit(record)[0]['status'],'translation_discrepancy')
        record['sequence']='ATGNCCTAA'
        self.assertEqual(coding_audit(record)[0]['status'],'ambiguous_coding_letters')
        record['features'][0]['qualifiers'].append({'name':'transl_table','value':'2'})
        self.assertEqual(coding_audit(record)[0]['status'],'unsupported_translation_table_or_exception')
    def test_lossless_xml_and_repeated_qualifiers(self):
        r=genbank(record_xml())['NM_1.1']
        self.assertIn('future-field',json.dumps(r['source']))
        self.assertEqual([q['value'] for q in r['features'][0]['qualifiers']],['one','two'])
        self.assertEqual(r['features'][0]['intervals'][1]['strand'],-1)

    def test_overlap_union_counts_no_double_bases(self):
        r=genbank(record_xml())['NM_1.1'];p=project(r,2,5)[0]
        self.assertEqual(p['overlap_bases'],4);self.assertEqual(p['overlap_intervals'],[[1,5]])
        self.assertEqual(project(r,5,2),project(r,2,5))
        with self.assertRaises(ValueError):project(r,0,5)

    def test_remote_features_remain_explicitly_unresolved(self):
        raw=record_xml().replace(b'<GBInterval_from>1',b'<GBInterval_accession>OTHER.1</GBInterval_accession><GBInterval_from>1')
        r=genbank(raw)['NM_1.1'];p=project(r,1,2)[0]
        self.assertFalse(p['projection_complete']);self.assertEqual(p['overlap_bases'],0)

    def test_malformed_and_duplicate_records_fail(self):
        for raw in [record_xml().replace(b'<GBSeq_length>6',b'<GBSeq_length>7'),
                    record_xml().replace(b'</GBSet>',record_xml().split(b'<GBSet>')[1]),
                    record_xml().replace(b'<GBInterval_to>5',b'<GBInterval_to>7')]:
            with self.assertRaises(ValueError):genbank(raw)

    def test_complete_pinned_corpus_and_tamper(self):
        manifest,records=load_corpus(ROOT/'data/blast_corpus')
        self.assertEqual(len(records),930);self.assertEqual(sum(r['length'] for r in records.values()),628656)
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp);raw=record_xml();(p/'record.xml').write_bytes(raw)
            m={'accessions':['NM_1.1'],'record_count':1,'sources':[{'file':'record.xml','sha256':sha256(raw).hexdigest()}]}
            (p/'manifest.json').write_text(json.dumps(m));self.assertEqual(len(load_corpus(p)[1]),1)
            (p/'record.xml').write_bytes(raw+b' ')
            with self.assertRaisesRegex(ValueError,'hash'):load_corpus(p)
            (p/'record.xml').write_bytes(raw);m['accessions'].append('NM_2.1');m['record_count']=2
            (p/'manifest.json').write_text(json.dumps(m))
            with self.assertRaisesRegex(ValueError,'incomplete'):load_corpus(p)


class AdapterTests(unittest.TestCase):
    def test_kernel_encoding_rejects_source_and_coordinate_tamper(self):
        import generate_blast_source_certificates as generator
        import gzip
        from perfectpower.blast_io import FIELDS
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);(root/'examples/blast').mkdir(parents=True);(root/'data/blast_corpus').mkdir(parents=True)
            (root/'receipts/blast/certification').mkdir(parents=True)
            (root/'examples/blast/insulin_family.fasta').write_text('>q\nACGT\n')
            (root/'data/blast_corpus/database.fasta').write_text('>s\nACGT\n')
            hit=simple_hit();raw=('\t'.join(str(hit.fields.get(k,'0')) for k in FIELDS)+'\n').encode()
            (root/'data/blast_corpus/blast_word28.tsv.gz').write_bytes(gzip.compress(raw))
            with patch.object(generator,'ROOT',root):
                manifest=generator.generate();self.assertTrue(generator.validate_encoding(manifest))
                source=root/manifest['modules'][0];text=source.read_text();source.write_text(text.replace('ACGT','ACGA',1))
                with self.assertRaisesRegex(ValueError,'sequence'):generator.validate_encoding(manifest)
                source.write_text(text)
                module=root/manifest['modules'][1];module.write_text(module.read_text().replace(', 1, 4,',', 2, 4,',1))
                with self.assertRaisesRegex(ValueError,'omit or alter'):generator.validate_encoding(manifest)
    def test_cli_compressed_source_and_alias_protection(self):
        with tempfile.TemporaryDirectory() as tmp:
            output=Path(tmp)/'audit.json'
            args=[sys.executable,'-m','perfectpower.blast_cli','certify-source',str(ROOT/'data/blast_corpus/blast_word28.tsv.gz'),
                  '--query-fasta',str(ROOT/'examples/blast/insulin_family.fasta'),
                  '--subject-fasta',str(ROOT/'data/blast_corpus/database.fasta'),'--output',str(output)]
            subprocess.run(args,check=True,capture_output=True)
            self.assertEqual(len(json.loads(output.read_text())['hits']),624)
            args[-1]=str(ROOT/'examples/blast/insulin_family.fasta')
            result=subprocess.run(args,capture_output=True,text=True)
            self.assertNotEqual(result.returncode,0);self.assertIn('differ',result.stderr)
    def test_zero_run_and_affine_openings(self):
        self.assertEqual(independent_trace('2A-0C-1','ACACG','ACG'),{'features':[3,0,1,2],'length':5})
        self.assertEqual(independent_trace('1AT1','AAC','ATC')['features'],[2,1,0,0])

    def test_mutated_source_and_grammar_rejected(self):
        for trace,q,s in [('4','ACGT','ACGA'),('1A','AA','AA'),('AA','A','A'),('--','',''),('4','ACG','ACG'),('1','AA','A')]:
            with self.assertRaises(ValueError):independent_trace(trace,q,s)

    def test_full_byte_binding_and_budget(self):
        from perfectpower.blast_io import FIELDS
        h=simple_hit();raw=('\t'.join(str(h.fields[k]) for k in FIELDS)+'\n').encode() if 'staxids' in h.fields else (
             '\t'.join(str(h.fields.get(k,'0')) for k in FIELDS)+'\n').encode()
        q=b'>q\nACGT\n';s=b'>s\nACGT\n';audit=certify(q,s,raw)
        self.assertEqual(audit['sources']['tabular'],sha256(raw).hexdigest());self.assertTrue(audit['accepted'])
        with self.assertRaises(ValueError):certify(q,b'>s\nACGA\n',raw)
        with self.assertRaises(WorkLimit):certify(q,s,raw*2,row_limit=1)
        self.assertEqual(len(certify(q,s,raw*2,row_limit=2)['hits']),2)


class RecallTests(unittest.TestCase):
    def test_complete_denominator_absent_pairs_and_exact_fraction(self):
        r=recall_audit({'q':'ACGT'},{'s':'ACGT','t':'AAAA'},[simple_hit()],{('q','s'):(8,8),('q','t'):(6,0)},thresholds=(5,9))
        self.assertEqual(r['complete_pair_count'],2)
        self.assertEqual(r['thresholds'][0]['recall'],'1/2');self.assertIsNone(r['thresholds'][1]['recall'])
        self.assertEqual(r['thresholds'][0]['misses'],[{'query':'q','subject':'t'}])

    def test_incomplete_reference_and_impossible_scores_rejected(self):
        with self.assertRaises(ValueError):recall_audit({'q':'A'},{'s':'A'},[],{})
        with self.assertRaises(ValueError):recall_audit({'q':'ACGT'},{'s':'ACGT'},[simple_hit()],{('q','s'):(7,0)})
        with self.assertRaises(ValueError):recall_audit({'q':'A'},{'s':'A'},[],{('q','s'):(True,0)})


if __name__=='__main__':unittest.main()
