"""python -m perfectpower.blast_cli: offline exploration and explicit acquisition."""
import argparse
import json
from pathlib import Path
from .blast_alignment import AlignmentFamily, exact_alignment, weights
from .blast_io import fasta, tabular, provenance, replay
from .blast_parameters import line_atlas, plane_atlas, robustness
from .blast_machinery import partition_statistics
from .blast_report import json_ready, write_report


def main(argv=None):
    parser = argparse.ArgumentParser(description='PerfectPower exact BLAST exploration')
    sub = parser.add_subparsers(dest='command', required=True)
    align = sub.add_parser('align', help='complete global polynomial family from two literal sequences')
    align.add_argument('query'); align.add_argument('subject'); align.add_argument('--output', required=True)
    pair = sub.add_parser('pair', help='exact local/global scalar alignment of two single-record FASTA files')
    pair.add_argument('query'); pair.add_argument('subject'); pair.add_argument('--global', dest='global_mode', action='store_true'); pair.add_argument('--output', required=True)
    ingest = sub.add_parser('ingest', help='strict outfmt 6/7 + BTOP import, optional source replay')
    ingest.add_argument('input'); ingest.add_argument('--query-fasta'); ingest.add_argument('--subject-fasta'); ingest.add_argument('--protein', action='store_true'); ingest.add_argument('--output', required=True)
    fetch = sub.add_parser('fetch', help='fetch versioned NCBI records into a reproducible cache')
    fetch.add_argument('accessions', nargs='+'); fetch.add_argument('--database', choices=['nuccore','protein'], default='nuccore'); fetch.add_argument('--email', required=True); fetch.add_argument('--cache', required=True); fetch.add_argument('--output', required=True)
    local = sub.add_parser('blast', help='run installed NCBI BLAST+ on two FASTA files')
    local.add_argument('query'); local.add_argument('subject'); local.add_argument('--program', choices=['blastn','blastp'], default='blastn'); local.add_argument('--output', required=True)
    remote = sub.add_parser('submit', help='explicit remote search; returns RID without blocking polling')
    remote.add_argument('query'); remote.add_argument('--email', required=True); remote.add_argument('--cache', required=True); remote.add_argument('--database', default='refseq_rna'); remote.add_argument('--program', choices=['blastn','blastp'], default='blastn'); remote.add_argument('--output', required=True)
    retrieve = sub.add_parser('retrieve', help='retrieve an RID, respecting persistent request pacing')
    retrieve.add_argument('rid'); retrieve.add_argument('--email', required=True); retrieve.add_argument('--cache', required=True); retrieve.add_argument('--output', required=True)
    report = sub.add_parser('report', help='render an atlas receipt as offline HTML')
    report.add_argument('receipt'); report.add_argument('--output', required=True)
    mining = sub.add_parser('mine', help='replay and mine HSPs with exact DAG, graph, motif and Hall machinery')
    mining.add_argument('input'); mining.add_argument('--query-fasta', required=True); mining.add_argument('--subject-fasta', required=True)
    mining.add_argument('--protein', action='store_true'); mining.add_argument('--maximum-evalue', default='0.001')
    mining.add_argument('--minimum-identity', default='1/2'); mining.add_argument('--minimum-coverage', default='0')
    mining.add_argument('--selection-backend', choices=['separator', 'native'], default='separator')
    mining.add_argument('--cell-limit', type=int, default=1000000); mining.add_argument('--motif', action='append', default=[])
    mining.add_argument('--output', required=True)
    motif = sub.add_parser('motif', help='exact overlapping motif-anywhere probabilities and expected counts under IID letters')
    motif.add_argument('motifs', nargs='+'); motif.add_argument('--length', type=int, required=True)
    motif.add_argument('--alphabet', default='ACGT'); motif.add_argument('--probabilities', help='JSON map of exact rational letter probabilities')
    motif.add_argument('--modulus', type=int); motif.add_argument('--output', required=True)
    check = sub.add_parser('verify-mining', help='reexecute a mining receipt against all three original source files')
    check.add_argument('receipt'); check.add_argument('input'); check.add_argument('--query-fasta', required=True); check.add_argument('--subject-fasta', required=True)
    mine_report = sub.add_parser('mining-report', help='write a self-contained explorer for a source-replayed mining receipt')
    mine_report.add_argument('receipt'); mine_report.add_argument('--output', required=True)
    audit = sub.add_parser('certify-source', help='audit every source traceback using two independent decoders')
    audit.add_argument('input'); audit.add_argument('--query-fasta', required=True); audit.add_argument('--subject-fasta', required=True)
    audit.add_argument('--row-limit',type=int,default=100000); audit.add_argument('--protein',action='store_true'); audit.add_argument('--output',required=True)
    annotation = sub.add_parser('annotate', help='retain complete GBSeq annotations and project every supplied HSP')
    annotation.add_argument('input'); annotation.add_argument('--corpus',required=True); annotation.add_argument('--query-fasta',required=True)
    annotation.add_argument('--row-limit',type=int,default=100000); annotation.add_argument('--output',required=True)
    recall = sub.add_parser('recall', help='audit every pinned query/subject pair against a complete reference receipt')
    recall.add_argument('input'); recall.add_argument('--reference',required=True); recall.add_argument('--query-fasta',required=True)
    recall.add_argument('--subject-fasta',required=True); recall.add_argument('--threshold',action='append',type=int)
    recall.add_argument('--row-limit',type=int,default=100000); recall.add_argument('--output',required=True)
    certification_report=sub.add_parser('certification-report',help='offline full-corpus recall and annotation explorer')
    certification_report.add_argument('directory');certification_report.add_argument('--output',required=True)
    args = parser.parse_args(argv)
    if args.command in ('certify-source','annotate','recall'):
        from .blast_certification import source_bytes,certify
        inputs=[args.input,args.query_fasta]
        if args.command in ('certify-source','recall'): inputs.append(args.subject_fasta)
        if args.command=='recall': inputs.append(args.reference)
        if Path(args.output).resolve() in {Path(p).resolve() for p in inputs}:
            parser.error('output must differ from source inputs')
        raw=source_bytes(args.input);qraw=source_bytes(args.query_fasta)
        if args.command=='certify-source':
            receipt=certify(qraw,source_bytes(args.subject_fasta),raw,nucleotide=not args.protein,row_limit=args.row_limit)
        elif args.command=='annotate':
            from .blast_annotation import annotation_sources,annotate,coding_audit
            manifest,records=annotation_sources(args.corpus)
            protected={Path(args.corpus,'manifest.json').resolve(),Path(args.corpus,'query_sources.json').resolve()}
            for name in ('manifest.json','query_sources.json'):
                protected.update(Path(args.corpus,x['file']).resolve() for x in json.loads(Path(args.corpus,name).read_text())['sources'])
            if Path(args.output).resolve() in protected: parser.error('output must differ from annotation sources')
            receipt=annotate(tabular(raw.decode(),row_limit=args.row_limit),fasta(qraw.decode()),records,manifest=manifest)
            receipt['coding_audit']={key:coding_audit(record) for key,record in records.items()}
        else:
            from .blast_recall import recall_audit
            from hashlib import sha256
            reference=json.loads(source_bytes(args.reference))
            sraw=source_bytes(args.subject_fasta)
            if reference.get('schema')!='pp-blast-affine-reference/1' or reference.get('scoring')!=[2,-3,-5,-2] or reference.get('query_sha256')!=sha256(qraw).hexdigest() or reference.get('database_sha256')!=sha256(sraw).hexdigest():
                raise ValueError('reference model and source hashes must match the complete FASTA inputs')
            pairs={}
            for row in reference['pairs']:
                key=row['query'],row['subject']
                if key in pairs: raise ValueError('duplicate reference pair')
                pairs[key]=row['scores']
            receipt=recall_audit(fasta(qraw.decode()),fasta(sraw.decode()),
                    tabular(raw.decode(),row_limit=args.row_limit),pairs,thresholds=args.threshold or (40,100,200))
    elif args.command == 'align':
        family = AlignmentFamily(args.query, args.subject)
        receipt = {'family': family.packet(), 'optimal': family.optimal(weights()),
                   'robustness': robustness(family.terms, weights()), 'statistics': partition_statistics(family),
                   'line': line_atlas(family.terms, (2,-3,0,-1), (0,0,-1,0), (0,12)),
                   'plane': plane_atlas(family.terms, (2,0,0,-1), [(0,-1,0,0),(0,0,-1,0)], [(0,8),(0,12)])}
    elif args.command == 'pair':
        q, s = fasta(Path(args.query).read_text()), fasta(Path(args.subject).read_text())
        if len(q) != 1 or len(s) != 1:
            parser.error('pair requires one FASTA record in each file')
        receipt = exact_alignment(next(iter(q.values())), next(iter(s.values())), local=not args.global_mode)
    elif args.command == 'ingest':
        hits = tabular(Path(args.input).read_text()); receipt = provenance(hits, str(Path(args.input).resolve()))
        if bool(args.query_fasta) != bool(args.subject_fasta):
            parser.error('both source FASTA files are required for replay')
        if args.query_fasta:
            q, s = fasta(Path(args.query_fasta).read_text()), fasta(Path(args.subject_fasta).read_text())
            receipt['replays'] = [replay(h, q[h.fields['qseqid']], s[h.fields['sseqid']], nucleotide=not args.protein) for h in hits]
    elif args.command in ('mine', 'verify-mining'):
        from hashlib import sha256
        from .blast_mining import mine
        paths = {'tabular': Path(args.input), 'query_fasta': Path(args.query_fasta), 'subject_fasta': Path(args.subject_fasta)}
        if args.command == 'mine' and Path(args.output).resolve() in {p.resolve() for p in paths.values()}:
            parser.error('output must differ from all inputs')
        texts = {k: p.read_bytes() for k, p in paths.items()}
        if args.command == 'verify-mining':
            from .blast_mining import verify_mining
            verify_mining(json.loads(Path(args.receipt).read_text()), tabular(texts['tabular'].decode()),
                          fasta(texts['query_fasta'].decode()), fasta(texts['subject_fasta'].decode()),
                          source_hashes={k: sha256(v).hexdigest() for k,v in texts.items()})
            print('Mining receipt replays against all original source files'); return
        receipt = mine(tabular(texts['tabular'].decode()), fasta(texts['query_fasta'].decode()), fasta(texts['subject_fasta'].decode()),
                       nucleotide=not args.protein, maximum_evalue=args.maximum_evalue, minimum_identity=args.minimum_identity,
                       minimum_coverage=args.minimum_coverage, selection_backend=args.selection_backend, cell_limit=args.cell_limit,
                       motifs=args.motif, source_hashes={k: sha256(v).hexdigest() for k, v in texts.items()})
    elif args.command == 'motif':
        from .blast_mining import motif_series, motif_values
        packet = motif_series(args.motifs, alphabet=args.alphabet, probabilities=json.loads(args.probabilities) if args.probabilities else None)
        receipt = {'model': packet, 'values': motif_values(packet, args.length, modulus=args.modulus)}
    elif args.command == 'mining-report':
        from .blast_mining_report import write_mining_report
        write_mining_report(json.loads(Path(args.receipt).read_text()), args.output)
        print(str(Path(args.output).resolve())); return
    elif args.command == 'certification-report':
        from .blast_certification_report import write_report
        write_report(args.directory,args.output)
        print(str(Path(args.output).resolve()));return
    elif args.command in ('fetch', 'submit', 'retrieve'):
        from .blast_client import NCBIClient
        client = NCBIClient(args.cache, email=args.email)
        if args.command == 'fetch':
            receipt = client.fetch_sequences(args.accessions, database=args.database)
        elif args.command == 'submit':
            receipt = client.submit(Path(args.query).read_text(), program=args.program, database=args.database)
        else:
            receipt = client.retrieve(args.rid)
    elif args.command == 'blast':
        from .blast_client import local_blast
        receipt = local_blast(args.query, args.subject, args.output, program=args.program)
        Path(args.output+'.provenance.json').write_text(json.dumps(receipt, indent=2))
        print(json.dumps(receipt, indent=2)); return
    else:
        write_report(json.loads(Path(args.receipt).read_text()), args.output)
        print(str(Path(args.output).resolve())); return
    encoded=(json.dumps(json_ready(receipt), indent=2, sort_keys=True)+'\n').encode()
    if Path(args.output).suffix=='.gz':
        import gzip
        encoded=gzip.compress(encoded,mtime=0)
    Path(args.output).write_bytes(encoded)
    print(str(Path(args.output).resolve()))


if __name__ == '__main__':
    main()
