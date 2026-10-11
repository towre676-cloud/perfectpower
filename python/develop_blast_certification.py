"""Reproduce annotation, adapter audits, exhaustive recall and measured benchmarks."""
import argparse
import gzip
from hashlib import sha256
import json
import os
from pathlib import Path
import platform
import random
import statistics
from math import comb
import subprocess
import tempfile
import time
from fractions import Fraction
from perfectpower.blast_annotation import annotation_sources, annotate, coding_audit
from perfectpower.blast_certification import certify, source_bytes
from perfectpower.blast_io import fasta, tabular, BlastHit
from perfectpower.blast_alignment import exact_alignment
from perfectpower.blast_recall import recall_audit
from perfectpower.blast_mining import ChainIndex

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'receipts/blast/certification'
DATA=ROOT/'data/blast_corpus'


def write(path, value):
    path.parent.mkdir(parents=True,exist_ok=True)
    if path.suffix == '.gz':
        raw=(json.dumps(value,sort_keys=True,separators=(',',':'))+'\n').encode()
        path.write_bytes(gzip.compress(raw,mtime=0))
    else:
        path.write_text(json.dumps(value,sort_keys=True,indent=2)+'\n')


def prepare():
    manifest,all_records=annotation_sources(DATA)
    queries=fasta((ROOT/'examples/blast/insulin_family.fasta').read_text())
    for key,seq in queries.items():
        if key not in all_records or all_records[key]['sequence'] != seq:
            raise ValueError('query source annotation disagrees with retained FASTA')
    subjects={key:all_records[key]['sequence'] for key in manifest['accessions']}
    (DATA/'database.fasta').write_text(''.join('>'+key+'\n'+seq+'\n' for key,seq in sorted(subjects.items())))
    return manifest,all_records,queries,subjects


def reference_scan(queries,subjects,binary):
    pairs=[(q,s) for q in sorted(queries) for s in sorted(subjects)]
    text=''.join(queries[q]+' '+subjects[s]+'\n' for q,s in pairs)
    start=time.perf_counter()
    result=subprocess.run([str(binary)],input=text,text=True,capture_output=True,check=True)
    elapsed=time.perf_counter()-start
    lines=result.stdout.splitlines()
    if len(lines)!=len(pairs):
        raise ValueError('reference scanner omitted database pairs')
    reference={pair:tuple(map(int,line.split())) for pair,line in zip(pairs,lines)}
    return reference,elapsed


def reference_validation(binary):
    rng=random.Random(20261012)
    cases=[(''.join(rng.choice('ACGT') for _ in range(rng.randrange(1,12))),
            ''.join(rng.choice('ACGT') for _ in range(rng.randrange(1,12)))) for _ in range(120)]
    cases += [('A'*20,'A'*7+'C'*3+'A'*7),('ACGTT','AACGTT'),('AAAA','TTTT')]
    text=''.join(q+' '+s+'\n' for q,s in cases)
    lines=subprocess.run([str(binary)],input=text,text=True,capture_output=True,check=True).stdout.splitlines()
    if len(lines)!=len(cases): raise ValueError('incomplete native validation')
    from perfectpower.blast_io import COMPLEMENT
    for (q,s),line in zip(cases,lines):
        values=tuple(map(int,line.split()))
        expected=tuple(int(exact_alignment(q,t,(2,-3,-5,-2))['score']) for t in
                       [s,s.translate(COMPLEMENT)[::-1]])
        if values!=expected: raise ValueError('native reference differs from independent Python solver')
    return {'cases':len(cases),'strand_checks':2*len(cases),'accepted':True,'seed':20261012}


def synthetic_hit(i):
    return BlastHit(dict(qseqid='q',sseqid='s',pident='100',length=1,mismatch=0,gapopen=0,
                         qstart=i+1,qend=i+1,sstart=i+1,send=i+1,evalue='0',bitscore='1',btop='1',qlen=512,slen=512))


def enumerate_paths(children,n):
    out=[]
    def visit(p):
        out.append(p)
        for child in children[p[-1]]: visit(p+(child,))
    for i in range(n): visit((i,))
    return out


def benchmarks():
    rows=[]
    for n in (8,12,16,40,80):
        hits=[synthetic_hit(i) for i in range(n)]
        times=[]
        for _ in range(3):
            start=time.perf_counter();index=ChainIndex(hits);times.append(time.perf_counter()-start)
        row={'vertices':n,'population':str(index.count),'index_seconds':times,'index_median_seconds':statistics.median(times),
             'polynomial_terms':sum(len(t) for t in index.suffix.values()),'work_cells':index.work}
        if index.count!=(1<<n)-1 or any(index.suffix[i].get((k,k),0)!=comb(n-i-1,k-1)
                                        for i in range(n) for k in range(1,n-i+1)):
            raise ValueError('ordered-DAG polynomial differs from independent binomial formula')
        row['binomial_coefficient_check']=True
        if n<=16:
            enumerations=[]
            for _ in range(3):
                start=time.perf_counter();paths=enumerate_paths(index.children,n);enumerations.append(time.perf_counter()-start)
            if len(paths)!=index.count or any(index.select(k)!=list(paths[k]) for k in (0,len(paths)//2,len(paths)-1)):
                raise ValueError('enumerated benchmark population disagrees with compressed index')
            row.update(enumeration_seconds=enumerations,enumeration_median_seconds=statistics.median(enumerations),enumeration_checked=True)
        else:
            row.update(enumeration_checked=False,enumeration_status='not attempted; exponential population')
        rows.append(row)
    return {'schema':'pp-blast-benchmark/1','python':platform.python_version(),'platform':platform.platform(),
            'cpu':platform.processor(),'trials':3,'seed':20261012,'cases':rows,
            'scope':'same synthetic all-chain population for enumeration/index; process-local timings, no BLAST speedup claim'}


def run(args):
    manifest,records,queries,subjects=prepare(); OUT.mkdir(parents=True,exist_ok=True)
    from collections import Counter
    coding={key:coding_audit(record) for key,record in records.items()}
    write(OUT/'coding_annotation.json',{'schema':'pp-blast-coding-audit/1','records':coding,
          'statuses':dict(Counter(row['status'] for rows in coding.values() for row in rows)),
          'scope':'all annotated CDS, standard code 1; exceptions/ambiguity/missing translations are explicit, not silently accepted',
          'kernel_checked':False})
    with tempfile.TemporaryDirectory() as tmp:
        binary=Path(tmp)/'reference'
        subprocess.run(['g++','-O3','-std=c++17',str(ROOT/'native/blast_reference.cpp'),'-o',str(binary)],check=True)
        validation=reference_validation(binary)
        if args.run_blast:
            db=Path(tmp)/'insulin'
            start=time.perf_counter()
            subprocess.run(['makeblastdb','-in',str(DATA/'database.fasta'),'-dbtype','nucl','-parse_seqids','-out',str(db)],check=True,capture_output=True)
            database_build_seconds=time.perf_counter()-start
            commands=[]
            from perfectpower.blast_io import FIELDS
            for word in (7,11,28):
                command=['blastn','-task','blastn','-query',str(ROOT/'examples/blast/insulin_family.fasta'),'-db',str(db),
                         '-word_size',str(word),'-dust','no','-soft_masking','false','-reward','2','-penalty','-3',
                         '-gapopen','5','-gapextend','2','-evalue','1000000','-max_target_seqs',str(len(subjects)),'-num_threads','1',
                         '-outfmt','6 '+' '.join('saccver' if f=='sseqid' else f for f in FIELDS),'-out',str(DATA/f'blast_word{word}.tsv')]
                trials=[];digests=[]
                for trial in range(3):
                    start=time.perf_counter();subprocess.run(command,check=True,capture_output=True);trials.append(time.perf_counter()-start)
                    digests.append(sha256((DATA/f'blast_word{word}.tsv').read_bytes()).hexdigest())
                if len(set(digests))!=1:raise ValueError('BLAST benchmark repetitions differ')
                command=[x.replace(str(ROOT),'<repository>').replace(str(tmp),'<temporary>') for x in command]
                (DATA/f'blast_word{word}.tsv.gz').write_bytes(gzip.compress((DATA/f'blast_word{word}.tsv').read_bytes(),mtime=0))
                commands.append({'word_size':word,'command':command,'elapsed_seconds':statistics.median(trials),'trials_seconds':trials,
                                 'tabular_sha256':sha256((DATA/f'blast_word{word}.tsv').read_bytes()).hexdigest()})
            write(OUT/'blast_execution.json',{'version':subprocess.run(['blastn','-version'],capture_output=True,text=True,check=True).stdout,
                  'database_sha256':sha256((DATA/'database.fasta').read_bytes()).hexdigest(),
                  'query_sha256':sha256((ROOT/'examples/blast/insulin_family.fasta').read_bytes()).hexdigest(),'runs':commands,
                  'database_build_seconds':database_build_seconds,'benchmark_repetitions':3})
        reference,trials=None,[]
        for trial in range(3):
            values,elapsed=reference_scan(queries,subjects,binary);trials.append(elapsed)
            if reference is not None and reference!=values:raise ValueError('reference benchmark repetitions differ')
            reference=values
    write(OUT/'reference.json',{'schema':'pp-blast-affine-reference/1',
                              'query_sha256':sha256((ROOT/'examples/blast/insulin_family.fasta').read_bytes()).hexdigest(),
                              'database_sha256':sha256((DATA/'database.fasta').read_bytes()).hexdigest(),
                              'scoring':[2,-3,-5,-2],'strand_policy':'forward and reverse-complement subject; literal equality',
                              'pairs':[{'query':q,'subject':s,'scores':list(v)} for (q,s),v in sorted(reference.items())],
                              'elapsed_seconds':statistics.median(trials),'trials_seconds':trials,'validation':validation,
                              'compiler':subprocess.run(['g++','--version'],capture_output=True,text=True,check=True).stdout.splitlines()[0],
                              'flags':['-O3','-std=c++17'],'python_solver_source_sha256':sha256((ROOT/'python/perfectpower/blast_alignment.py').read_bytes()).hexdigest(),
                              'source_sha256':sha256((ROOT/'native/blast_reference.cpp').read_bytes()).hexdigest()})
    for word in (7,11,28):
        raw=source_bytes(DATA/f'blast_word{word}.tsv.gz');hits=tabular(raw.decode(),row_limit=200000)
        audit=certify((ROOT/'examples/blast/insulin_family.fasta').read_bytes(),(DATA/'database.fasta').read_bytes(),raw,row_limit=200000)
        write(OUT/f'adapters_word{word}.json.gz',audit)
        receipt=recall_audit(queries,subjects,hits,reference);receipt['corpus_manifest']=manifest
        receipt['sources']=audit['sources'];write(OUT/f'recall_word{word}.json',receipt)
        print(word,len(hits),[(x['threshold'],x['recall'],x['missed_pairs']) for x in receipt['thresholds']],flush=True)
        annotation=annotate(hits,queries,records,manifest=manifest)
        # Every original XML byte is retained in data/blast_corpus. Do not duplicate XML trees here.
        for record in annotation['records'].values():
            record.pop('source')
            for feature in record['features']: feature.pop('source')
        for row in annotation['hsp_annotations']:
            for field in ('query_features','subject_features'):
                for feature in row[field]: feature.pop('qualifiers')
        annotation['raw_source_retention']='all XML fields remain in hash-bound original GBSeq files; normalized view references accession and feature_index'
        annotation['sources']=audit['sources']
        annotation['query_annotation_sources']=json.loads((DATA/'query_sources.json').read_text())
        write(OUT/f'annotation_word{word}.json.gz',annotation)
    write(OUT/'benchmark.json',benchmarks())


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--run-blast',action='store_true')
    run(parser.parse_args())
