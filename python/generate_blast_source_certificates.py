"""Generate kernel-checkable literal BTOP replay inputs from hash-bound corpus bytes.

The source-to-Lean encoding is independently rechecked, never silently trusted.
"""
import argparse
from hashlib import sha256
import json
import re
from pathlib import Path
from perfectpower.blast_io import fasta, tabular
from perfectpower.blast_certification import source_bytes

ROOT=Path(__file__).resolve().parents[1]


def generate(words=(28,)):
    if len(set(words))!=len(words) or any(w not in (7,11,28) for w in words):
        raise ValueError('distinct supported word-size runs required')
    queries_path=ROOT/'examples/blast/insulin_family.fasta'
    subjects_path=ROOT/'data/blast_corpus/database.fasta'
    query=fasta(queries_path.read_text());subject=fasta(subjects_path.read_text())
    if any(query[k]!=subject[k] for k in query.keys() & subject.keys()):
        raise ValueError('query and database versions have conflicting source sequences')
    sequences={**subject,**query}
    names={accession:f'source_{i}' for i,accession in enumerate(sorted(sequences))}
    directory=ROOT/'PerfectPower/Generated/BlastCertification';directory.mkdir(parents=True,exist_ok=True)
    sources='import PerfectPower.BlastSourceReplay\nnamespace PerfectPower.BlastSourceReplay.Generated\n'
    for key in sorted(sequences):
        sources+=f'def {names[key]} : String := {json.dumps(sequences[key])}\n'
    sources+='end PerfectPower.BlastSourceReplay.Generated\n'
    sourcepath=directory/'Sources.lean';sourcepath.write_text(sources)
    modules=[str(sourcepath.relative_to(ROOT))];rows=[]
    for word in words:
        path=ROOT/f'data/blast_corpus/blast_word{word}.tsv.gz'
        hits=tabular(source_bytes(path).decode(),row_limit=200000)
        for offset in range(0,len(hits),50):
            module=directory/f'Word{word}Batch{offset//50:04}.lean'
            source='import PerfectPower.Generated.BlastCertification.Sources\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace PerfectPower.BlastSourceReplay.Generated\n'
            name=f'word{word}batch{offset//50:04}'
            source+=f'def {name} : List Input := [\n'
            terms=[]
            for hit in hits[offset:offset+50]:
                f=hit.fields
                terms.append('  ⟨'+', '.join([names[f['qseqid']],names[f['sseqid']],
                     str(f['qstart']),str(f['qend']),str(f['sstart']),str(f['send']),json.dumps(f['btop'])])+'⟩')
            source+=',\n'.join(terms)+'\n]\n'
            source+=f'theorem {name}_accepted : {name}.all accepts = true := by decide +kernel\n#print axioms {name}_accepted\n'
            source+='end PerfectPower.BlastSourceReplay.Generated\n';module.write_text(source)
            modules.append(str(module.relative_to(ROOT)))
        rows.append({'word_size':word,'hits':len(hits),'source_sha256':sha256(source_bytes(path)).hexdigest()})
    manifest={'schema':'pp-blast-source-kernel-inputs/1','modules':modules,'runs':rows,
              'query_sha256':sha256(queries_path.read_bytes()).hexdigest(),
              'database_sha256':sha256(subjects_path.read_bytes()).hexdigest(),
              'scope':'kernel literal source-coordinate/BTOP acceptance; source encoding and file hashes independently checked by executable generator'}
    (ROOT/'receipts/blast/certification/source_kernel_inputs.json').write_text(json.dumps(manifest,indent=2)+'\n')
    return manifest


def validate_encoding(manifest):
    """Re-read source bytes and independently inspect the literal Lean encoding."""
    queries=ROOT/'examples/blast/insulin_family.fasta';subjects=ROOT/'data/blast_corpus/database.fasta'
    for path,key in [(queries,'query_sha256'),(subjects,'database_sha256')]:
        if sha256(path.read_bytes()).hexdigest()!=manifest[key]:
            raise ValueError('kernel input source hash mismatch')
    q,s=fasta(queries.read_text()),fasta(subjects.read_text())
    if any(q[k]!=s[k] for k in q.keys() & s.keys()):
        raise ValueError('query and database versions have conflicting source sequences')
    sequences={**s,**q}
    source=(ROOT/manifest['modules'][0]).read_text()
    literals=re.findall(r'def (source_\d+) : String := ("[A-Z]+")',source)
    if len(literals)!=len(sequences) or len(dict(literals))!=len(literals):
        raise ValueError('kernel source carrier differs from complete FASTA sources')
    names={f'source_{i}':key for i,key in enumerate(sorted(sequences))}
    for name,literal in literals:
        if name not in names or json.loads(literal)!=sequences[names[name]]:
            raise ValueError('Lean literal sequence differs from source FASTA')
    for run in manifest['runs']:
        word=run['word_size'];raw=source_bytes(ROOT/f'data/blast_corpus/blast_word{word}.tsv.gz')
        if sha256(raw).hexdigest()!=run['source_sha256']:raise ValueError('kernel trace source hash mismatch')
        hits=tabular(raw.decode(),row_limit=200000);encoded=[]
        modules=[m for m in manifest['modules'][1:] if f'/Word{word}Batch' in m]
        for module in modules:
            rows=re.findall(r'⟨(source_\d+), (source_\d+), (\d+), (\d+), (\d+), (\d+), ("[A-Z0-9-]+")⟩',(ROOT/module).read_text())
            encoded += [(names[q],names[s],int(a),int(b),int(c),int(d),json.loads(trace)) for q,s,a,b,c,d,trace in rows]
        expected=[tuple(hit.fields[k] for k in ('qseqid','sseqid','qstart','qend','sstart','send','btop')) for hit in hits]
        if encoded!=expected or len(hits)!=run['hits']:
            raise ValueError('kernel literal inputs omit or alter source HSPs')
    return True


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--words',nargs='+',type=int,choices=[7,11,28],default=[28])
    args=parser.parse_args();print(json.dumps(generate(args.words),indent=2))
