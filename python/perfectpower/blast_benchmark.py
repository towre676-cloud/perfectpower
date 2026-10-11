"""Pinned structural-domain benchmark; labels never enter search or chaining."""
from collections import defaultdict
from decimal import Decimal
from fractions import Fraction
from hashlib import sha256
import gzip
import lzma
import json
from pathlib import Path
import tarfile
import time
from .blast_io import fasta, tabular, replay, FIELDS, btop_features
from .blast_mining import ChainIndex
from .divisor_square import WorkLimit


def aligned_fasta(raw):
    rows = {}; name = None
    for line in raw.decode('ascii').splitlines():
        if line.startswith('>'):
            name = line[1:].split()[0]
            if name in rows: raise ValueError('duplicate reference ID')
            rows[name] = ''
        elif line.strip():
            if name is None: raise ValueError('reference sequence before header')
            if any(c not in '.-' and not c.isascii() or c not in '.-' and not c.isalpha() for c in line.strip()):
                raise ValueError('invalid reference alphabet')
            rows[name] += line.strip()
    if not rows or len({len(s) for s in rows.values()}) != 1:
        raise ValueError('nonempty equal-length reference rows required')
    return rows


def load_dataset(directory):
    directory = Path(directory)
    manifest = json.loads((directory/'manifest.json').read_text())
    raw = (directory/'source.tar.gz').read_bytes()
    if sha256(raw).hexdigest() != manifest['retained_sha256']: raise ValueError('source archive hash mismatch')
    with tarfile.open(fileobj=__import__('io').BytesIO(raw)) as archive:
        members = archive.getmembers()
        if any(not m.isfile() or m.size > 10_000_000 for m in members): raise ValueError('invalid archive member')
        files = {m.name: archive.extractfile(m).read() for m in members}
    if {k: sha256(v).hexdigest() for k,v in files.items()} != manifest['files']:
        raise ValueError('retained member inventory/hash mismatch')
    ids = files['bench1.0/ox/info/ids.txt'].decode().split()
    if len(set(ids)) != len(ids): raise ValueError('duplicate set identifier')
    for kind in ('in','ref'):
        if {k.rsplit('/',1)[1] for k in files if k.startswith('bench1.0/ox/'+kind+'/')} != set(ids):
            raise ValueError('dataset inventory differs from declared ids')
    records = {}; groups = {}; references = {}; mapping = []
    for family in ids:
        source = fasta(files['bench1.0/ox/in/'+family].decode())
        aligned = aligned_fasta(files['bench1.0/ox/ref/'+family])
        if source.keys() != aligned.keys(): raise ValueError('input/reference carriers differ')
        group = []
        for number,(name,seq) in enumerate(source.items()):
            row = aligned[name]
            if ''.join(c for c in row if c not in '.-').upper() != seq:
                raise ValueError('ungapped reference differs from input')
            key = f'{family}__{number:04d}'
            records[key] = seq; group.append(key)
            pos = 0; coordinates = {}
            for column,c in enumerate(row):
                if c not in '.-':
                    pos += 1
                    if c.isupper(): coordinates[pos] = column
            references[key] = coordinates
            mapping.append({'id':key,'source_id':name,'family':family,'length':len(seq),'sha256':sha256(seq.encode()).hexdigest()})
        groups[family] = group
    return manifest, records, groups, references, mapping


def residue_pairs(hit):
    """Independent BTOP coordinate decoder; replay must be performed first."""
    f = hit.fields
    if f['qend'] < f['qstart'] or f['send'] < f['sstart']:
        raise ValueError('protein benchmark requires forward coordinates')
    q,s = f['qstart'],f['sstart']; pairs = set()
    for token in btop_features(f['btop'])['tokens']:
        if token.isdigit():
            n=int(token);pairs.update((q+i,s+i) for i in range(n));q+=n;s+=n
        else:
            a,b=token
            if a!='-' and b!='-': pairs.add((q,s))
            q+=a!='-';s+=b!='-'
    return pairs


def union_coverage(hits):
    spans=sorted(h.interval('q') for h in hits); merged=[]
    for a,b in spans:
        if merged and a<=merged[-1][1]: merged[-1][1]=max(merged[-1][1],b)
        else: merged.append([a,b])
    return sum(b-a for a,b in merged)


def coverage_chain(index):
    """Maximize query coverage, then BLAST bit-score sum; no annotation access."""
    best={}
    for i in reversed(index.order):
        opts=[(index.coverage[i],Decimal(index.hits[i].fields['bitscore']),(i,))]
        for j in index.children[i]:
            c,b,path=best[j];opts.append((index.coverage[i]+c,Decimal(index.hits[i].fields['bitscore'])+b,(i,)+path))
        best[i]=max(opts,key=lambda p:(p[0],p[1],tuple(-v for v in p[2])))
    return max(best.values(),key=lambda p:(p[0],p[1],tuple(-v for v in p[2]))) if best else (0,Decimal(0),())



def baseline_chain(hits):
    """Ordinary maximum-coverage BLAST-HSP chaining, without population counts."""
    best = {}
    order = sorted(range(len(hits)), key=lambda i: (*hits[i].interval('q'),i))
    for i in order:
        f=hits[i].fields;span=f['qend']-f['qstart']+1;bit=Decimal(f['bitscore'])
        options=[(span,bit,(i,))]
        for j in best:
            g=hits[j].fields
            if g['qend']<f['qstart'] and g['send']<f['sstart']:
                cov,b,path=best[j];options.append((cov+span,b+bit,path+(i,)))
        best[i]=max(options,key=lambda p:(p[0],p[1],tuple(-v for v in p[2])))
    return max(best.values(),key=lambda p:(p[0],p[1],tuple(-v for v in p[2]))) if best else (0,Decimal(0),())

def evaluate(records, groups, references, hits, *, coverage=Fraction(1,2), evalue=Decimal('0.001'), cell_limit=1_000_000):
    by_pair=defaultdict(list)
    for hit in hits:
        f=hit.fields;q,s=f['qseqid'],f['sseqid']
        if q not in records or s not in records: raise ValueError('BLAST IDs outside carrier')
        if f['qlen']!=len(records[q]) or f['slen']!=len(records[s]): raise ValueError('BLAST lengths differ from carrier')
        replay(hit,records[q],records[s],nucleotide=False)
        if q!=s and Decimal(f['evalue'])<=evalue: by_pair[q,s].append(hit)
    methods=('best_hsp','any_hsp','hsp_union','blast_chain_dp','exact_chain')
    baseline_seconds=exact_seconds=0.0
    totals={m:{'retrieved_pairs':0,'correct_reference_residue_pairs':0,'predicted_eligible_residue_pairs':0,'unresolved_pairs':0} for m in methods}
    rows=[];denominator=reference_total=0;family_rows=[]
    for family,ids in groups.items():
        local={m:0 for m in methods};local_ref={m:0 for m in methods};local_den=local_truth=0
        for q in ids:
            for s in ids:
                if q==s: continue
                denominator+=1;local_den+=1
                qref,sref=references[q],references[s]
                inv={col:pos for pos,col in sref.items()}
                truth={(pos,inv[col]) for pos,col in qref.items() if col in inv}
                reference_total+=len(truth);local_truth+=len(truth)
                hs=by_pair.get((q,s),[]);threshold=(len(records[q])*coverage.numerator+coverage.denominator-1)//coverage.denominator
                best=max(hs,key=lambda h:(Decimal(h.fields['bitscore']),h.features[0],h.fields['btop'])) if hs else None
                started=time.perf_counter();baseline_cov,_,baseline_path=baseline_chain(hs);baseline_seconds+=time.perf_counter()-started
                selected={'blast_chain_dp':[hs[i] for i in baseline_path],'best_hsp':[best] if best else [],'any_hsp':hs,'hsp_union':hs,'exact_chain':[]}
                cover={'blast_chain_dp':baseline_cov,'best_hsp':0 if best is None else abs(best.fields['qend']-best.fields['qstart'])+1,
                       'any_hsp':max((abs(h.fields['qend']-h.fields['qstart'])+1 for h in hs),default=0),
                       'hsp_union':union_coverage(hs),'exact_chain':0}
                status='complete';count=0;terms=[];work=0;chain=()
                if hs:
                    started=time.perf_counter()
                    try:
                        index=ChainIndex(hs,min_coverage=threshold,cell_limit=cell_limit)
                        cover['exact_chain'],_,chain=coverage_chain(index)
                        selected['exact_chain']=[hs[i] for i in chain]
                        if cover['exact_chain']!=baseline_cov: raise AssertionError('independent chain baseline disagreement')
                        count=index.count;work=index.work
                        terms=index.packet()['length_polynomial']
                        if bool(count)!=(cover['exact_chain']>=threshold): raise AssertionError('recurrence/optimizer disagreement')
                        if count:
                            witness=index.select(0)
                            if index.rank(witness)!=0: raise AssertionError('address disagreement')
                    except WorkLimit as exc:
                        status='work_limit';cover['exact_chain']=None
                    exact_seconds+=time.perf_counter()-started
                row={'family':family,'query':q,'subject':s,'hsps':len(hs),'threshold_residues':threshold,
                     'coverage':cover,'chain_status':status,'chain_count':str(count) if status=='complete' else None,
                     'length_polynomial':terms,'work_cells':work,'chain_indices':list(chain),'reference_pairs':len(truth),'methods':{}}
                for m in methods:
                    retrieved=None if cover[m] is None else cover[m]>=threshold
                    predicted=set().union(*(residue_pairs(h) for h in selected[m])) if selected[m] else set()
                    eligible={(a,b) for a,b in predicted if a in qref and b in sref}
                    correct=len(eligible & truth)
                    row['methods'][m]={'retrieved':retrieved,'correct':correct,'eligible_predicted':len(eligible)}
                    totals[m]['unresolved_pairs']+=retrieved is None
                    totals[m]['retrieved_pairs']+=retrieved is True;local[m]+=retrieved is True
                    totals[m]['correct_reference_residue_pairs']+=correct;local_ref[m]+=correct
                    totals[m]['predicted_eligible_residue_pairs']+=len(eligible)
                # Retain every positive, missed pair and empty candidate population.
                rows.append(row)
        family_rows.append({'family':family,'records':len(ids),'positive_pairs':local_den,'retrieved':local,
                            'reference_pairs':local_truth,'correct_reference_pairs':local_ref})
    nonidentical=[r for r in rows if records[r['query']]!=records[r['subject']]]
    unique_pairs=defaultdict(list)
    for r in nonidentical:unique_pairs[records[r['query']],records[r['subject']]].append(r)
    for m in methods:
        totals[m]['nonidentical_pair_recall']=sum(r['methods'][m]['retrieved'] is True for r in nonidentical)/len(nonidentical) if nonidentical else None
        totals[m]['unique_nonidentical_sequence_pair_recall']=sum(any(r['methods'][m]['retrieved'] is True for r in rs) for rs in unique_pairs.values())/len(unique_pairs) if unique_pairs else None
        totals[m]['pair_recall']=totals[m]['retrieved_pairs']/denominator if denominator else None
        totals[m]['pair_recall_upper_bound']=(totals[m]['retrieved_pairs']+totals[m]['unresolved_pairs'])/denominator if denominator else None
        totals[m]['residue_recall']=totals[m]['correct_reference_residue_pairs']/reference_total if reference_total else None
        eligible=totals[m]['predicted_eligible_residue_pairs']
        totals[m]['eligible_residue_precision']=totals[m]['correct_reference_residue_pairs']/eligible if eligible else None
        totals[m]['family_macro_pair_recall']=sum(r['retrieved'][m]/r['positive_pairs'] for r in family_rows if r['positive_pairs'])/sum(bool(r['positive_pairs']) for r in family_rows)
    within={(r['query'],r['subject']) for r in rows}
    return {'schema':'pp-oxbench-evaluation/1','record_count':len(records),'family_count':len(groups),
            'directed_positive_pairs':denominator,'nonidentical_positive_pairs':len(nonidentical),'unique_nonidentical_positive_sequence_pairs':len(unique_pairs),'reference_residue_pairs':reference_total,'raw_hsps_replayed':len(hits),
            'all_ordered_search_pairs':len(records)**2,'all_queries':len(records),'qualified_cross_set_pair_count':sum(p not in within for p in by_pair),
            'chain_baseline_seconds':baseline_seconds,'exact_population_seconds':exact_seconds,'unique_sequence_count':len(set(records.values())),'totals':totals,'families':family_rows,'pairs':rows,
            'thresholds':{'evalue':str(evalue),'query_coverage':str(coverage)},
            'chain_work_limits':sum(r['chain_status']!='complete' for r in rows),'cell_limit_per_pair':cell_limit,
            'scope':'all sequences searched against pooled local dataset; recall on all same-set directed nonself pairs. Cross-set pairs are unlabelled, not negatives. No nt/nr completeness, orthology or paralogy claim.'}


def stream_hits(path, *, row_limit=2_000_000, byte_limit=250_000_000):
    """Bounded complete gzip ingestion; no lifting of the ordinary parser limit."""
    size=rows=0
    with (lzma.open if str(path).endswith('.xz') else gzip.open)(path,'rt',encoding='ascii') as stream:
        while True:
            line=stream.readline(1_000_001)
            if not line:break
            if len(line)>1_000_000:raise WorkLimit('stream BLAST line budget exceeded')
            size+=len(line)
            if size>byte_limit:raise WorkLimit('stream BLAST uncompressed byte budget exceeded')
            batch=tabular(line,row_limit=1)
            for hit in batch:
                rows+=1
                if rows>row_limit:raise WorkLimit('stream BLAST row budget exceeded')
                yield hit


def retain_reference_hits(path, records, groups):
    """Replay every source HSP, retain only scored within-set nonself pairs."""
    family={k:g for g,ids in groups.items() for k in ids};integer={k:i for i,k in enumerate(records)}
    retained=[];cross=set();queries=set();subjects=set();rows=0
    for hit in stream_hits(path):
        f=hit.fields;q,s=f['qseqid'],f['sseqid']
        if q not in records or s not in records or f['qlen']!=len(records[q]) or f['slen']!=len(records[s]):
            raise ValueError('streamed HSP carrier/length mismatch')
        replay(hit,records[q],records[s],nucleotide=False)
        rows+=1;queries.add(q);subjects.add(s)
        if Decimal(f['evalue'])>Decimal('0.001'):raise ValueError('row exceeds declared search threshold')
        if q!=s and family[q]==family[s]:retained.append(hit)
        elif family[q]!=family[s]:cross.add((integer[q],integer[s]))
    return retained,{'raw_hsps_replayed':rows,'qualified_cross_set_pair_count':len(cross),
                     'queries_appearing_in_output':len(queries),'subjects_appearing_in_output':len(subjects),
                     'within_set_nonself_hsps':len(retained),'stream_limits':{'rows':2_000_000,'uncompressed_bytes':250_000_000}}
