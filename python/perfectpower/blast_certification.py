"""Independent adapter audit. Receipts certify supplied bytes, not external servers."""
from hashlib import sha256
from .blast_io import fasta, tabular, oriented_segment, replay


def source_bytes(path):
    """Lossless retained source compression; source hashes bind decompressed bytes."""
    import gzip
    from pathlib import Path
    path=Path(path)
    raw=path.read_bytes()
    return gzip.decompress(raw) if path.suffix=='.gz' else raw


def independent_trace(trace, query, subject):
    """Character scanner independent of production regex/token/features parsing."""
    at = qi = si = matches = mismatch = openings = gaps = columns = 0
    previous = None
    while at < len(trace):
        if '0' <= trace[at] <= '9':
            end = at
            while end < len(trace) and '0' <= trace[end] <= '9':
                end += 1
            n = int(trace[at:end])
            if n > 1000000 or len(query[qi:qi+n]) != n or query[qi:qi+n] != subject[si:si+n]:
                raise ValueError('independent matching-run check failed')
            qi += n; si += n; matches += n; columns += n
            if n:
                previous = None
            at = end
        else:
            if at+1 >= len(trace):
                raise ValueError('unpaired BTOP residue')
            a,b = trace[at:at+2]
            if a == b or any(c != '-' and not 'A' <= c <= 'Z' for c in (a,b)):
                raise ValueError('invalid BTOP residue pair')
            if a != '-':
                if qi >= len(query) or query[qi] != a:
                    raise ValueError('independent query residue check failed')
                qi += 1
            if b != '-':
                if si >= len(subject) or subject[si] != b:
                    raise ValueError('independent subject residue check failed')
                si += 1
            state = 'I' if a == '-' else 'D' if b == '-' else None
            mismatch += state is None; gaps += state is not None
            openings += state is not None and state != previous
            previous = state; columns += 1; at += 2
    if qi != len(query) or si != len(subject):
        raise ValueError('independent replay must consume both entire intervals')
    return {'features':[matches,mismatch,openings,gaps], 'length':columns}


def certify(query_bytes, subject_bytes, tabular_bytes, *, nucleotide=True, row_limit=100000):
    if type(row_limit) is not int or row_limit < 1 or type(nucleotide) is not bool:
        raise ValueError('positive integer row budget and boolean nucleotide mode required')
    queries, subjects = fasta(query_bytes.decode()), fasta(subject_bytes.decode())
    hits = tabular(tabular_bytes.decode(), row_limit=row_limit)
    checks = []
    for index, hit in enumerate(hits):
        f = hit.fields
        q = queries[f['qseqid']]; s = subjects[f['sseqid']]
        if f.get('qlen') != len(q) or f.get('slen') != len(s):
            raise ValueError('source length declarations required and must match FASTA')
        original = replay(hit,q,s,nucleotide=nucleotide)
        qs = oriented_segment(q,f['qstart'],f['qend'],nucleotide=nucleotide)
        ss = oriented_segment(s,f['sstart'],f['send'],nucleotide=nucleotide)
        check = independent_trace(f['btop'],qs,ss)
        if check['features'] != list(hit.features) or check['length'] != f['length']:
            raise ValueError('independent feature totals disagree')
        checks.append({'hit_index':index, 'query_sha256':original['query_sha256'],
                       'subject_sha256':original['subject_sha256'], **check, 'accepted':True})
    from pathlib import Path
    modules=[Path(__file__),Path(__file__).with_name('blast_io.py')]
    return {'schema':'pp-blast-adapter-audit/1',
            'adapter_sources':{p.name:sha256(p.read_bytes()).hexdigest() for p in modules},
            'sources':{name:sha256(raw).hexdigest() for name,raw in
                       [('query_fasta',query_bytes),('subject_fasta',subject_bytes),('tabular',tabular_bytes)]},
            'query_records':len(queries), 'subject_records':len(subjects), 'hits':checks,
            'row_limit':row_limit,
            'accepted':True, 'kernel_checked':False,
            'supported':['FASTA literal ASCII letters','BLAST outfmt6/7 with BTOP and lengths',
                         'nucleotide forward/reverse coordinate replay' if nucleotide else 'forward protein coordinate replay'],
            'scope':'two independent executable traceback checks of every supplied HSP; no translated-coordinate or server-origin certification'}
