"""NCBI tabular/BTOP ingestion, strict FASTA parsing and literal source replay."""
from dataclasses import dataclass
from decimal import Decimal, InvalidOperation
from fractions import Fraction as Q
from hashlib import sha256
import json
import re
from .blast_alignment import sequence
from .divisor_square import WorkLimit

FIELDS = ('qseqid', 'sseqid', 'pident', 'length', 'mismatch', 'gapopen', 'qstart', 'qend',
          'sstart', 'send', 'evalue', 'bitscore', 'btop', 'qlen', 'slen', 'staxids')
FIELD_LABELS = dict(zip(('query id', 'subject id', '% identity', 'alignment length', 'mismatches',
    'gap opens', 'q. start', 'q. end', 's. start', 's. end', 'evalue', 'bit score',
    'BTOP', 'query length', 'subject length', 'subject tax ids'), FIELDS))
COMPLEMENT = str.maketrans('ACGTRYSWKMBDHVNU', 'TGCAYRSWMKVHDBNA')


def fasta(text, *, size_limit=10000000):
    if type(text) is not str or len(text.encode()) > size_limit:
        raise WorkLimit('FASTA byte limit exceeded')
    out, name, chunks = {}, None, []
    def finish():
        if name is not None:
            if name in out or not chunks:
                raise ValueError('duplicate or empty FASTA record')
            out[name] = sequence(''.join(chunks))
    for line in text.splitlines():
        line = line.strip()
        if not line:
            continue
        if line.startswith('>'):
            finish()
            names = line[1:].split()
            if not names:
                raise ValueError('empty FASTA identifier')
            name, chunks = names[0], []
        elif name is None:
            raise ValueError('sequence before FASTA header')
        else:
            chunks.append(line)
    finish()
    if not out:
        raise ValueError('no FASTA records')
    return out


def btop_features(trace):
    if type(trace) is not str or not trace or len(trace) > 1000000:
        raise ValueError('nonempty bounded BTOP trace required')
    tokens = re.findall(r'\d+|[A-Z-]{2}', trace)
    if ''.join(tokens) != trace:
        raise ValueError('invalid BTOP token')
    matches = mismatches = gaps = openings = length = qspan = sspan = 0
    previous = None
    for token in tokens:
        if token.isdigit():
            count = int(token)
            if count > 1000000:
                raise WorkLimit('BTOP matching run exceeds replay budget')
            matches += count
            length += count
            qspan += count
            sspan += count
            if count:
                previous = None
        else:
            a, b = token
            if a == b:
                raise ValueError('BTOP pair must be a mismatch or a single gap')
            gap = 'I' if a == '-' else 'D' if b == '-' else None
            qspan += a != '-'
            sspan += b != '-'
            length += 1
            gaps += gap is not None
            mismatches += gap is None
            openings += gap is not None and gap != previous
            previous = gap
    return {'features': [matches, mismatches, openings, gaps], 'length': length,
            'query_span': qspan, 'subject_span': sspan, 'tokens': tokens}


@dataclass(frozen=True)
class BlastHit:
    fields: dict

    def __post_init__(self):
        f = dict(self.fields)
        required = set(FIELDS[:13])
        if not required <= set(f):
            raise ValueError('BLAST custom output must contain standard fields and btop')
        if any(type(f[k]) is not str or not f[k] or any(c.isspace() for c in f[k]) for k in ('qseqid', 'sseqid')):
            raise ValueError('nonempty whitespace-free sequence identifiers required')
        for key in ('length', 'mismatch', 'gapopen', 'qstart', 'qend', 'sstart', 'send', 'qlen', 'slen'):
            if key in f:
                if isinstance(f[key], bool):
                    raise ValueError('integer BLAST field required')
                f[key] = int(f[key])
                if f[key] < (0 if key in ('mismatch', 'gapopen') else 1):
                    raise ValueError('BLAST integer field out of range')
        try:
            for key in ('evalue', 'bitscore', 'pident'):
                value = Decimal(str(f[key]))
                if not value.is_finite() or value < 0:
                    raise ValueError('finite nonnegative BLAST statistic required')
                f[key] = str(value)
        except InvalidOperation as error:
            raise ValueError('invalid BLAST statistic') from error
        if Decimal(f['pident']) > 100:
            raise ValueError('identity percentage above 100')
        info = btop_features(f['btop'])
        if [f['length'], f['mismatch'], f['gapopen']] != [info['length'], info['features'][1], info['features'][2]]:
            raise ValueError('BTOP and declared alignment counts disagree')
        if abs(f['qend']-f['qstart'])+1 != info['query_span'] or abs(f['send']-f['sstart'])+1 != info['subject_span']:
            raise ValueError('BTOP coordinate spans disagree; translated output requires a separate adapter')
        for prefix in ('q', 's'):
            if prefix+'len' in f and max(f[prefix+'start'], f[prefix+'end']) > f[prefix+'len']:
                raise ValueError('alignment exceeds declared sequence length')
        # Percentage identity is rounded in tabular output; validate within its last decimal place.
        decimal = Decimal(f['pident'])
        tolerance = Q(Decimal(1).scaleb(decimal.as_tuple().exponent))/2
        exact_percent = Q(100*info['features'][0], f['length'])
        if abs(Q(decimal)-exact_percent) > tolerance:
            raise ValueError('reported identity percentage disagrees with BTOP')
        object.__setattr__(self, 'fields', f)

    @property
    def features(self):
        return tuple(btop_features(self.fields['btop'])['features'])

    @property
    def strand(self):
        f = self.fields
        return (1 if f['qend'] >= f['qstart'] else -1)*(1 if f['send'] >= f['sstart'] else -1)

    def interval(self, prefix, *, oriented=False):
        f = self.fields
        a, b = f[prefix+'start'], f[prefix+'end']
        if oriented and b < a:
            return (-a, -b+1)
        return (min(a, b)-1, max(a, b))

    def packet(self):
        return {'fields': dict(self.fields), 'features': list(self.features), 'relative_strand': self.strand}


def tabular(text, fields=None, *, row_limit=100000):
    if type(text) is not str or len(text.encode()) > 50000000:
        raise WorkLimit('BLAST text byte limit exceeded')
    fields = list(FIELDS if fields is None else fields)
    out = []
    for number, line in enumerate(text.splitlines(), 1):
        if line.startswith('# Fields: '):
            labels = line[len('# Fields: '):].split(', ')
            fields = [FIELD_LABELS.get(label, label) for label in labels]
        elif line and not line.startswith('#'):
            columns = line.split('\t')
            if len(columns) != len(fields) or len(set(fields)) != len(fields):
                raise ValueError(f'BLAST field count or duplicate field on line {number}')
            if len(out) >= row_limit:
                raise WorkLimit('BLAST row budget exceeded')
            try:
                out.append(BlastHit(dict(zip(fields, columns))))
            except (ValueError, TypeError) as error:
                raise ValueError(f'BLAST line {number}: {error}') from error
    return out


def oriented_segment(seq, start, end, *, nucleotide=True):
    seq = sequence(seq)
    if min(start, end) < 1 or max(start, end) > len(seq):
        raise ValueError('coordinates outside supplied sequence')
    segment = seq[min(start, end)-1:max(start, end)]
    if end < start:
        if not nucleotide:
            raise ValueError('reverse protein coordinates are unsupported')
        if any(c not in 'ACGTRYSWKMBDHVNU' for c in segment):
            raise ValueError('nucleotide alphabet required for reverse complement')
        segment = segment.translate(COMPLEMENT)[::-1]
    return segment


def replay(hit, query, subject, *, nucleotide=True):
    f = hit.fields
    q = oriented_segment(query, f['qstart'], f['qend'], nucleotide=nucleotide)
    s = oriented_segment(subject, f['sstart'], f['send'], nucleotide=nucleotide)
    i = j = 0
    a, b = [], []
    for token in btop_features(f['btop'])['tokens']:
        if token.isdigit():
            n = int(token)
            if q[i:i+n] != s[j:j+n] or len(q[i:i+n]) != n:
                raise ValueError('BTOP match run disagrees with source sequences')
            a.append(q[i:i+n]); b.append(s[j:j+n]); i += n; j += n
        else:
            x, y = token
            if x != '-':
                if i >= len(q) or q[i] != x:
                    raise ValueError('BTOP query residue disagrees with source')
                i += 1
            if y != '-':
                if j >= len(s) or s[j] != y:
                    raise ValueError('BTOP subject residue disagrees with source')
                j += 1
            a.append(x); b.append(y)
    if i != len(q) or j != len(s):
        raise ValueError('BTOP replay did not consume both coordinate intervals')
    return {'query': ''.join(a), 'subject': ''.join(b), 'source_replayed': True,
            'query_sha256': sha256(sequence(query).encode()).hexdigest(),
            'subject_sha256': sha256(sequence(subject).encode()).hexdigest(),
            'scope': 'literal traceback agreement on supplied source sequences; not search completeness'}


def provenance(hits, source, parameters=None):
    payload = {'hits': [h.packet() for h in hits], 'source': source, 'parameters': parameters or {}}
    digest = sha256(json.dumps(payload, sort_keys=True, separators=(',', ':'), allow_nan=False).encode()).hexdigest()
    return {'schema': 'pp-blast-ingestion/1', **payload, 'sha256': digest,
            'complete_database_search': False, 'kernel_checked': False}
