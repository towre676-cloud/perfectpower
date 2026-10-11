"""Lossless source retention and explicit, conservative GBSeq feature projection."""
from hashlib import sha256
from copy import deepcopy
import json
import re
from pathlib import Path
import xml.etree.ElementTree as ET
from .blast_io import replay


def xml_tree(node):
    return {'tag': node.tag, 'attributes': dict(node.attrib), 'text': node.text,
            'tail': node.tail, 'children': [xml_tree(child) for child in node]}


def genbank(raw):
    """Retain every XML field; normalized coordinates are zero-based half-open."""
    root = ET.fromstring(raw)
    if root.tag != 'GBSet' or any(x.tag != 'GBSeq' for x in root):
        raise ValueError('GBSet containing only GBSeq records required')
    records = {}
    for node in root:
        accession = node.findtext('GBSeq_accession-version')
        seq = (node.findtext('GBSeq_sequence') or '').upper()
        if not accession or not re.fullmatch(r'[A-Z][A-Z0-9_]*\.[1-9][0-9]*', accession) or accession in records or not seq or not seq.isascii() or not seq.isalpha():
            raise ValueError('unique versioned records with literal sequence required')
        if len(seq) != int(node.findtext('GBSeq_length')):
            raise ValueError('GBSeq declared length differs from sequence')
        features = []
        for feature in node.findall('GBSeq_feature-table/GBFeature'):
            qualifiers = [{'name': q.findtext('GBQualifier_name'), 'value': q.findtext('GBQualifier_value')}
                          for q in feature.findall('GBFeature_quals/GBQualifier')]
            intervals = []
            for interval in feature.findall('GBFeature_intervals/GBInterval'):
                a = interval.findtext('GBInterval_from') or interval.findtext('GBInterval_point')
                b = interval.findtext('GBInterval_to') or interval.findtext('GBInterval_point')
                remote = interval.findtext('GBInterval_accession')
                if a is None or b is None or (remote and remote != accession):
                    intervals.append({'status': 'unsupported_remote_or_missing', 'source': xml_tree(interval)})
                    continue
                start, end = sorted((int(a), int(b)))
                if not 1 <= start <= end <= len(seq):
                    raise ValueError('local GBSeq interval outside source sequence')
                comp = interval.find('GBInterval_iscomp')
                intervals.append({'status': 'local', 'start': start-1, 'end': end,
                                  'strand': -1 if comp is not None and comp.attrib.get('value') == 'true' else 1})
            features.append({'key': feature.findtext('GBFeature_key'),
                             'location': feature.findtext('GBFeature_location'),
                             'intervals': intervals, 'qualifiers': qualifiers,
                             'source': xml_tree(feature)})
        records[accession] = {'accession': accession, 'length': len(seq), 'sequence_sha256': sha256(seq.encode()).hexdigest(),
                             'sequence': seq, 'definition': node.findtext('GBSeq_definition'),
                             'organism': node.findtext('GBSeq_organism'), 'taxonomy': node.findtext('GBSeq_taxonomy'),
                             'features': features, 'source': xml_tree(node)}
    return records


def load_corpus(directory):
    directory = Path(directory)
    manifest = json.loads((directory/'manifest.json').read_text())
    records = {}
    for entry in manifest['sources']:
        path = directory / entry['file']
        if path.resolve().parent != directory.resolve():
            raise ValueError('corpus source must be a direct child')
        raw = path.read_bytes()
        if sha256(raw).hexdigest() != entry['sha256']:
            raise ValueError('corpus source hash mismatch')
        if entry['file'].endswith('.xml'):
            batch = genbank(raw)
            if records.keys() & batch.keys():
                raise ValueError('duplicate corpus record across batches')
            records.update(batch)
        elif entry['file'] == 'esearch.json':
            result = json.loads(raw)['esearchresult']
            if result['idlist'] != manifest['accessions'] or int(result['count']) != manifest['record_count']:
                raise ValueError('ESearch source and manifest disagree')
    if set(records) != set(manifest['accessions']) or len(records) != manifest['record_count']:
        raise ValueError('incomplete corpus: every pinned accession must be present exactly once')
    return manifest, records


def project(record, start, end):
    """Overlap is a coordinate fact, not a functional or orthology assignment."""
    a, b = min(start, end)-1, max(start, end)
    if not 0 <= a < b <= record['length']:
        raise ValueError('HSP projection outside annotation source')
    out = []
    for index, feature in enumerate(record['features']):
        spans = sorted((max(a, x['start']), min(b, x['end'])) for x in feature['intervals'] if x['status'] == 'local')
        merged = []
        for left, right in spans:
            if left >= right:
                continue
            if merged and left <= merged[-1][1]:
                merged[-1][1] = max(merged[-1][1], right)
            else:
                merged.append([left, right])
        bases = sum(right-left for left, right in merged)
        if bases or any(x['status'] != 'local' for x in feature['intervals']):
            out.append({'feature_index': index, 'key': feature['key'], 'location': feature['location'],
                        'overlap_intervals': merged, 'overlap_bases': bases,
                        'projection_complete': all(x['status'] == 'local' for x in feature['intervals']),
                        'qualifiers': feature['qualifiers']})
    return out


def annotation_sources(directory):
    """Complete database plus separately pinned query annotation records."""
    directory=Path(directory)
    manifest,records=load_corpus(directory)
    extra=json.loads((directory/'query_sources.json').read_text())
    for entry in extra['sources']:
        path=directory/entry['file']
        if path.resolve().parent != directory.resolve():
            raise ValueError('query source must be a direct child')
        raw=path.read_bytes()
        if sha256(raw).hexdigest()!=entry['sha256']:
            raise ValueError('query annotation source hash mismatch')
        batch=genbank(raw)
        for key,record in batch.items():
            if key in records and records[key]['sequence'] != record['sequence']:
                raise ValueError('duplicate version disagrees across annotation sources')
        records.update(batch)
    return manifest,records


def annotate(hits, queries, records, *, manifest=None):
    if any(key not in records or records[key]['sequence'] != seq for key, seq in queries.items()):
        raise ValueError('query annotation must bind to the exact versioned query sequence')
    rows = []
    for index, hit in enumerate(hits):
        f = hit.fields
        if f['qseqid'] not in queries:
            raise ValueError('HSP query is outside supplied query annotation carrier')
        q, s = records[f['qseqid']], records[f['sseqid']]
        if f.get('qlen')!=q['length'] or f.get('slen')!=s['length']:
            raise ValueError('annotation length declarations differ from source records')
        replay(hit,q['sequence'],s['sequence'])
        rows.append({'hit_index': index, 'query': f['qseqid'], 'subject': f['sseqid'],
                     'query_features': project(q, f['qstart'], f['qend']),
                     'subject_features': project(s, f['sstart'], f['send'])})
    return {'schema': 'pp-blast-annotation/1', 'manifest': manifest,
            'records': {k: deepcopy({a:b for a,b in v.items() if a != 'sequence'}) for k,v in records.items()},
            'hsp_annotations': rows, 'record_count': len(records), 'hit_count': len(hits),
            'scope': 'all source XML fields and qualifiers retained; literal feature overlap only; no inferred orthology',
            'kernel_checked': False}


def coding_audit(record):
    """Check every annotated CDS; retain unknown/exception cases as explicit states."""
    from itertools import product
    from .blast_io import COMPLEMENT
    amino='FFLLSSSSYY**CC*WLLLLPPPPHHQQRRRRIIIMTTTTNNKKSSRRVVVVAAAADDEEGGGG'
    code=dict(zip((''.join(x) for x in product('TCAG',repeat=3)),amino))
    rows=[]
    for index,feature in enumerate(record['features']):
        if feature['key'] != 'CDS': continue
        qualifiers={}
        for q in feature['qualifiers']: qualifiers.setdefault(q['name'],[]).append(q['value'])
        row={'feature_index':index,'location':feature['location']}
        if len(qualifiers.get('translation',[])) != 1 or not isinstance(qualifiers['translation'][0],str) or not qualifiers['translation'][0]:
            row['status']='missing_or_multiple_translation'
        elif qualifiers.get('transl_table',['1']) != ['1'] or any(k in qualifiers for k in ('transl_except','ribosomal_slippage','exception')):
            row['status']='unsupported_translation_table_or_exception'
        elif not feature['intervals'] or any(x['status']!='local' for x in feature['intervals']):
            row['status']='unsupported_location'
        else:
            chunks=[]
            for interval in feature['intervals']:
                text=record['sequence'][interval['start']:interval['end']]
                chunks.append(text if interval['strand']==1 else text.translate(COMPLEMENT)[::-1])
            offset=qualifiers.get('codon_start',['1'])
            if len(offset)!=1 or offset[0] not in ('1','2','3'):
                raise ValueError('invalid annotated codon_start')
            coding=''.join(chunks)[int(offset[0])-1:]
            expected=qualifiers['translation'][0]
            if any(c not in 'ACGT' for c in coding):
                row['status']='ambiguous_coding_letters'
            else:
                translated=''.join(code[coding[i:i+3]] for i in range(0,len(coding)-2,3))
                initiation=False
                if expected.startswith('M') and coding[:3] in ('CTG','TTG') and '<' not in feature['location'] and '>' not in feature['location']:
                    translated='M'+translated[1:];initiation=True
                if translated.endswith('*'): translated=translated[:-1]
                row.update(status='literal_translation_agrees' if translated==expected else 'translation_discrepancy',
                           computed_translation=translated,annotated_translation=expected,
                           trailing_partial_codon_bases=len(coding)%3,alternative_initiation=initiation)
        rows.append(row)
    return rows
