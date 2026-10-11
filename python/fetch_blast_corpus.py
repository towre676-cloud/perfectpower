"""Explicit live acquisition; offline experiments never silently refresh sources."""
import argparse
from datetime import datetime, timezone
from hashlib import sha256
import json
from pathlib import Path
import time
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET


def acquire(directory, term):
    directory = Path(directory)
    directory.mkdir(parents=True, exist_ok=True)
    def fetch(endpoint, params):
        url = 'https://eutils.ncbi.nlm.nih.gov/entrez/eutils/' + endpoint + '?' + urllib.parse.urlencode(params)
        for attempt in range(4):
            try:
                with urllib.request.urlopen(url, timeout=90) as response:
                    raw = response.read()
                time.sleep(.4)
                return url, raw
            except Exception:
                if attempt == 3:
                    raise
                time.sleep(2 ** attempt)
    url, raw = fetch('esearch.fcgi', dict(db='nuccore', term=term, retmode='json', retmax=10000, idtype='acc'))
    result = json.loads(raw)['esearchresult']
    ids = result['idlist']
    if len(ids) != int(result['count']) or len(set(ids)) != len(ids):
        raise ValueError('complete unique ESearch accession list required; no truncation accepted')
    (directory / 'esearch.json').write_bytes(raw)
    sources = [{'file': 'esearch.json', 'url': url, 'sha256': sha256(raw).hexdigest()}]
    observed = []
    for offset in range(0, len(ids), 100):
        batch = ids[offset:offset+100]
        name = f'genbank_{offset:05}.xml'
        url, raw = fetch('efetch.fcgi', dict(db='nuccore', id=','.join(batch), rettype='gb', retmode='xml'))
        root = ET.fromstring(raw)
        found = [x.findtext('GBSeq_accession-version') for x in root.findall('GBSeq')]
        if set(found) != set(batch) or len(found) != len(batch):
            raise ValueError('EFetch accession set differs from requested batch')
        observed.extend(found)
        (directory / name).write_bytes(raw)
        sources.append({'file': name, 'url': url, 'sha256': sha256(raw).hexdigest()})
        print(f'Pinned {len(observed)}/{len(ids)} records', flush=True)
    manifest = {'schema': 'pp-blast-corpus/1', 'retrieved_utc': datetime.now(timezone.utc).isoformat(),
                'database': 'nuccore', 'search_term': term, 'accessions': ids,
                'record_count': len(ids), 'sources': sources,
                'scope': 'complete accession set from this ESearch response; a query-defined RefSeq corpus, not nt/nr'}
    (directory / 'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('directory')
    parser.add_argument('--term', default='INS[Gene Name] AND refseq[filter] AND biomol_mrna[PROP]')
    args = parser.parse_args()
    acquire(args.directory, args.term)
