"""Bounded NCBI input acquisition, persistent BLAST pacing, optional local BLAST+."""
from pathlib import Path
from hashlib import sha256
from urllib.parse import urlencode
from urllib.request import Request, urlopen
from time import time
import json
import re
import shutil
import subprocess
from .blast_io import fasta, FIELDS
from .divisor_square import WorkLimit


class NCBIClient:
    def __init__(self, cache, *, email, tool='perfectpower-blast-atlas', transport=None, clock=time):
        if type(email) is not str or '@' not in email or any(c.isspace() for c in email):
            raise ValueError('contact email required for NCBI requests')
        if not re.fullmatch(r'[A-Za-z0-9_-]{1,64}', tool):
            raise ValueError('bounded tool identifier required')
        self.cache = Path(cache); self.cache.mkdir(parents=True, exist_ok=True)
        self.email, self.tool, self.clock = email, tool, clock
        self.transport = transport or self._http

    @staticmethod
    def _http(url, data=None):
        request = Request(url, data=data, headers={'User-Agent': 'PerfectPower-BLAST-Atlas/1'})
        with urlopen(request, timeout=60) as response:
            payload = response.read(50000001)
        if len(payload) > 50000000:
            raise WorkLimit('NCBI response exceeds 50MB budget')
        return payload.decode('utf-8')

    def fetch_sequences(self, accessions, *, database='nuccore', refresh=False):
        accessions = tuple(accessions)
        if not 1 <= len(accessions) <= 100 or any(not re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*\.\d+', a) for a in accessions):
            raise ValueError('one through 100 versioned accession identifiers required')
        if database not in ('nuccore', 'protein'):
            raise ValueError('nuccore or protein database required')
        params = {'db': database, 'id': ','.join(accessions), 'rettype': 'fasta', 'retmode': 'text', 'email': self.email, 'tool': self.tool}
        key = sha256(json.dumps({'database': database, 'accessions': accessions}, sort_keys=True).encode()).hexdigest()
        path = self.cache/(key+'.fasta')
        if path.exists() and not refresh:
            text = path.read_text()
            cached = True
        else:
            rate = self.cache/'efetch-rate.json'
            now = self.clock()
            previous = json.loads(rate.read_text()).get('last', -100) if rate.exists() else -100
            if now-previous < 0.34:
                raise WorkLimit('NCBI EFetch pacing: retry after 0.34 seconds')
            rate.write_text(json.dumps({'last': now}))
            text = self.transport('https://eutils.ncbi.nlm.nih.gov/entrez/eutils/efetch.fcgi?'+urlencode(params))
            records = fasta(text)
            if set(records) != set(accessions):
                raise ValueError('NCBI accession response differs from requested versioned records')
            path.write_text(text); cached = False
        records = fasta(text)
        if set(records) != set(accessions):
            raise ValueError('cached accession response differs from requested records')
        return {'records': records, 'fasta_path': str(path), 'cache_hit': cached,
                'source': 'NCBI EFetch', 'sha256': sha256(text.encode()).hexdigest(), 'database': database,
                'accessions': list(accessions)}

    def _blast_request(self, parameters, rid=None):
        rate = self.cache/'blast-rate.json'
        state = json.loads(rate.read_text()) if rate.exists() else {'last': -100, 'rids': {}}
        now = self.clock()
        if now-state['last'] < 10:
            raise WorkLimit('NCBI BLAST pacing: requests must be at least 10 seconds apart')
        if rid is not None and now-state['rids'].get(rid, -100) < 60:
            raise WorkLimit('NCBI BLAST pacing: polls for one RID must be at least 60 seconds apart')
        state['last'] = now
        if rid is not None:
            state['rids'][rid] = now
        rate.write_text(json.dumps(state))
        parameters.update({'EMAIL': self.email, 'TOOL': self.tool})
        text = self.transport('https://blast.ncbi.nlm.nih.gov/Blast.cgi', urlencode(parameters).encode())
        return text

    def submit(self, query_fasta, *, program='blastn', database='refseq_rna'):
        if program not in ('blastn', 'blastp') or not re.fullmatch(r'[A-Za-z0-9_]{1,64}', database):
            raise ValueError('blastn/blastp and a bounded database name required')
        records = fasta(query_fasta, size_limit=100000)
        if sum(map(len, records.values())) > 50000:
            raise WorkLimit('remote query limited to 50000 residues')
        text = self._blast_request({'CMD': 'Put', 'PROGRAM': program, 'DATABASE': database, 'QUERY': query_fasta})
        match = re.search(r'RID\s*=\s*([A-Z0-9-]+)', text)
        if not match:
            raise ValueError('NCBI did not return a BLAST request identifier')
        receipt = {'rid': match[1], 'program': program, 'database': database,
                   'query_sha256': sha256(query_fasta.encode()).hexdigest(), 'submitted': self.clock(),
                   'response': text, 'next_poll_seconds': 60}
        (self.cache/(match[1]+'.json')).write_text(json.dumps(receipt, indent=2))
        return receipt

    def retrieve(self, rid):
        if not re.fullmatch(r'[A-Z0-9-]{1,64}', rid):
            raise ValueError('valid BLAST request identifier required')
        text = self._blast_request({'CMD': 'Get', 'RID': rid, 'FORMAT_TYPE': 'Text', 'ALIGNMENT_VIEW': 'Tabular'}, rid=rid)
        # URL API tabular output need not include BTOP. Save it without claiming
        # acceptance by our strict custom BTOP importer; local BLAST+ supplies it.
        path = self.cache/(rid+'.tabular.txt'); path.write_text(text)
        return {'rid': rid, 'result_path': str(path), 'sha256': sha256(text.encode()).hexdigest(),
                'btop_import_ready': False, 'scope': 'raw URL API tabular response, potentially pending'}


def local_blast(query_path, subject_path, output_path, *, program='blastn', timeout=120, extra=()):
    if program not in ('blastn', 'blastp'):
        raise ValueError('blastn or blastp required')
    if extra:
        raise ValueError('arbitrary BLAST arguments unsupported; use a separate explicit BLAST invocation')
    binary = shutil.which(program)
    if binary is None:
        raise FileNotFoundError('Install NCBI BLAST+ and place '+program+' on PATH')
    if type(timeout) is not int or not 1 <= timeout <= 600:
        raise ValueError('timeout in 1..600 seconds required')
    query_path, subject_path, output_path = map(lambda p: Path(p).resolve(), (query_path, subject_path, output_path))
    if output_path in (query_path, subject_path):
        raise ValueError('output must differ from input FASTA paths')
    for path in (query_path, subject_path):
        fasta(path.read_text())
    version = subprocess.run([binary, '-version'], capture_output=True, text=True, check=True, timeout=10).stdout
    command = [binary, '-query', str(query_path), '-subject', str(subject_path), '-out', str(output_path),
               '-outfmt', '7 '+' '.join(FIELDS)]
    if program == 'blastn':
        command += ['-task', 'blastn', '-word_size', '7', '-dust', 'no']
    subprocess.run(command, capture_output=True, text=True, timeout=timeout, check=True)
    return {'command': command, 'version': version, 'query_sha256': sha256(query_path.read_bytes()).hexdigest(),
            'subject_sha256': sha256(subject_path.read_bytes()).hexdigest(),
            'output_sha256': sha256(output_path.read_bytes()).hexdigest(), 'result_path': str(output_path),
            'scope': 'NCBI BLAST+ heuristic candidate search, not exhaustive alignment discovery'}
