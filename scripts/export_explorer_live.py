#!/usr/bin/env python3
"""Regenerate deterministic public application receipts and the live data feed."""
import hashlib
import json
import subprocess
import sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'python'))
from perfectpower.research_counting import MonomialPopulation, ResiduePopulation, digit_sumset


def export(root=ROOT):
    root = Path(root)
    applications, identities = [], {}
    receipts = root / 'receipts/research_counting'
    receipts.mkdir(parents=True, exist_ok=True)
    for name in ('monomial', 'crt', 'digits'):
        relative = 'examples/research_counting/' + name + '.json'
        raw = (root / relative).read_bytes()
        identities[relative] = hashlib.sha256(raw).hexdigest()
        spec = json.loads(raw)
        if name == 'monomial':
            result = MonomialPopulation(spec['generators'], spec.get('degree')).packet(spec.get('ranks', []), spec.get('histogram', False))
        elif name == 'crt':
            result = ResiduePopulation(spec['lo'], spec['hi'], spec['constraints']).packet(spec.get('ranks', []))
        else:
            result = digit_sumset(spec)
        result['input_sha256'] = identities[relative]
        (receipts / (name + '.json')).write_text(json.dumps(result, sort_keys=True, indent=2) + '\n')
        applications.append({'id': name, 'title': {'monomial': 'Monomial degree populations', 'crt': 'CRT integer populations', 'digits': 'Distinct restricted-digit sums'}[name],
                             'input_path': relative, 'input': spec, 'input_json': raw.decode('utf8'), 'result': result})
    payload = {'schema': 'pp-research-applications/1', 'release': 'research-counting-live-1',
               'applications': applications, 'source_inputs': identities,
               'monograph': 'https://github.com/towre676-cloud/perfectpower/blob/main/docs/RESEARCH_COUNTING_LIVE_MONOGRAPH.md',
               'historical_benchmark': {'status': 'recovered aggregate only; original fresh raw receipts unavailable',
                                       'instances': 200, 'budget_seconds': 5,
                                       'exact': {'perfectpower_0102': 18, 'paired_0101': 12, 'ganak': 18, 'd4': 19},
                                       'independently_replayable_from_this_feed': False}}
    portfolio_input='examples/planning/petersen_50_population.json'
    portfolio_receipt='receipts/planning/explorer/validation.json'
    payload['native_portfolio']={'title':'Petersen 50-project portfolios', 'workspace':'portfolio',
        'input_path':portfolio_input,'input_sha256':hashlib.sha256((root/portfolio_input).read_bytes()).hexdigest(),
        'validation':json.loads((root/portfolio_receipt).read_text()),
        'monograph':'https://github.com/towre676-cloud/perfectpower/blob/main/docs/PORTFOLIO_EXPLORER_MONOGRAPH.md',
        'requires_native_upgrade':True,'browser_six_item_demo_is_same_engine':False,
        'geometry':{'url':'https://perfectpower-explorer-download.towre676.chatgpt.site/geometry/','schema':'pp-portfolio-geometry/1',
                    'receipt':json.loads((root/'receipts/planning/explorer/geometry.json').read_text()),
                    'scope':'Browser companion displays retained exact computations; native workspace follows fresh queries.'}}
    verification=root/'receipts/planning/independent/verification.json'
    if verification.exists():
        payload['native_portfolio']['independent_confirmation']=json.loads(verification.read_text())
    transport=root/'receipts/arithmetic_transport/release.json'
    if transport.exists():
        payload['arithmetic_transport']={'title':'Paths under an arithmetic height ceiling',
            'workspace':'arithmetic-transport',
            'url':'https://perfectpower-explorer-download.towre676.chatgpt.site/arithmetic/',
            'result':json.loads(transport.read_text()),
            'monograph':'https://github.com/towre676-cloud/perfectpower/blob/main/docs/ARITHMETIC_HEIGHT_PAULI_MONOGRAPH.md',
            'native_engine_requires_upgrade':True}
    modes=root/'receipts/arithmetic_modes/release.json'
    if modes.exists():
        payload['arithmetic_modes']={'title':'Arithmetic interference microscope',
            'workspace':'arithmetic-modes',
            'url':'https://perfectpower-explorer-download.towre676.chatgpt.site/arithmetic/modes',
            'result':json.loads(modes.read_text()),
            'monograph':'https://github.com/towre676-cloud/perfectpower/blob/main/docs/ARITHMETIC_MODES_MONOGRAPH.md',
            'native_engine_requires_upgrade':True}
    encoded = json.dumps(payload, sort_keys=True, separators=(',', ':'))
    source_parent = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip()
    envelope = {'schema': 'pp-explorer-live/1', 'source_parent': source_parent,
                'payload_json': encoded, 'payload_sha256': hashlib.sha256(encoded.encode()).hexdigest()}
    target = root / 'data/explorer_live.json'
    target.write_text(json.dumps(envelope, sort_keys=True, indent=2) + '\n')
    return {'applications': len(applications), 'payload_sha256': envelope['payload_sha256'], 'source_parent': source_parent}


if __name__ == '__main__':
    print(json.dumps(export()))
