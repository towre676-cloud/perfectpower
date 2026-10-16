"""Read the retained integral-family calculations through the existing console.

The summary is a data receipt. Loading it does not pretend that an installed
engine acquired new executable functionality or that a categorical claim was proved.
"""
import hashlib
import json
from pathlib import Path

SUMMARY_SCHEMA = 'pp-period-bridge/1'
DEFAULT_RECEIPT = Path('receipts/period_bridge/summary.json')
MONOGRAPH = 'https://github.com/towre676-cloud/perfectpower/blob/main/docs/PERIOD_BRIDGE_MONOGRAPH.md'


def read_summary(path):
    """Return the checked public summary and its identity without changing it."""
    path = Path(path)
    raw = path.read_bytes()
    summary = json.loads(raw)
    if not isinstance(summary, dict) or summary.get('schema') != SUMMARY_SCHEMA:
        raise ValueError('Expected a pp-period-bridge/1 integral-family summary')
    if not isinstance(summary.get('highlights', []), list):
        raise ValueError('Integral-family highlights must be a list')
    return summary, hashlib.sha256(raw).hexdigest()


def application(root):
    """Optional companion data; legacy finite-population records stay unchanged."""
    root = Path(root)
    path = root / DEFAULT_RECEIPT
    if not path.is_file():
        return None
    summary, digest = read_summary(path)
    return {
        'id': 'integral-families',
        'title': summary.get('title', 'Integral families'),
        'workspace': 'integral-families',
        'url': 'https://perfectpower-explorer-download.towre676.chatgpt.site/research#integral-families',
        'receipt_path': DEFAULT_RECEIPT.as_posix(),
        'receipt_sha256': digest,
        'result': summary,
        'monograph': MONOGRAPH,
        'native_engine_requires_upgrade': True,
        'live_data_is_executable_upgrade': False,
    }


def receipt(path=None, details=False):
    if path is None:
        from .resources import runtime_root
        path = runtime_root() / DEFAULT_RECEIPT
    path = Path(path)
    if path.is_dir():
        path /= 'summary.json'
    summary, digest = read_summary(path)
    packet = {'schema': 'pp-integral-families/1', 'summary': summary,
              'receipt_path': str(path), 'receipt_sha256': digest}
    if details:
        results_path = path.with_name('results.json')
        raw = results_path.read_bytes()
        packet['results'] = json.loads(raw)
        packet['results_sha256'] = hashlib.sha256(raw).hexdigest()
    return packet


def explain(packet):
    summary = packet['summary']
    lines = [str(summary.get('title', 'Integral families')),
             str(summary.get('description', ''))]
    for item in summary.get('highlights', []):
        if isinstance(item, dict):
            heading = ': '.join(str(item[key]) for key in ('label', 'value') if key in item)
            lines.append(heading + ('. ' + str(item['detail']) if item.get('detail') else ''))
    for limit in summary.get('limits', []):
        lines.append(str(limit))
    return '\n\n'.join(line for line in lines if line)


def add_commands(sub):
    p = sub.add_parser('integral-families', help='inspect retained Raghava, cyclotomic and E8 integral-family results')
    p.add_argument('--receipt', type=Path, help='summary JSON or its containing directory; defaults to the retained release')
    p.add_argument('--details', action='store_true', help='include the complete sibling results.json')
    p.add_argument('--explain', action='store_true', help='show the short plain-language explanation')


def cli(args):
    if args.command != 'integral-families':
        return False
    packet = receipt(args.receipt, args.details)
    print(explain(packet) if args.explain else json.dumps(packet, sort_keys=True, indent=2))
    return True
