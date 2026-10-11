"""Offline explorer for batch mining receipts, with escaped source JSON."""
import json
import re
from pathlib import Path
from .blast_report import json_ready


def write_mining_report(receipt, output):
    if receipt.get('schema') != 'pp-blast-mining/2':
        raise ValueError('mining receipt required')
    payload = json.dumps(json_ready(receipt), sort_keys=True).replace('&', '\\u0026').replace('<', '\\u003c')
    def display(value):
        if type(value) is int and abs(value) > 2**53-1:
            return str(value)
        if isinstance(value, dict): return {k: display(v) for k,v in value.items()}
        if isinstance(value, (list, tuple)): return [display(v) for v in value]
        return value
    view = json.dumps(display(json_ready(receipt)), sort_keys=True).replace('&', '\\u0026').replace('<', '\\u003c')
    template = Path(__file__).with_name('blast_data').joinpath('mining.html').read_text()
    rendered = re.sub('__MINING_RECEIPT__|__RAW_RECEIPT__',
                      lambda match: view if match.group() == '__MINING_RECEIPT__' else payload, template)
    Path(output).write_text(rendered, encoding='utf-8')
    return str(Path(output).resolve())
