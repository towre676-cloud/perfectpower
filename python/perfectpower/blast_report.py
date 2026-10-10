"""Offline interactive atlas rendered from exact Python-generated receipts."""
import json
from fractions import Fraction
from pathlib import Path


def json_ready(value):
    if isinstance(value, Fraction):
        return str(value)
    if isinstance(value, dict):
        return {str(k): json_ready(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [json_ready(v) for v in value]
    return value


def write_report(receipt, output):
    from .blast_machinery import soe_packet, motif_machine, similarity_geometry
    from .blast_alignment import AlignmentFamily
    receipt = dict(receipt)
    if 'family' not in receipt or 'plane' not in receipt:
        raise ValueError('report requires an align or demonstration receipt with family and plane')
    family = AlignmentFamily(receipt['family']['query'], receipt['family']['subject'])
    if family.packet() != receipt['family']:
        raise ValueError('supplied family receipt does not match its source sequences')
    receipt['representatives'] = {','.join(map(str, f)): family.select(f) for f in family.terms}
    if 'soe' not in receipt:
        receipt['soe'] = soe_packet(motif_machine(['AC', 'CG'])[0])
    if 'geometry' not in receipt:
        receipt['geometry'] = similarity_geometry(3, [(0, 1, 1, 1), (1, 2, 1, 1), (0, 2, 1, -1)])
    payload = json.dumps(json_ready(receipt), sort_keys=True, allow_nan=False).replace('<', '\\u003c').replace('&', '\\u0026')
    template = Path(__file__).with_name('blast_data').joinpath('atlas.html').read_text()
    Path(output).write_text(template.replace('__ATLAS_DATA__', payload))
    return str(Path(output).resolve())
