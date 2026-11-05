#!/usr/bin/env python3
"""Stream the Python campaign's spill frontier: verify the manifest
accounting (exact + sum lo = floor, exact + sum hi = ceiling) and
collect width/depth statistics."""
import pickle, json, collections, sys
from pathlib import Path
spill = Path('/home/hatch/workspace/research/closures/petersen50_count/spill')
man = json.loads((spill/'manifest.json').read_text())
files = ['ram_heap.pkl'] + man['spill_files']
tot = 0; slo = 0; shi = 0
width_hist = collections.Counter()
depth_hist = collections.Counter()
maxwidth = 0
for fn in files:
    with open(spill/fn, 'rb') as f:
        nodes = pickle.load(f)
    for (nw, nd, used, lo, hi) in nodes:
        w = hi - lo
        tot += 1; slo += lo; shi += hi
        if w > maxwidth: maxwidth = w
        width_hist[w.bit_length()] += 1
        depth_hist[-nd] += 1
    del nodes
exact = man['exact']
print('nodes_total', tot)
print('exact + sum_lo =', exact + slo, ' manifest floor   =', man['floor'], ' match:', exact + slo == man['floor'])
print('exact + sum_hi =', exact + shi, ' manifest ceiling =', man['ceiling'], ' match:', exact + shi == man['ceiling'])
print('width', man['ceiling'] - man['floor'], 'max node width', maxwidth)
print('width bit-length hist (bit_length -> count):', dict(sorted(width_hist.items())))
print('depth hist:', dict(sorted(depth_hist.items())))
json.dump({'nodes_total': tot, 'sum_lo': slo, 'sum_hi': shi,
           'floor_match': exact + slo == man['floor'],
           'ceiling_match': exact + shi == man['ceiling'],
           'max_width': maxwidth,
           'width_bitlen_hist': {str(k): v for k, v in width_hist.items()},
           'depth_hist': {str(k): v for k, v in depth_hist.items()}},
          open('/home/hatch/workspace/research/expansions/petersen50_c/spill_census.json', 'w'), indent=1)
