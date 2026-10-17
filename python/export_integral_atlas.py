"""Export actual E8 coordinates and integer branch geometry for the atlas.

Membership, adjacency, and Coxeter actions are exact. The displayed Fourier
projection is floating point and is explicitly separate from those checks.
"""
import hashlib
import json
from math import cos, sin, pi, hypot, gcd
from pathlib import Path
from perfectpower import e8_periods as e8

ROOT = Path(__file__).resolve().parents[1]


def project(root, exponent):
    point = root
    real = imaginary = 0.0
    for k in range(30):
        angle = 2*pi*exponent*k/30
        real += point[0]*cos(angle)
        imaginary += point[0]*sin(angle)
        point = e8.coxeter_action(point)
    return real, imaginary


def build():
    orbits = e8.root_orbits()
    ordered = [root for orbit in orbits for root in orbit]
    index = {root: i for i, root in enumerate(ordered)}
    xy = [project(root, 1) for root in ordered]
    depth = [project(root, 7)[0] for root in ordered]
    scale = max(hypot(x, y) for x, y in xy)
    zscale = max(abs(z) for z in depth)
    rows = []
    for i, root in enumerate(ordered):
        neighbors = [j for j, other in enumerate(ordered) if sum(a*b for a,b in zip(root,other)) == 4]
        assert len(neighbors) == 56 and sum(a*a for a in root) == 8
        x, y = xy[i]
        following = index[e8.coxeter_action(root)]
        assert following == (i//30)*30+(i+1)%30
        xx, yy = xy[following]
        angle = 2*pi/30
        assert abs(xx-(x*cos(angle)+y*sin(angle))) < 1e-10
        assert abs(yy-(-x*sin(angle)+y*cos(angle))) < 1e-10
        rows.append(dict(id=i, orbit=i//30, step=i%30, doubled_root=list(root),
                         x=round(x/scale,12), y=round(y/scale,12), z=round(depth[i]/zscale,12),
                         next=following, neighbors=neighbors))
    branches = [dict(index=j, exponent=1+1680*j, primitive=gcd(1+1680*j,443520)==1)
                for j in range(264)]
    assert sum(row['primitive'] for row in branches) == 240
    radii = [hypot(rows[i*30]['x'],rows[i*30]['y']) for i in range(8)]
    assert len({round(r,8) for r in radii}) == 8
    payload = dict(schema='pp-integral-atlas-data/1', roots=rows, orbit_radii=radii,
                   branches=branches, root_count=240, adjacency_pairs=6720,
                   projection='Fourier exponent 1 Coxeter plane; optional real exponent 7 depth. Normalized floating-point display coordinates.',
                   scope='The 240 primitive branches and the 240 E8 roots are different objects; the atlas defines no bijection between them.',
                   exact_sources=['python/perfectpower/e8_periods.py','receipts/period_bridge_deep/e8_lift.json',
                                  'receipts/period_bridge_deep/coxeter.json'],
                   source_sha256={path:hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in
                                  ('python/export_integral_atlas.py','python/perfectpower/e8_periods.py',
                                   'receipts/period_bridge_deep/e8_lift.json','receipts/period_bridge_deep/coxeter.json')})
    raw=json.dumps(payload,sort_keys=True,separators=(',',':'))
    envelope=dict(schema='pp-integral-atlas/1',payload_json=raw,payload_sha256=hashlib.sha256(raw.encode()).hexdigest())
    target=ROOT/'web/integral-families/atlas-data.json'
    target.write_text(json.dumps(envelope,sort_keys=True,indent=2)+'\n')
    result = dict(roots=240,orbits=8,adjacency_pairs=6720,branches=264,primitive=240,payload_sha256=envelope['payload_sha256'])
    sources = ['python/export_integral_atlas.py','python/build_resonance_downloads.py',
               'python/tests/test_resonance_scene.mjs','python/tests/test_resonance_shaders.py'] + ['web/integral-families/'+name for name in
               ('index.html','atlas.html','atlas.js','atlas-model.js','atlas.css','calculator.html',
                'resonance.jsx','resonance-math.jsx','resonance-scene.js','resonance-effects.js','resonance-layout.js','inline-fragment.html','resonance.css','build-resonance.mjs','package.json','resonance.bundle.js','resonance.bundle.js.LEGAL.txt')]
    receipt = dict(schema='pp-spectral-atlas/1', title='The 384–264 Resonance', geometry=result,
                   url='https://perfectpower-explorer-download.towre676.chatgpt.site/integrals/',
                   calculator_url='https://perfectpower-explorer-download.towre676.chatgpt.site/integrals/calculator.html',
                   chapters=['framework','phase resonance','higher structure motif','nerve motif'],
                   runtime=dict(react='19.2.6',three='0.186.1',autonomous=True,mode_duration_seconds=18,
                                interruptible_transitions=True,focus_inspection=True,adaptive_quality=True,
                                root_neighbors=56,root_step_seconds=1.6,background_grid=[37,29],cinema_first=True,luminous_node_surfaces=5,
                                volumetric_torus_strands=12,interference_discs=5,braid_strands=6,simplex_membranes=10,
                                math_visible_by_default=True,scene_linked_identities=4,math_node_annotations=5,
                                semantic_mathml=True,visible_root_coordinates=True),
                   atlas_url='https://perfectpower-explorer-download.towre676.chatgpt.site/integrals/atlas.html',
                   monograph='docs/PERIOD_BRIDGE_DEEP_MONOGRAPH.md',
                   scope='Exact underlying geometry and integer arithmetic; floating-point projections and curves. No identification of distinct 240-element objects.',
                   source_sha256={p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sources})
    (ROOT/'receipts/period_bridge_deep/atlas.json').write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n')
    names=('index.html','atlas.html','atlas.js','atlas-model.js','atlas.css','atlas-data.json','calculator.html',
           'resonance.bundle.js','resonance.bundle.js.LEGAL.txt','resonance.css')
    assets={name:(ROOT/'web/integral-families'/name).read_text() for name in names}
    dedicated=dict(schema='pp-integral-atlas-web/1',assets=assets,
                   hashes={name:hashlib.sha256(raw.encode()).hexdigest() for name,raw in assets.items()})
    (ROOT/'data/integral_atlas_web.json').write_text(json.dumps(dedicated,sort_keys=True,indent=2)+'\n')
    return result


if __name__ == '__main__':
    print(json.dumps(build()))
