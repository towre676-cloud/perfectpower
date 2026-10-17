"""Export actual E8 coordinates and integer branch geometry for the atlas.

Membership, adjacency, and Coxeter actions are exact. The displayed Fourier
projection is floating point and is explicitly separate from those checks.
"""
import hashlib
import json
from math import cos, sin, pi, hypot, gcd
from pathlib import Path
from perfectpower import e8_periods as e8
from perfectpower import raghava_coxeter as rc
from fractions import Fraction
from math import comb

ROOT = Path(__file__).resolve().parents[1]



def calculation_data():
    phases=[dict(exponent=a,conductor=1680,image_exponent=a%30) for a in range(1680) if gcd(a,1680)==1]
    profiles={}
    for name,spectrum in [('reflection',rc.e8_reflection_spectrum()),('adjoint',rc.e8_adjoint_spectrum()),('induced_adjoint',rc.induce_spectrum(rc.e8_adjoint_spectrum(),264))]:
        moments=rc.moment_vector(spectrum,3)
        profiles[name]=dict(moments=list(map(str,moments)),mellin=list(map(str,rc.mellin_from_moments(moments))))
    traces=rc.reflection_trace_sequence(128)
    e=[Fraction(1),Fraction(0),Fraction(0)];sums=[Fraction(0)]*3
    root_sum=cartan_sum=Fraction(0);samples=[]
    c= e8.coxeter_matrix()
    c_traces=[sum(e8.matrix_power(c,k)[i][i] for i in range(8)) for k in range(30)]
    for n in range(1,129):
        for j in range(3):sums[j]+=e[j]*Fraction(traces[n],n*n*comb(2*n,n))
        root_sum+=Fraction(240 if n%30==0 else 0,n*n)
        cartan_sum+=Fraction(c_traces[n%30],n*n)
        samples.append(dict(n=n,trace=str(traces[n]),partial=list(map(float,sums)),root_mellin=float(root_sum),cartan_mellin=float(cartan_sum),adjoint_mellin=float(root_sum+cartan_sum),mellin_tail_bound=str(Fraction(248,n))))
        for j in (2,1):e[j]+=e[j-1]/(n*n)
    return dict(schema='pp-resonance-calculations/1',primitive_phases=phases,eigen_exponents=list(e8.EXPONENTS),profiles=profiles,coxeter_simple_basis=[list(row) for row in c],coxeter_traces=c_traces,series=samples,series_enclosures=[rc.reflection_partial(j,128,64) for j in range(1,4)],bernoulli_bridge=[list(map(str,row)) for row in rc.bernoulli_bridge_matrix(3)],phase_projection='(0.88 cos(2πq),0.88 sin(2πq),0.28 sin(14πq)); a real projection of (z,z^7), not a field embedding or isometry.',interpolation='Straight display interpolation between exact endpoints; no fractional-power identity.')


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
    studio_dir = ROOT/'web/integral-studio'
    studio_build = json.loads((studio_dir/'build-receipt.json').read_text())
    studio = dict(schema='pp-integral-studio/1', title='The Resonance Field',
                  url='https://perfectpower-explorer-download.towre676.chatgpt.site/integrals/',
                  entry_url='https://perfectpower-explorer-download.towre676.chatgpt.site/integrals/studio.html',
                  views=['integral','spectrum','fourier','energy'],
                  study_url='https://perfectpower-explorer-download.towre676.chatgpt.site/integrals/studio.html?study=1',
                  presentation=dict(default='full-screen cinematic',chapters=['connected field','264-fold lift','golden split','integral synthesis'],autonomous=True,chapter_seconds=27,bloom=True,mathematical_nodes=dict(primitive_1680=384,eigenphases=8,preimages_per_phase=48,fiber=264,primitive_fiber=240,e8_roots=240,e8_adjacencies=6720)),
                  basis=['log|Q+Q-|','log|Q+/Q-|','u^2','u^2(u+pi^2/2)'],
                  master='E(a,b,c,d)=integral_[−1,1](aA+bK+cP+dR)^2/sqrt(1-x^2) dx',
                  dependencies=studio_build['dependencies'],
                  analytic_gram_entries=10, analytic_gram_formalized_in_lean=False,
                  independent_quadrature=True, source_sha256=studio_build['source_sha256'],
                  mathematical_receipt_sha256=hashlib.sha256((studio_dir/'mathematics.json').read_bytes()).hexdigest(),
                  offline_sha256=studio_build['offline_sha256'],
                  offline_url='https://perfectpower-explorer-download.towre676.chatgpt.site/PerfectPower_Integral_Studio.html',
                  legacy_resonance='./resonance.html')
    unified=json.loads((ROOT/'receipts/period_bridge_deep/unification.json').read_text())
    formal=unified['formalization']
    for name, expected in formal['source_sha256'].items():
        assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==expected, 'Proof source changed after Lean checking'
    unification=dict(schema=unified['schema'], finite_lean_theorems=formal['theorem_count'],
                     finite_kernel_checked=formal['kernel_checked'],analytic_series_formalized=False,
                     reflection_first_moment='56/45',adjoint_first_moment='124/3',
                     refinement_degree=264,refined_dimension=65472,refined_first_moment='10912',
                     note_url='./unification.html',receipt_url='./unification.json')
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
        rows.append(dict(id=i, orbit=i//30, step=i%30, doubled_root=list(root), simple_coordinates=list(e8.simple_root_coordinates(root)),
                         x=round(x/scale,12), y=round(y/scale,12), z=round(depth[i]/zscale,12),
                         next=following, neighbors=neighbors))
    branches = [dict(index=j, exponent=1+1680*j, primitive=gcd(1+1680*j,443520)==1)
                for j in range(264)]
    assert sum(row['primitive'] for row in branches) == 240
    radii = [hypot(rows[i*30]['x'],rows[i*30]['y']) for i in range(8)]
    assert len({round(r,8) for r in radii}) == 8
    payload = dict(schema='pp-integral-atlas-data/1', roots=rows, orbit_radii=radii,unification=unification,studio=studio,calculations=calculation_data(),
                   branches=branches, root_count=240, adjacency_pairs=6720,
                   projection='Fourier exponent 1 Coxeter plane; optional real exponent 7 depth. Normalized floating-point display coordinates.',
                   scope='The 240 primitive branches and the 240 E8 roots are different objects; the atlas defines no bijection between them.',
                   exact_sources=['python/perfectpower/e8_periods.py','receipts/period_bridge_deep/e8_lift.json',
                                  'receipts/period_bridge_deep/coxeter.json'],
                   source_sha256={path:hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in
                                  ('python/export_integral_atlas.py','python/perfectpower/e8_periods.py',
                                   'receipts/period_bridge_deep/e8_lift.json','receipts/period_bridge_deep/coxeter.json','python/perfectpower/raghava_coxeter.py')})
    raw=json.dumps(payload,sort_keys=True,separators=(',',':'))
    envelope=dict(schema='pp-integral-atlas/1',payload_json=raw,payload_sha256=hashlib.sha256(raw.encode()).hexdigest())
    target=ROOT/'web/integral-families/atlas-data.json'
    target.write_text(json.dumps(envelope,sort_keys=True,indent=2)+'\n')
    result = dict(roots=240,orbits=8,adjacency_pairs=6720,branches=264,primitive=240,payload_sha256=envelope['payload_sha256'])
    sources = ['python/export_integral_atlas.py','python/build_resonance_downloads.py',
               'python/export_raghava_coxeter.py','python/check_raghava_coxeter_lean.py',
               'python/perfectpower/raghava_coxeter.py','python/tests/test_raghava_coxeter.py',
               'receipts/period_bridge_deep/unification.json','receipts/period_bridge_deep/unification_lean.json',
               'PerfectPower/PhaseFiber.lean','PerfectPower/CoxeterPhaseBridge.lean','PerfectPower/RaghavaInduction.lean',
               'python/tests/test_resonance_scene.mjs','python/tests/test_resonance_calculations.py','python/tests/test_resonance_shaders.py'] + ['web/integral-families/'+name for name in
               ('index.html','atlas.html','atlas.js','atlas-model.js','atlas.css','calculator.html',
                'resonance.jsx','resonance-model.js','resonance-calculations.jsx','resonance-math.jsx','resonance-scene.js','resonance-effects.js','resonance-layout.js','inline-fragment.html','resonance.css','build-resonance.mjs','package.json','resonance.bundle.js','resonance.bundle.js.LEGAL.txt','unification.html','unification-template.html','unification.json')]
    sources += ['web/integral-studio/'+p for p in ('CinematicExperience.jsx','CinematicScene.jsx','cinematic-geometry.mjs','cinematic-geometry.test.mjs','cinema.css','StudioApp.jsx','StudioScene.jsx','studio-geometry.mjs','studio-geometry.test.mjs','math-engine.mjs','math-engine.test.mjs','ui-model.mjs','ui-model.test.mjs','e8-roots.json','studio.css','studio.html','build-studio.mjs','verify-ui.mjs','mathematics.json','package.json','pnpm-lock.yaml','README.md','build-receipt.json')]
    sources += ['docs/INTEGRAL_STUDIO_MATHEMATICS.md','docs/INTEGRAL_STUDIO_MONOGRAPH.md','python/build_integral_studio_monograph.py']
    receipt = dict(schema='pp-spectral-atlas/1', title='The Resonance Field · Integral Studio', geometry=result,studio=studio,
                   url='https://perfectpower-explorer-download.towre676.chatgpt.site/integrals/',unification=unification,
                   calculator_url='https://perfectpower-explorer-download.towre676.chatgpt.site/integrals/calculator.html',
                   chapters=['connected field','264-fold lift','golden split','integral synthesis'],
                   study_views=['integral','spectrum','fourier','energy'],
                   resonance_url='https://perfectpower-explorer-download.towre676.chatgpt.site/integrals/resonance.html',legacy_chapters=['framework','phase resonance','higher structure motif','nerve motif'],
                   legacy_runtime=dict(react='19.2.6',three='0.186.1',autonomous=True,mode_duration_seconds=18,
                                interruptible_transitions=True,focus_inspection=True,adaptive_quality=True,
                                root_neighbors=56,root_step_seconds=1.6,background_grid=[37,29],cinema_first=True,luminous_node_surfaces=5,
                                volumetric_torus_strands=12,interference_discs=5,braid_strands=6,simplex_membranes=10,
                                math_visible_by_default=True,scene_linked_identities=4,math_node_annotations=5,
                                semantic_mathml=True,visible_root_coordinates=True,actual_phase_projections=True,phase_power_maps=[56,264],exact_coxeter_endpoints=True,inspectable_calculations=True),
                   atlas_url='https://perfectpower-explorer-download.towre676.chatgpt.site/integrals/atlas.html',
                   monograph='docs/PERIOD_BRIDGE_DEEP_MONOGRAPH.md',
                   scope='Exact underlying geometry and integer arithmetic; floating-point projections and curves. No identification of distinct 240-element objects.',
                   source_sha256={p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sources})
    (ROOT/'receipts/period_bridge_deep/atlas.json').write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n')
    names=('index.html','atlas.html','atlas.js','atlas-model.js','atlas.css','atlas-data.json','calculator.html',
           'resonance.bundle.js','resonance.bundle.js.LEGAL.txt','resonance.css','resonance.html','unification.html','unification.json',
           'studio.html','studio.bundle.js','studio.bundle.js.LEGAL.txt','studio.bundle.css','studio-mathematics.json')
    assets={name:(ROOT/'web/integral-families'/name).read_text() for name in names}
    dedicated=dict(schema='pp-integral-atlas-web/1',assets=assets,
                   hashes={name:hashlib.sha256(raw.encode()).hexdigest() for name,raw in assets.items()})
    (ROOT/'data/integral_atlas_web.json').write_text(json.dumps(dedicated,sort_keys=True,indent=2)+'\n')
    return result


if __name__ == '__main__':
    print(json.dumps(build()))
