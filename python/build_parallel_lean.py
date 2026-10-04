"""Reproduce exact Lean fixtures from parallel-session receipts (no numeric promotion)."""
import hashlib
import json
import pathlib
from fractions import Fraction

ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = ROOT / 'PerfectPower/Generated'

def matrix(rows):
    def scalar(x):
        q = Fraction(str(x))
        return str(q.numerator) if q.denominator == 1 else f'({q.numerator}/{q.denominator})'
    return '!![' + ';\n'.join(','.join(map(scalar, row)) for row in rows) + ']'

def generate():
    OUT.mkdir(exist_ok=True)
    sources = {}
    def read(name):
        data = (ROOT / name).read_bytes()
        sources[name] = hashlib.sha256(data).hexdigest()
        return json.loads(data)
    for name in ['recovery_sources/deep_gems/PSG_Q_U_L_Z.txt','recovery_sources/deep_gems/PSG_Qtilde_W_L_Z.txt']:
        sources[name] = hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
    header = 'import PerfectPower.WeightedHodge\nimport PerfectPower.SymplecticTransport\nnamespace PerfectPower.ParallelCertificates\nopen Matrix\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n'
    text = header
    paths = sorted((ROOT / 'receipts/symplectic_periods').glob('*.json'))
    count = 0
    for path in paths:
        obj = read(str(path.relative_to(ROOT)))
        if not isinstance(obj, dict) or 'basis' not in obj:
            continue
        b = obj['basis']
        if not all(k in b for k in ['intersection_matrix','basis_columns','inverse_basis','standard_intersection']):
            continue
        name = 'surface_' + path.stem
        n = len(b['basis_columns'])
        for letter, key in [('O','intersection_matrix'),('S','basis_columns'),('I','inverse_basis'),('J','standard_intersection')]:
            text += f'def {name}_{letter} : Matrix (Fin {n}) (Fin {n}) ℤ := {matrix(b[key])}\n'
        o,s,i,j = [name+'_'+k for k in ['O','S','I','J']]
        text += f'theorem {name}_checked : {s}*{i}=1 ∧ {i}*{s}=1 ∧ {s}.transpose*{o}*{s}={j} ∧ {o}.transpose = -{o} := by decide +kernel\n'
        count += 1
    text += 'end PerfectPower.ParallelCertificates\n'
    (OUT/'ParallelSurfaceCertificates.lean').write_text(text)
    models = read('receipts/deep_gems/weighted_hodge.json')['models']
    hodge_modules = []
    for model in models:
        g = model['genus']; n = len(model['harmonic_projector']); name=f'hodge_{g}'
        text=header
        for letter,key in [('G','gradient_projector'),('B','boundary_projector'),('H','harmonic_projector'),('L','laplacian')]:
            text += f'def {name}_{letter} : Matrix (Fin {n}) (Fin {n}) ℚ := {matrix(model[key])}\n'
        G,B,H,L=[name+'_'+k for k in ['G','B','H','L']]
        text+=f'def {name}_M : Matrix (Fin {n}) (Fin {n}) ℚ := Matrix.diagonal (fun i => (i.val+3 : ℚ))\n'
        checks = [f'{G}*{G}={G}', f'{B}*{B}={B}', f'{G}*{B}=0', f'{B}*{G}=0', f'{G}+{B}+{H}=1', f'{L}*{H}=0', f'{H}.transpose*{name}_M={name}_M*{H}', f'Matrix.trace {H}={2*g}']
        if g >= 4:
            if g == 7:
                text += f'theorem {name}_gradient_zero : {G}=0 := by decide +kernel\n'
            data_name = f'WeightedHodge{g}Data'
            (OUT/(data_name+'.lean')).write_text(text+'end PerfectPower.ParallelCertificates\n')
            hodge_modules.append('Generated/'+data_name)
            imports = []
            aggregate = ''
            for k, check in enumerate(checks[:-1]):
                left, right = check.split('=')
                if right in ('0','1'): right=f'({right} : Matrix (Fin {n}) (Fin {n}) ℚ)'
                for start in range(0,n,5):
                    chunk_name=f'WeightedHodge{g}Part{k}Rows{start}'
                    chunk=f'import PerfectPower.Generated.{data_name}\nnamespace PerfectPower.ParallelCertificates\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n'
                    for i in range(start,min(start+5,n)):
                        proof = 'by\n  intro j\n  fin_cases j <;> decide +kernel' if g == 7 else 'by decide +kernel'
                        if g == 7 and k in (0,2,3):
                            proof = f'by simp [{name}_gradient_zero]'
                        if g == 7 and k == 6:
                            proof = f'by\n  simp only [{name}_M, Matrix.mul_diagonal, Matrix.diagonal_mul]\n  intro j\n  fin_cases j <;> decide +kernel'
                        chunk += f'theorem {name}_row_{k}_{i} : ∀ j, ({left}) {i} j = ({right}) {i} j := {proof}\n'
                    chunk += 'end PerfectPower.ParallelCertificates\n'
                    (OUT/(chunk_name+'.lean')).write_text(chunk)
                    hodge_modules.append('Generated/'+chunk_name)
                    imports.append(f'import PerfectPower.Generated.{chunk_name}\n')
                aggregate += f'theorem {name}_part_{k} : {check} := by\n  ext i j\n  fin_cases i\n'
                for i in range(n): aggregate += f'  · exact {name}_row_{k}_{i} j\n'
            text=''.join(imports)+'namespace PerfectPower.ParallelCertificates\nopen Matrix\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n'+aggregate
            text += f'theorem {name}_part_7 : {checks[7]} := by decide +kernel\n'
            text += f'theorem {name}_checked : ' + ' ∧ '.join(checks) + ' := by\n  exact ⟨' + ','.join(f'{name}_part_{i}' for i in range(8)) + '⟩\n'
        else:
            text += f'theorem {name}_checked : ' + ' ∧ '.join(checks) + ' := by decide +kernel\n'
        text+=f'theorem {name}_idempotent : {H}*{H}={H} := by\n  have hc := {name}_checked\n  have he : {H}=1-{G}-{B} := by rw [← hc.2.2.2.2.1]; abel\n  rw [he]\n  exact (PerfectPower.WeightedHodge.harmonic_projector {G} {B} hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1).1\n'
        text+='end PerfectPower.ParallelCertificates\n'
        (OUT/f'WeightedHodge{g}.lean').write_text(text)
        hodge_modules.append(f'Generated/WeightedHodge{g}')
    # Check the newly stored literal packets against the prior literal outer packets.
    import re
    outer_path = 'receipts/divisor_sum/CompleteQuartics.lean'
    data = (ROOT / outer_path).read_bytes()
    sources[outer_path] = hashlib.sha256(data).hexdigest()
    matches = re.findall(r'theorem curve_(\d+)_packet : curve_\d+ = (.*?) := by decide \+kernel', data.decode())
    packets = {int(i): packet for i, packet in matches}
    pulls = read('receipts/deep_gems/quartic_pullbacks.json')['rows']
    commands = re.findall(r'native_(linear_perturbation|square_leading_quartic) curve_\d+ for ([^\n]+)', data.decode())
    assert len(commands) == 3080
    registry = 'import PerfectPower.QuarticPowerAtlas\nnamespace PerfectPower.Generated.QuarticPowerRegistry\nopen QuarticPowerAtlas\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\ndef cases : List Case := [\n'
    entries=[]
    for mode, params in commands:
        values = [int(v.strip()) for v in params.split(',')]
        assert len(values) == 5
        entries.append('⟨'+str(mode == 'square_leading_quartic').lower()+','+','.join(map(str,values))+'⟩')
    registry += ',\n'.join(entries)+']\n\n'
    registry += 'theorem all_valid : cases.all (fun C => decide (valid C))=true := by decide +kernel\n\n'
    registry += 'theorem complete (C : Case) (hc : C ∈ cases) (q : ℕ) (hq : q ≠ 0) (x y : ℤ) :\n    y^2=value C (x^q) ↔ (x,y) ∈ PowerComposition.lift (outer C) q := by\n  apply QuarticPowerAtlas.complete C ?_ q hq x y\n  exact of_decide_eq_true ((List.all_eq_true.mp all_valid) C hc)\nend PerfectPower.Generated.QuarticPowerRegistry\n'
    (OUT/'QuarticPowerRegistry.lean').write_text(registry)
    assert len(packets) == 3080 and len(pulls) == 6160
    for row in pulls:
        mode, params = commands[row['source_row']]
        L,a,b,c,d = [int(v.strip()) for v in params.split(',')]
        expected = [d,c,b,a,L*L] if mode == 'square_leading_quartic' else [b*b+d,2*a*b+c,a*a+2*L*b,2*L*a,L*L]
        assert row['outer_coefficients'] == expected, row
        assert row['degree'] == 4*row['power']
    packet_files = []
    for start in range(0, len(pulls), 200):
        name = f'QuarticLiftPackets{start//200:02d}'
        text = 'import PerfectPower.PowerComposition\nnamespace PerfectPower.ParallelCertificates\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n'
        for idx, row in enumerate(pulls[start:start+200], start):
            outer = packets[row['source_row']]
            pts = '{' + ','.join(f'({int(x)},{int(y)})' for x,y in row['points']) + '}' if row['points'] else '∅'
            text += f'theorem lift_packet_{idx:04d} : PerfectPower.PowerComposition.lift ({outer} : Finset (ℤ × ℤ)) {row["power"]} = {pts} := by decide +kernel\n'
        text += 'end PerfectPower.ParallelCertificates\n'
        (OUT / (name+'.lean')).write_text(text)
        packet_files.append(name)
    receipt={'schema':'parallel-lean-inputs/1','source_sha256':sources,'surface_certificates':count,'literal_lift_packets':len(pulls),'packet_modules':packet_files,'hodge_genera':[m['genus'] for m in models],'scope':'Exact matrix identities only; numerical periods and identification with smooth-curve homology are not certified.'}
    affine_rows=read('receipts/enhanced_machinery/corpus.json')['rows']
    plain_lookup={(r['source_row'],r['power']):r['points'] for r in pulls}
    affine_rows_selected=[]
    for row in affine_rows:
        assert row['power'] in (2,3) and 0 <= row['source_row'] < 3080
        if row['variant']=='plain':
            assert row['affine']==[1,0] and row['points']==plain_lookup[row['source_row'],row['power']]
        else:
            assert row['variant']=='affine' and row['affine'][0]!=0
            affine_rows_selected.append(row)
    assert len(affine_rows)==12320 and len(affine_rows_selected)==6160
    affine_packet_files=[]
    for start in range(0,len(affine_rows_selected),200):
        name=f'AffineQuarticPackets{start//200:02d}'
        text='import PerfectPower.AffinePowerComposition\nnamespace PerfectPower.ParallelCertificates\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n'
        for idx,row in enumerate(affine_rows_selected[start:start+200],start):
            a,b=row['affine'];outer=packets[row['source_row']]
            pts='{' + ','.join(f'({int(x)},{int(y)})' for x,y in row['points']) + '}' if row['points'] else '∅'
            text+=f'theorem affine_packet_{idx:04d} : PerfectPower.AffinePowerComposition.lift ({outer} : Finset (ℤ × ℤ)) {row["power"]} ({a}) ({b}) 1 = {pts} := by decide +kernel\n'
        text+='end PerfectPower.ParallelCertificates\n'
        (OUT/(name+'.lean')).write_text(text)
        affine_packet_files.append(name)
    receipt['affine_lift_packets']=len(affine_rows_selected)
    receipt['enhanced_corpus_queries']=len(affine_rows)
    core = ['WeightedHodge','PowerComposition','DivisorCoordinates','PolyhedralVoronoi','SymplecticTransport','FiniteWeilAlgebra','PowerSumRecovery','PSGRecovery','QuarticPowerAtlas','CanonicalMetric','AffinePowerComposition','ResidueCover','IntegerOptimization']
    modules = core + ['Generated/QuarticPowerRegistry','Generated/ParallelSurfaceCertificates'] + hodge_modules + ['Generated/'+p for p in packet_files] + ['AffineQuarticAtlas'] + ['Generated/'+p for p in affine_packet_files]
    audit = ''.join('import PerfectPower.'+m.replace('/','.')+'\n' for m in modules)
    declarations = []
    direct = []
    bundles = []
    for module in modules:
        src=(ROOT/'PerfectPower'/(module+'.lean')).read_text()
        ns=re.search(r'^namespace (\S+)',src,re.M).group(1)
        names=[ns+'.'+name for name in re.findall(r'^theorem (\w+)',src,re.M)]
        declarations.extend(names)
        if module.split('/')[-1] in packet_files + affine_packet_files:
            bundles.append((module.split('/')[-1],names))
        else:
            direct.extend(names)
    audit+='namespace PerfectPower.ParallelAxiomBundles\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
    for name,names in bundles:
        audit+=f'def {name} : List (PSigma fun P : Prop => P) := [\n'
        audit+=',\n'.join('⟨_,'+n+'⟩' for n in names)+']\n'
    audit+='end PerfectPower.ParallelAxiomBundles\n'
    printed=direct+['PerfectPower.ParallelAxiomBundles.'+name for name,_ in bundles]
    audit+=''.join('#print axioms '+name+'\n' for name in printed)
    receipt['audited_groups']=len(printed)
    receipt['axiom_strategy']='Every theorem directly audited or stored as an actual proof term in an audited PSigma list; exact-name coverage checked.'
    (ROOT/'audit/ParallelPush.lean').write_text(audit)
    receipt['modules']=modules
    receipt['audited_declarations']=len(declarations)
    receipt['generated_source_sha256']={m:hashlib.sha256((ROOT/'PerfectPower'/(m+'.lean')).read_bytes()).hexdigest() for m in modules}
    dest=ROOT/'receipts/parallel_lean';dest.mkdir(exist_ok=True)
    (dest/'inputs.json').write_text(json.dumps(receipt,indent=2)+'\n')

if __name__ == '__main__':
    generate()
