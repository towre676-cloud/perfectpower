"""Reproduce the exact spectral census, compressed plans and native worked sources."""
import json,gzip,hashlib,zipfile
from pathlib import Path
from math import lcm
from perfectpower import weil_spectral as W
from perfectpower import weil_commutant as C
from perfectpower.native_weil_spectral import native_spectral
ROOT=Path(__file__).resolve().parents[1]
def main():
    out=ROOT/'receipts/weil_spectral';out.mkdir(parents=True,exist_ok=True)
    original=json.loads((ROOT/'receipts/weil_commutant/summary.json').read_text())
    dims={r['level']:r['dimension'] for r in original['dimensions']}
    packets=[];records=[];total=0
    for n in range(2,65):
        p=W.spectral_packet(n);assert p['dimension']==dims[n]
        projects=W._spectral(n)[3]
        for E in projects:
            den=lcm(*(x.denominator for row in E for x in row))
            assert C._check_basis(n,[tuple(tuple(int(x*den) for x in row) for row in E)])
        total+=len(projects);packets.append(p)
        records.append({'level':n,'dimension':p['dimension'],'ranks':[r['rank'] for r in p['blocks']]})
        print(n,p['dimension'],records[-1]['ranks'],flush=True)
    raw=json.dumps(packets,separators=(',',':'),sort_keys=True).encode()
    # Text receipt keeps GitHub publishing and diffs simple; no opaque matrix archive.
    (out/'complete_packets.json').write_bytes(raw+b'\n')
    plans=[W.decomposition_plan(n) for n in [81,125,128,243,256,343,512,625,729,1024,3125,1000000]]
    (out/'compressed_plans.json').write_text(json.dumps(plans,indent=2)+'\n')
    native=out/'native';native.mkdir(exist_ok=True);names=[];sources=[]
    for n in (3,4,8,9):
        packet=native_spectral(n);path=native/f'Level{n}.lean';path.write_text(packet['lean_source'])
        names.extend(packet['declarations']);sources.append({'level':n,'path':str(path.relative_to(ROOT)),'sha256':hashlib.sha256(path.read_bytes()).hexdigest()})
    generic=[]
    for line in (ROOT/'PerfectPower/WeilSpectral.lean').read_text().splitlines():
        if line.startswith('theorem '):generic.append('PerfectPower.WeilSpectral.'+line.split()[1])
    audit=ROOT/'audit/WeilSpectral.lean'
    audit.write_text('import PerfectPower.WeilSpectral\n'+''.join(f'#print axioms {name}\n' for name in generic))
    (out/'native_declarations.json').write_text(json.dumps({'generic':generic,'native':names,'sources':sources},indent=2)+'\n')
    summary={'schema':'pp-weil-spectral-census/1','levels':63,'maximum_dense_level':64,'projectors':total,
             'exact_original_fourier_chirp_checks':True,'all_rational_algebra_identities_checked':True,
             'dimensions_compared_to_prior_certified_census':True,'packet_sha256':hashlib.sha256(raw).hexdigest(),
             'records':records,'generic_declarations':len(generic),'native_declarations':len(names),
             'native_levels':[3,4,8,9],'kernel_checked':False,
             'all_level_Lean_orbit_classification':False,
             'all_level_scope':'Paper commutativity and recursive rational primitive decomposition; bounded Python construction through 1000000.'}
    (out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print('Exact projectors:',total,'Generic:',len(generic),'Native:',len(names),flush=True)
if __name__=='__main__':main()
