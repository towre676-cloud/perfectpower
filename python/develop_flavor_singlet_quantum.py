"""Replay fermion counterterms, matching and fixed-spectrum orbit results."""
from pathlib import Path
import json
from perfectpower.flavor_singlet_quantum import (exact_fermion_counterterms,
    exact_portal_regeneration,non_gaussian_matching_certificate,fixed_spectrum_orbit_certificate,
    non_gaussian_vacuum_extension)

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'receipts/m22_interactions'

def build():
    old=json.loads((OUT/'flavor_singlet_mediation.json').read_text())
    return {'fermion_counterterms':exact_fermion_counterterms(),
            'scalar_portal_regeneration':exact_portal_regeneration(),
            'non_Gaussian_matching':non_gaussian_matching_certificate(),
            'non_Gaussian_local_extension':non_gaussian_vacuum_extension(),
            'fixed_spectrum_orbits':fixed_spectrum_orbit_certificate(old['singlet_finite_UV']),
            'reference':{'author':'Stephen P. Martin','arxiv':'hep-ph/0111209','equations':'1.1-1.3, 3.3-3.4',
                         'url':'https://arxiv.org/abs/hep-ph/0111209'},
            'scope':'Fermion determinant contribution, one specified scalar regeneration channel and general classical singlet matching. Not full gauge/Yukawa/EFT running or a golden-frame selection.'}

if __name__=='__main__':
    destination=OUT/'flavor_singlet_quantum.json'
    destination.write_text(json.dumps(build(),indent=2,sort_keys=True)+'\n')
    print(destination)
