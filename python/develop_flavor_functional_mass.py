"""Reproduce the single-source hierarchy and operator boundary receipt."""
from pathlib import Path
import json
import numpy as np
from perfectpower.flavor_functional_mass import *
from perfectpower.flavor_hermitian import paired_vertex_reality
from perfectpower.flavor_quantum import scalar_threshold
ROOT=Path(__file__).resolve().parents[1]


def hermitian_basis(n=3):
    out=[np.diag(np.eye(n)[i]).astype(complex) for i in range(n)]
    for i in range(n):
        for j in range(i+1,n):
            r=np.zeros((n,n),complex);r[i,j]=r[j,i]=1/np.sqrt(2);out.append(r)
            r=np.zeros((n,n),complex);r[i,j]=1j/np.sqrt(2);r[j,i]=-1j/np.sqrt(2);out.append(r)
    return np.array(out)


def build_receipt():
    coefficients=[.101,0,-.002,0,.00001];C=np.diag([-10.,-20.,30.]);spectrum=functional_spectrum(C,1.,coefficients)
    rng=np.random.default_rng(441);X=rng.normal(size=(10,10));H=X.T@X+.2*np.eye(10)
    G=functional_vertices(C,.001*hermitian_basis(),coefficients,.05/30)
    mixed=np.einsum('ab,aij->bij',np.linalg.eigh(H)[1],G)
    threshold=scalar_threshold(spectrum['mass_matrix'],G,H)
    return {'exact_scalar_running_tensor':exact_cross_source_running_tensor(),'exact_source_multiplicities':exact_quadratic_source_multiplicities(),
            'exact_hierarchy':positive_quartic_certificate(),'charges_and_operator_space':charge_and_operator_certificate(),
            'functional_benchmark':{'masses':spectrum['masses'].tolist(),'heavy_mass_entries':spectrum['heavy_mass_eigenvalues'].tolist(),
                'light_doublet_weights_squared':np.diag(spectrum['doublet_frame'].conj().T@spectrum['doublet_frame']).real.tolist(),
                'diagonalization_residual':float(np.max(abs(spectrum['left'].conj().T@spectrum['mass_matrix']@spectrum['right']-np.diag(spectrum['masses'])))),
                'maximum_mixed_vertex_pair_imaginary_part':paired_vertex_reality(spectrum,mixed),
                'first_order_neutral_scalar_phase':threshold['delta_theta'],'UV_phase_coefficient':threshold['UV_phase_coefficient'],
                'relative_correction_norm':threshold['relative_correction_norm'],
                'scope':'Neutral-scalar first-order determinant phase and Hermitian seagull reality; full gauge/Yukawa EFT running and higher-loop phases are not computed.'},
            'fixed_spectrum_orientation':orientation_response(np.sqrt(np.diag(spectrum['doublet_frame'].conj().T@spectrum['doublet_frame']).real),np.sqrt(np.diag(spectrum['doublet_frame'].conj().T@spectrum['doublet_frame']).real)),
            'independent_high_precision_threshold':high_precision_wrong_source_phase(),
            'wrong_source_threshold':wrong_source_example(),'exact_wrong_source_resolvent':exact_wrong_source_resolvent_certificate()}

if __name__=='__main__':
    target=ROOT/'receipts/m22_interactions/flavor_functional_mass.json';target.write_text(json.dumps(build_receipt(),indent=2,sort_keys=True)+'\n');print(target)
