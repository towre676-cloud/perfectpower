"""Flavor-independent one-loop QED screening on equal-charge Dirac blocks.

This is a perturbative free-fermion contribution in model mass units, not
the physical hadronic conversion of alpha(0). The gauge boundary is input.
"""
import numpy as np
from scipy.integrate import quad


def photon_screening(momentum, masses, charge, colors=3):
    """Positive subtraction from inverse alpha at spacelike momentum Q.

    alpha_eff(Q)^-1 = alpha(0)^-1 - screening(Q), at one-loop accuracy.
    Each equal-charge Dirac eigenstate appears once, including heavy states.
    """
    masses=np.asarray(masses,float)
    if not np.all(np.isfinite(masses)) or np.any(masses<=0):
        raise ValueError('Positive finite Dirac masses required')
    if not np.isfinite(momentum) or momentum<0 or not np.isfinite(charge) or colors<=0:
        raise ValueError('Nonnegative finite momentum and positive multiplicity required')
    values=[quad(lambda x:x*(1-x)*np.log1p((momentum/m)**2*x*(1-x)),0,1,
                 epsabs=1e-12,epsrel=1e-12)[0] for m in masses]
    return float(2*colors*charge**2/np.pi*sum(values))


def logarithmic_threshold(masses, charge, matching_scale=1., colors=3):
    """Logarithmic inverse-alpha contribution relative to a fixed scale.

    The sign here corresponds to integration from matching_scale to masses;
    the full threshold convention and independent boundary must be specified.
    """
    masses=np.asarray(masses,float)
    if np.any(masses<=0) or not np.all(np.isfinite(masses)) or matching_scale<=0:
        raise ValueError('Positive finite masses and matching scale required')
    return float(2*colors*charge**2/(3*np.pi)*sum(np.log(matching_scale/masses)))


def determinant_log_threshold(y,vev,messenger_mass,charge,matching_scale=1.,colors=3):
    """All six-state logarithmic contributions; independent of Hermitian C."""
    return float(2*colors*charge**2/(3*np.pi)*
                 (6*np.log(matching_scale)-3*np.log(y*vev*messenger_mass)))
