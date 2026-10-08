"""UV-finite thermal relative determinant of the closed physical TE channel.

Dirichlet boxes use identical meshes for wall and vacuum subtraction. This
includes one vector polarization per species, not a gauge-fixed determinant
or a zero-temperature renormalized Coleman-Weinberg potential.
"""
from math import pi
import numpy as np
from scipy.linalg import eigh_tridiagonal


def planar_boson_free_energy(masses, temperature, *, terms=240):
    """T int d^2p/(2pi)^2 log(1-exp(-sqrt(p^2+a^2)/T)). GeV^3."""
    a=np.asarray(masses,float)
    if temperature<=0 or not np.isfinite(temperature) or np.any(a<0) or not np.all(np.isfinite(a)) or terms<2:raise ValueError('positive finite temperature, nonnegative masses and terms>=2 required')
    ratio=a/temperature;n=np.arange(1,terms+1,dtype=float)
    return -temperature**3/(2*pi)*np.sum(np.exp(-ratio[...,None]*n)*(ratio[...,None]/n**2+1/n**3),axis=-1)


def thermal_relative_determinant(z, mass_squared, vacuum_mass, temperature, *, terms=240):
    """Finite-difference relative TE free energy per unit area, GeV^3.

    Both endpoints impose Dirichlet boundary conditions. Compare grid spacings
    and box radii; no continuum or thermodynamic limit is asserted from one box.
    """
    z=np.asarray(z,float);V=np.asarray(mass_squared,float)
    if len(z)<5 or V.shape!=z.shape or vacuum_mass<=0 or not np.all(np.isfinite(V)):raise ValueError('resolved real mass profile and positive vacuum mass required')
    dz=np.diff(z)
    if min(dz)<=0 or not np.allclose(dz,dz[0],rtol=1e-10,atol=1e-15):raise ValueError('uniform increasing physical z mesh required')
    inv=1/dz[0]**2;n=len(z)-2
    eigen=eigh_tridiagonal(2*inv+V[1:-1],-inv*np.ones(n-1),eigvals_only=True)
    j=np.arange(1,n+1);free=vacuum_mass**2+4*inv*np.sin(pi*j/(2*(n+1)))**2
    if min(eigen)<0:raise ValueError('negative mode: a real equilibrium determinant is not defined')
    wall=planar_boson_free_energy(np.sqrt(eigen),temperature,terms=terms)
    vacuum=planar_boson_free_energy(np.sqrt(free),temperature,terms=terms)
    return {'relative_thermal_free_energy_per_area_GeV3':float(np.sum(wall-vacuum)),
            'temperature_GeV':float(temperature),'interior_nodes':n,'spacing_GeV_inverse':float(dz[0]),
            'half_box_GeV_inverse':float((z[-1]-z[0])/2),'lowest_wall_mass_GeV':float(np.sqrt(min(eigen))),
            'minimum_profile_mass_squared_above_vacuum_GeV2':float(min(V-vacuum_mass**2)),
            'scope':'One closed physical TE polarization; relative thermal contribution on a fixed zero-temperature wall. No longitudinal/mixed gauge sector, ghosts, Debye resummation, vacuum counterterms, bounce or nucleation update.'}


def candidate_thermal_vectors(solution, temperature, *, g=.65, gprime=.36, nodes=1201, radius_x=None, terms=240):
    if nodes<5 or min(g,gprime)<=0:raise ValueError('resolved box and positive declared gauge inputs required')
    wall=solution['wall'];v=wall['model'].v_GeV;k=wall['k'];h0=wall['bath'].v_GeV/v
    R=k*wall['L'] if radius_x is None else radius_x
    if R<=0 or R>k*wall['L']:raise ValueError('box inside wall solution required')
    x=np.linspace(-R,R,nodes);h=wall['solution'].sol(abs(x)/k)[2];z=x/(v*k)
    results={}
    for name,c in [('W_TE',g*g),('Z_TE',g*g+gprime*gprime)]:
        results[name]=thermal_relative_determinant(z,c*v*v*h*h/4,sqrt_mass(c)*v*h0,temperature,terms=terms)
    return {'declared_g':g,'declared_gprime':gprime,'channels':results,
        'charged_W_multiplicity':2,'neutral_Z_multiplicity':1,
        'total_TE_thermal_free_energy_per_area_GeV3':2*results['W_TE']['relative_thermal_free_energy_per_area_GeV3']+results['Z_TE']['relative_thermal_free_energy_per_area_GeV3']}


def sqrt_mass(c):return np.sqrt(c)/2
