"""Real-time lifetime check of the 154.225 GeV localized wall mode.

Run: OPENBLAS_NUM_THREADS=1 PYTHONPATH=python python python/develop_wall_mode_lifetime.py
Writes receipts/flavor_cosmology/wall_mode_lifetime.json (about 30 minutes, one core).
"""
from pathlib import Path
from math import sqrt, pi
import json, time
import numpy as np
from perfectpower import wall_mode_lifetime as W

ROOT = Path(__file__).resolve().parents[1]


def log(*a):print(time.strftime('%H:%M:%S'), *a, flush=True)


def main():
    c = W.couplings(); C = W.CANDIDATE; out = {'declared_inputs': C, 'reduced_couplings': c}
    out['units'] = ('x=k v z, t=k v t (k v=%.6f GeV); u=phi/v, h,pi in units of v_H. A is the source amplitude of the '
                    'full-line normalised mode in x units; mode energy per wall area omega^2 A^2 N/(2k^2) in kv units.' % c['kv_GeV'])
    # 1. Static lattice wall and the mode at two spacings.
    modes = []
    for dx in (.25, .125):
        N = int(round(60/dx)); wall = W.static_wall(c, N, dx); m = W.localized_mode(c, wall, dx)
        modes.append({'dx': dx, 'static_residual': wall['residual'], 'discrete_Ward_zero_mode_residual': wall['Ward_zero_mode_residual'],
                      'omega2': m['omega2'], 'mass_GeV': m['omega']*c['kv_GeV'],
                      'relative_mass_difference_from_main': m['omega']*c['kv_GeV']/C['main_mode_mass_GeV']-1,
                      'max_Higgs_component_over_source': float(abs(m['psi_h']).max()/abs(m['psi_u']).max()),
                      'radiating_Higgs_amplitude_A1': m['radiating_Higgs_amplitude'],
                      'linear_Higgs_leak_energy_rate_GeV': m['linear_leak_energy_rate']*c['kv_GeV'],
                      'canonical_norm': m['canonical_norm']})
        log('mode', modes[-1])
    out['lattice_mode'] = modes
    out['heavy_singlet_elimination'] = {'static': 'exact (S=-g phi^2/M^2 solves its equation; zero-frequency Hessian unchanged)',
        'dynamical_Hessian_shift_over_k2': 4*(C['source_current_GeV']/C['v_GeV'])**2*(c['k']**2*3)/((C['heavy_mass_GeV']/C['v_GeV'])**4)/c['k']**2}

    # 2. Classical noise-free run: Goldstones stay identically zero.
    dx = .25; wall = W.static_wall(c, 240, dx); m = W.localized_mode(c, wall, dx)
    z = W.classical_statistical_run(c, wall, m, .1, dt=.05, steps=2000, samples=1, noise_fraction=0., seed=0, record=(2000,))
    out['classical_Goldstone_subspace'] = {'Goldstone_energy_after_t100_A01': float(z[2000][0]),
        'statement': 'pi=0 is invariant under the nonlinear equations (force proportional to pi); a classical field without seeded fluctuations emits no Goldstone pairs.'}

    # 3. Second-harmonic radiation with an absorbing layer.
    Cth = W.kink_second_harmonic_rate(); sh = []
    for dx_, A in [(.25, .05), (.25, .1), (.25, .15), (.25, .2), (.125, .1)]:
        L = 250; wl = W.static_wall(c, int(round(L/dx_)), dx_); ml = W.localized_mode(c, wl, dx_)
        dt = .2*dx_; nT = int(round(2*pi/ml['omega']/dt))
        env = W.second_harmonic_envelope(c, wl, ml, A, dt=dt, steps=int(round(1500/dt)), sponge=(150., .5), period_steps=nT)
        t, a = env[:, 0], env[:, 1]; s = t > 100
        slope, icpt = np.polyfit(t[s], 1/a[s]**2, 1)
        res = float(np.max(abs(1/a[s]**2-(slope*t[s]+icpt)))*a[s][0]**2)
        sh.append({'dx': dx_, 'A0': A, 'fitted_d_inv_A2_dt': float(slope), 'ratio_to_closed_form': float(slope/Cth),
                   'final_envelope': float(a[-1]), 'max_relative_fit_residual': res})
        log('second harmonic', sh[-1])
    coarse = [r for r in sh if r['dx'] == .25]
    fit = np.polyfit([r['A0']**2 for r in coarse], [r['fitted_d_inv_A2_dt'] for r in coarse], 1)
    out['second_harmonic'] = {'closed_form_energy_rate_over_A2_x_units': Cth,
        'closed_form_energy_rate_over_A2_GeV': Cth*c['kv_GeV'], 'runs': sh,
        'A_to_zero_extrapolated_rate_over_A2': float(fit[1]), 'extrapolated_ratio_to_closed_form': float(fit[1]/Cth),
        'definition': 'Gamma_E(A)=-dlnE/dt=C A^2, equivalently d(1/A^2)/dt=C; envelope = half peak-to-peak of the source projection per period.'}

    # 4. Pair emission: exact Gaussian Goldstones per transverse momentum.
    base = dict(dx=.25, L=60., dt=.05, A=.05, nodes=10, t_ramp=20., t0=30., t1=100.)
    configs = {'base': base,
               'base_early_window': {**base, 't1': 65.},
               'nodes_14': {**base, 'nodes': 14},
               'long_box_L120_t220': {**base, 'L': 120., 't1': 220.},
               'fine_dx0125': {**base, 'dx': .125, 'dt': .025},
               'A_0.02': {**base, 'A': .02, 'nodes': 6},
               'A_0.05_nodes6': {**base, 'nodes': 6},
               'A_0.1': {**base, 'A': .1, 'nodes': 6},
               'A_0.2': {**base, 'A': .2, 'nodes': 6}}
    pairs = {}
    for name, cfg in configs.items():
        r = W.pair_width_scan(c, **cfg); r['ratio_to_main'] = r['Gamma_GG_GeV']/C['main_Gamma_GG_GeV']
        pairs[name] = r; log('pairs', name, r['Gamma_GG_GeV'], r['ratio_to_main'], r['even_GeV'], r['odd_GeV'])
    out['pair_emission'] = pairs
    best = pairs['long_box_L120_t220']
    out['pair_comparison'] = {'main_Gamma_GG_GeV': C['main_Gamma_GG_GeV'], 'main_even_GeV': C['main_Gamma_GG_even_GeV'],
        'main_odd_GeV': C['main_Gamma_GG_odd_GeV'],
        'real_time_values_GeV': {k: v['Gamma_GG_GeV'] for k, v in pairs.items()},
        'real_time_even_over_main_even_long_box': best['even_GeV']/C['main_Gamma_GG_even_GeV'],
        'real_time_odd_over_main_odd_long_box': best['odd_GeV']/C['main_Gamma_GG_odd_GeV'],
        'amplitude_dependence_ratio_to_A005': {k: pairs[k]['Gamma_GG_GeV']/pairs['A_0.05_nodes6']['Gamma_GG_GeV'] for k in ('A_0.02', 'A_0.1', 'A_0.2')}}

    # 5. Classical-statistical Monte Carlo (fully nonlinear) vs exact Gaussian, p=0 odd sector.
    A, dt, i0, i1 = .05, .05, 600, 2000; nT = int(round(2*pi/m['omega']/dt))
    rec = list(range(i0, i0+nT))+list(range(i1-nT+1, i1+1))
    bg = W.evolve_background(c, wall, m, A, dt=dt, steps=i1)
    det = W.goldstone_pair_power(c, wall, bg['X'], dt=dt, p=0., parity=-1, window=(i0, i1, nT))['power']/A**2
    nf = 1e-4; est = []
    def pw(r):
        e = np.mean([r[n] for n in rec[:nT]], 0); l = np.mean([r[n] for n in rec[nT:]], 0)
        return (l-e)/((i1-i0-(nT-1))*dt)
    for block in range(64):
        R = {a: pw(W.classical_statistical_run(c, wall, m, a, dt=dt, steps=i1, samples=64, noise_fraction=nf,
                                             seed=1000+block, record=rec)) for a in (A, -A, 0.)}
        est.append((R[A]+R[-A]-2*R[0.])/(2*nf*A*A))
    est = np.concatenate(est); mean = float(est.mean()); sem = float(est.std(ddof=1)/sqrt(len(est)))
    out['classical_statistical_check'] = {'sector': 'p=0, odd Goldstone parity, one component', 'A': A,
        'noise_fraction_of_half_quantum': nf, 'samples': len(est), 'seeds': '1000..1063 (numpy default_rng), 64 samples each',
        'estimator': '[E(A)+E(-A)-2E(0)]/2 with common noise (antithetic), divided by noise_fraction*A^2',
        'Monte_Carlo_power_over_A2': mean, 'standard_error': sem, 'exact_Gaussian_power_over_A2': det,
        'difference_in_standard_errors': (mean-det)/sem,
        'scope': 'Nonlinear equations with Goldstone self-interaction and backreaction; noise reduced to 1e-4 of a half quantum and rescaled linearly, valid while the emission is linear in the noise.'}
    log('MC', out['classical_statistical_check'])

    # 6. Lifetime synthesis.
    G = best['Gamma_GG_GeV']; Cg = out['second_harmonic']['A_to_zero_extrapolated_rate_over_A2']*c['kv_GeV']
    Ac2 = G/Cg; om = m['omega']
    out['lifetime'] = {'pair_width_used_GeV': G, 'lifetime_single_quantum_s': W.HBAR_GEV_S/G,
        'main_lifetime_s': W.HBAR_GEV_S/C['main_Gamma_GG_GeV'],
        'second_harmonic_energy_rate_over_A2_GeV': Cg, 'crossover_A': sqrt(Ac2),
        'crossover_occupation_per_area_GeV2': om*Ac2/(2*c['k']**2)*c['kv_GeV']**2,
        'crossover_occupation_per_kv_area': om*Ac2/(2*c['k']**2),
        'energy_law': 'dE/dt=-(Gamma_GG+C A^2)E with E proportional to A^2 (Goldstone channel only; ungauged O(4)); Gamma_lin from residual node detuning is listed separately and is negligible.',
        'amplitude_solution': 'A(t)^2=Gamma A0^2 e^{-Gamma t}/(Gamma+C A0^2(1-e^{-Gamma t}))',
        'quantum_note': 'Second-harmonic radiation is the classical limit of two mode quanta -> one source quantum (rate proportional to n(n-1)); a single quantum decays only through 1->2 channels such as the Goldstone pair.'}
    out['not_claimed'] = ['full 3+1 nonlinear classical-statistical lattice simulation (transverse momenta enter through the exact quadratic-order decomposition, not a 3+1 lattice)',
        'gauged electroweak lifetime; W/Z channels are not simulated', 'Monte Carlo resolution better than its quoted standard error',
        'loop/self-energy corrections, renormalised Goldstone mass shifts, thermal bath', 'interval or rigorous error bounds',
        'singlet dynamics beyond its static constraint (O(omega^2/M^2))']
    out['scope'] = ('Reduced (singlet-constrained) ungauged O(4) theory; 1+1 real-time lattice evolution; pair channel via exact Gaussian '
                    'mode functions (equal to the infinite classical-statistical ensemble with half-quantum seeding) per transverse momentum, '
                    'integrated over the planar phase space. Floating-point lattice numerics.')
    p = ROOT/'receipts/flavor_cosmology/wall_mode_lifetime.json'
    p.write_text(json.dumps(out, indent=1, sort_keys=True, default=float)+'\n')
    log('written', p)


if __name__ == '__main__':main()
