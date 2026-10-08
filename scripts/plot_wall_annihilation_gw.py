"""Plots for the annihilation-phase gravitational waves of the biased wall network."""
from pathlib import Path
import json
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

root = Path(__file__).resolve().parents[1]
r = json.loads((root/'receipts/flavor_cosmology/wall_annihilation_gw.json').read_text())
cache = json.loads((root/'receipts/flavor_cosmology/wall_annihilation_gw_series.json').read_text())
plt.rcParams.update({'font.size': 12, 'axes.spines.top': False, 'axes.spines.right': False})
fig, axes = plt.subplots(2, 2, figsize=(12.5, 9), constrained_layout=True)
colors = {2.5e-6: '#1f77b4', 4e-6: '#ff7f0e', 6e-6: '#2ca02c'}

a = axes[0, 0]
for run in cache['scan']:
    p = run['params']
    if p['N'] != 192 or p['tau_on'] != 40. or p['seed'] != 0:
        continue
    t = [x['tau'] for x in run['rows']]
    a.plot(t, [x['false_fraction'] for x in run['rows']], lw=1.3, label=r'$\epsilon$=%.2g' % p['eps'])
a.axvline(40, color='grey', ls=':', lw=.8)
a.set(xlabel=r'conformal time $\tau$', ylabel='false-vacuum volume fraction', yscale='log', ylim=(1e-4, .7),
      title='Collapse of the false vacuum (192$^3$, seed 0)')
a.legend(frameon=False, fontsize=9)

a = axes[0, 1]
ann = r['annihilation']
rows = [x for x in ann['runs'] if x['params']['N'] == 192 and x['params']['tau_on'] == 40.]
x = np.array([q['sigma_over_DeltaV'] for q in rows]); y = np.array([q['tau_false_below_1pct'] for q in rows])
a.loglog(x, y, 'o', label='lattice, false fraction < 1%')
y10 = np.array([q['tau_false_below_10pct'] for q in rows])
a.loglog(x, y10, 's', mfc='none', label='false fraction < 10%')
xx = np.geomspace(x.min()*.9, x.max()*1.1, 50)
f = ann['fit_false_1pct']
a.loglog(xx, f['power_law_prefactor']*xx**f['power_law_p'], '-', lw=1, label='power law p=%.2f' % f['power_law_p'])
o = f['offset_model']
a.loglog(xx, np.sqrt(2*(o['t0'] + o['K']*xx)), '--', lw=1, label='$t_0+K\\sigma/\\Delta V$, K=%.2f' % o['K'])
a.loglog(xx, np.sqrt(2*ann['K_PRS_reference']*xx), ':', color='grey', label='pressure balance, K$_{PRS}$ (p=1/2)')
a.set(xlabel=r'$\sigma/\Delta V$ (lattice units)', ylabel=r'$\tau_{\rm ann}$', title='Annihilation time versus bias')
a.legend(frameon=False, fontsize=8.5)

a = axes[1, 0]
for g in r['gw']['runs']:
    p = g['params']; s = g['series']
    ls = '-' if p['seed'] == 0 else '--'
    a.semilogy(s['tau'], s['E_avg'], ls, color=colors.get(p['eps'], 'k'), lw=1.3,
               label=(r'$\epsilon$=%.2g' % p['eps']) if p['seed'] == 0 else None)
    if p['eps'] == 2.5e-6:
        a.semilogy(s['tau'], s['E_unbiased_avg'], ls, color='k', lw=1, label='unbiased' if p['seed'] == 0 else None)
    a.axvline(g['tau_ann_false_1pct'], color=colors.get(p['eps'], 'k'), ls=':', lw=.7)
a.set(xlabel=r'$\tau$', ylabel=r'comoving GW energy $a^4\rho_{\rm gw}$ (avg)', title='GW energy through annihilation (dotted: $\\tau_{\\rm ann}$)')
a.legend(frameon=False, fontsize=9)

a = axes[1, 1]
for run in cache['gw']:
    p = run['params']
    if p['seed'] != 0:
        continue
    last = run['rows'][-1]; k = np.array(last['k']); s = np.array(last['drho_avg_dlnk'])*last['tau']**4
    g = s > 0
    a.loglog(k[g], s[g], color=colors.get(p['eps'], 'k'), lw=1.3, label=(r'$\epsilon$=%.2g' % p['eps']) if p['eps'] else 'unbiased')
un = [x for x in cache['gw'] if x['params']['seed'] == 0 and x['params']['eps'] == 0][0]
j = int(np.argmin([abs(x['tau'] - 106.) for x in un['rows']]))
k = np.array(un['rows'][j]['k']); s = np.array(un['rows'][j]['drho_avg_dlnk'])*un['rows'][j]['tau']**4; g = s > 0
a.loglog(k[g], s[g], color='k', ls=':', label=r'unbiased at $\tau$=%.0f ($\approx\tau_{\rm ann}$)' % un['rows'][j]['tau'])
kk = np.geomspace(.15, 1.5, 10); a.loglog(kk, 3e3*(kk/.15)**-1, '--', color='grey', lw=.8, label=r'$k^{-1}$')
a.axvline(np.pi/2, color='grey', lw=.6)
a.set(xlabel='comoving k (lattice units)', ylabel=r'$a^4\, d\rho_{\rm gw}/d\ln k$', title=r'Spectra at $\tau$=158 (seed 0)')
a.set_ylim(1, 3e5)
a.legend(frameon=False, fontsize=9)
fig.savefig(root/'receipts/flavor_cosmology/wall_annihilation_gw.png', dpi=150)
