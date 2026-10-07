"""Figures from retuned-node packets; unresolved widths are not plotted as rates."""
from pathlib import Path
import json,numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
r=Path(__file__).resolve().parents[1];d=json.loads((r/'receipts/flavor_cosmology/wall_embedded_states.json').read_text())
plt.rcParams.update({'font.size':10,'axes.spines.top':False,'axes.spines.right':False})
fig,ax=plt.subplots(1,3,figsize=(13.2,3.8),constrained_layout=True)
a=d['first_order_retuned_widths'];k=np.array([v['portal'] for v in a]);g=np.array([v['outgoing_pole']['width_GeV'] for v in a])
ax[0].loglog(k,g,'o-',label='First-order retuned pole');ax[0].loglog(k,g[0]*(k/k[0])**6,'--',label='Portal sixth reference');ax[0].set(xlabel='Portal coupling',ylabel='Width (unit v=1 GeV)',title='Derived correction suppresses leakage');ax[0].legend()
a=d['Higgs_quartic_detuning'];delta=np.array([v['relative_quartic_detuning'] for v in a if v['relative_quartic_detuning']]);g=np.array([v['outgoing_pole']['width_GeV'] for v in a if v['relative_quartic_detuning']])
ax[1].semilogy(delta,g,'o');ax[1].axvline(0,color='gray',ls='--');ax[1].set(xlabel='Relative quartic detuning',ylabel='Resolved width (GeV)',title='Retuned point: leakage unresolved');ax[1].grid(alpha=.2)
p=d['fixed_Higgs_parameters_source_quartic_candidates'][-1]['profile'];x=np.array(p['rho']);source=np.array(p['source_mode']);h=np.array(p['Higgs_mode'])
ax[2].plot(x,source/np.max(abs(source)),label='Source mode / max');ax[2].plot(x,h/np.max(abs(h)),label='Higgs mode / max');ax[2].set(xlabel='rho = v z',ylabel='Each component normalized separately',title='154.23 GeV localized candidate');ax[2].legend();ax[2].grid(alpha=.2)
fig.savefig(r/'receipts/flavor_cosmology/wall_embedded_states.png',dpi=180)
