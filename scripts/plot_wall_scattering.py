"""Render scientific comparisons from the committed outgoing/scattering packet."""
from pathlib import Path
import json
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
r=Path(__file__).resolve().parents[1]
d=json.loads((r/'receipts/flavor_cosmology/wall_scattering.json').read_text())
plt.rcParams.update({'font.size':10,'axes.spines.top':False,'axes.spines.right':False})
fig,ax=plt.subplots(1,3,figsize=(13,3.7),constrained_layout=True)
curve=d['real_axis_scattering'];x=[s['detuning_in_imaginary_energy_units'] for s in curve]
ax[0].plot(x,[s['reflection_probability'] for s in curve],'o-',label='Reflection')
ax[0].plot(x,[s['transmission_probability'] for s in curve],'s--',label='Transmission')
ax[0].set(xlabel='(E - Re pole) / |Im pole|',ylabel='Flux fraction',title='Resolved illustrative resonance',ylim=(-.03,1.03));ax[0].legend()
w=d['decoupled_weak_portal_sweep'];k=np.array([s['portal'] for s in w]);width=np.array([s['pole']['width_GeV'] for s in w])
ax[1].loglog(k,width,'o-',label='Outgoing pole');ax[1].loglog(k,[s['analytic']['width_GeV'] for s in w],'--',label='Leading analytic width')
ax[1].set(xlabel='Portal coupling',ylabel='Width (GeV)',title='Ordinary channel: portal squared');ax[1].legend()
w=d['polynomial_node_sweep'];k=np.array([s['portal'] for s in w]);width=np.array([s['pole']['width_GeV'] for s in w])
ax[2].loglog(k,width,'o-',label='Coupled outgoing pole');ax[2].loglog(k,width[0]*(k/k[0])**4,'--',label='Portal fourth reference')
ax[2].set(xlabel='Portal coupling',ylabel='Width (unit v=1 GeV)',title='Polynomial node: leading leakage zero');ax[2].legend()
for a in ax:a.grid(alpha=.18)
fig.savefig(r/'receipts/flavor_cosmology/wall_scattering.png',dpi=180)
