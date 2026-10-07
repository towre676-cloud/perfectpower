"""Plots for the PRS wall-network calibration."""
from pathlib import Path
import json
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

root=Path(__file__).resolve().parents[1]
r=json.loads((root/'receipts/flavor_cosmology/wall_network.json').read_text())
cache=json.loads((root/'receipts/flavor_cosmology/wall_network_series.json').read_text())
plt.rcParams.update({'font.size':13,'axes.spines.top':False,'axes.spines.right':False})
fig,axes=plt.subplots(1,2,figsize=(12,4.6),constrained_layout=True)
a=axes[0]
for x in cache['unbiased']:
    p=x['params'];s=x['series']
    a.plot(s['tau'],s['A'],lw=1.2,label='N=%d, $\\lambda$=%g, seed %d'%(p['N'],p['lam'],p['seed']))
a.axhline(.8,color='grey',ls='--',lw=.8,label='declared A=0.8')
a.set(xlabel=r'conformal time $\tau$',ylabel=r'area parameter $A=\rho_w t/\sigma$',title='Unbiased PRS network',ylim=(0,1.1));a.legend(frameon=False,fontsize=8.5,ncol=2,loc='lower right')
a=axes[1]
for x,b in zip(cache['biased'],r['biased']):
    s=x['series'];t=np.array(s['tau'])
    ff=np.minimum(np.array(s['false_fraction']),1-np.array(s['false_fraction']))
    a.semilogy(t,np.maximum(ff,1e-4),lw=1.2,label=r'$\epsilon_1$=%g, $C_{\rm ann}$=%.2f'%(x['params']['eps1'],b['C_ann_false_1pct']))
a.axhline(.01,color='grey',ls=':',lw=.8)
a.set(xlabel=r'conformal time $\tau$',ylabel='false-vacuum volume fraction',title='Biased networks (constant physical $\\Delta V$)',ylim=(1e-4,1));a.legend(frameon=False,fontsize=9.5)
fig.savefig(root/'receipts/flavor_cosmology/wall_network.png',dpi=170)
