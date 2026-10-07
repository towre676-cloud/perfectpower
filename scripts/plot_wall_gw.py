"""Plots for the lattice gravitational-wave extraction from the wall network."""
from pathlib import Path
import json
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

root=Path(__file__).resolve().parents[1]
r=json.loads((root/'receipts/flavor_cosmology/wall_gw.json').read_text())
cache=json.loads((root/'receipts/flavor_cosmology/wall_gw_series.json').read_text())
plt.rcParams.update({'font.size':13,'axes.spines.top':False,'axes.spines.right':False})
fig,axes=plt.subplots(1,2,figsize=(12,4.6),constrained_layout=True)
a=axes[0]
for run in r['runs']:
    p=run['params'];s=run['series']
    lab='N=%d, seed %d'%(p['N'],p['seed'])+(', w=3' if p.get('w_final') else '')
    a.plot([x['tau'] for x in s],[x['eps_gw'] for x in s],'o-',ms=3,label=lab)
a.axhline(.7,color='grey',ls='--',lw=.8,label='declared 0.7')
a.set(xlabel=r'conformal time $\tau$',ylabel=r'$\tilde\epsilon_{\rm gw}=\rho_{\rm gw}/(G A^2\sigma^2)$',title='GW efficiency of the physical wall network',ylim=(0,1));a.legend(frameon=False,fontsize=9.5)
a=axes[1]
for run in cache[:2]:
    for x in run['rows'][-4::3]:
        k=np.array(x['k']);s=np.array(x['drho_dlnk']);f=k*x['tau']/(2*np.pi);g=s>0
        a.loglog(f[g],s[g]/s[g].max(),lw=1.2,label='seed %d, $\\tau$=%.0f'%(run['params']['seed'],x['tau']))
ff=np.geomspace(1.5,20,10);a.loglog(ff,1.2/ff,'--',color='grey',label=r'$f^{-1}$')
a.set(xlabel=r'$f/H$ (cyclic frequency over Hubble rate)',ylabel=r'$d\rho_{\rm gw}/d\ln k$ (normalised)',title='Spectra: peak bounded by the box',ylim=(1e-4,2));a.legend(frameon=False,fontsize=9.5)
fig.savefig(root/'receipts/flavor_cosmology/wall_gw.png',dpi=170)
