"""Plots for bounce actions and the nucleation threshold of the biased CP vacua."""
from pathlib import Path
import json
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

root=Path(__file__).resolve().parents[1]
r=json.loads((root/'receipts/flavor_cosmology/wall_nucleation.json').read_text())
plt.rcParams.update({'font.size':13,'axes.spines.top':False,'axes.spines.right':False})
fig,axes=plt.subplots(1,2,figsize=(12,4.6),constrained_layout=True)
a=axes[0];esp=r['spinodal']['eps_sp'];e=np.linspace(.008,esp-1e-6,400)
sig=2*np.sqrt(2)/3
for d,c in ((3,'#1f77b4'),(4,'#d95f02')):
    rows=[x for x in r['bounce_table'] if x['d']==d]
    a.semilogy([x['eps'] for x in rows],[x['s'] for x in rows],'o',color=c,label=f'O({d}) bounce')
    tw=16*np.pi*sig**3/(3*(2*e)**2) if d==3 else 27*np.pi**2*sig**4/(2*(2*e)**3)
    a.semilogy(e,tw,'--',color=c,lw=.9)
    a.semilogy(e,r['spinodal']['C_exact'][str(d)]*(esp-e)**((6-d)/4),':',color=c,lw=1.2)
a.set(xlabel=r'$\epsilon=h/(\lambda v_T^3)$',ylabel=r'reduced action $s_d$',title='Bounces: thin wall (dashed), spinodal law (dotted)',ylim=(1e-2,1e8));a.legend(frameon=False,fontsize=10)
a=axes[1];rows=r['nucleation_threshold'];T=np.array([x['T_GeV'] for x in rows])
a.semilogx(T,[x['d3']['0.0']['eps_star']/esp for x in rows],'o-',label='thermal O(3) threshold')
a.semilogx(T,[x['d4']['0.0']['eps_star']/esp for x in rows],'s-',label='quantum O(4) threshold')
a.fill_between(T,[x['d4']['-20.0']['eps_star']/esp for x in rows],[x['d4']['20.0']['eps_star']/esp for x in rows],color='#d95f02',alpha=.2,lw=0,label=r'prefactor $e^{\pm20}$')
a.axhline(1,color='grey',lw=.8)
a.set(xlabel='temperature [GeV]',ylabel=r'$\epsilon_*/\epsilon_{\rm sp}$',title='Bias needed for one bubble per Hubble volume',ylim=(.93,1.01))
a.text(.04,.06,'declared bias: $\\epsilon\\approx10^{-25}\\,\\epsilon_{\\rm sp}$',transform=a.transAxes,fontsize=11)
a.legend(frameon=False,fontsize=10,loc='lower right')
fig.savefig(root/'receipts/flavor_cosmology/wall_nucleation.png',dpi=170)
