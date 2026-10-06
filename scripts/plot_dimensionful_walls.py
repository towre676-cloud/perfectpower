"""Plot the solved dimensionful wall and explicitly conditional GW templates."""
from pathlib import Path
import json
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
ROOT=Path(__file__).resolve().parents[1]
r=json.loads((ROOT/'receipts/flavor_cosmology/dimensionful_walls.json').read_text())
fig,axes=plt.subplots(1,2,figsize=(11.2,4.1),layout='constrained')
p=r['wall']['profile'];rho=np.array(p['rho']);phi=np.array(p['phi_over_v']);S=np.array(p['S_over_v'])
axes[0].plot(rho,phi,label=r'$\phi/v$',lw=2)
axes[0].plot(rho,S/S[0],label=r'$S/S_{\mathrm{vac}}$',lw=1.8)
axes[0].set(xlim=(-22,22),xlabel=r'$\rho=vz$',ylabel='Canonical field profile',title='Solved Gaussian wall | v = 30 TeV')
axes[0].legend(frameon=False);axes[0].grid(alpha=.15)
f=np.array(r['GW_scenarios']['reference_scaling']['frequency_Hz']);curves=[]
for x in r['nuisance_scan']:
 q=f/x['peak_frequency_Hz'];mid=-1. if x['emission_H_ratio']==1 else -.5;uv=-1. if x['emission_H_ratio']==1 else -1.8
 s=np.where(q<=1,q**3,np.where(q<=10,q**mid,10**mid*(q/10)**uv));curves.append(x['peak_Omega_h2']*s)
axes[1].fill_between(f,np.min(curves,axis=0),np.max(curves,axis=0),color='#d6dce8',label='162 chosen parameter cases')
for name,label in [('reference_scaling','Reference scaling'),('delayed_emission_sensitivity','Delayed emission sensitivity')]:
 g=r['GW_scenarios'][name];axes[1].loglog(g['frequency_Hz'],g['Omega_h2'],label=label,lw=2)
axes[1].set(xlim=(1e-12,1e-3),ylim=(1e-24,1e-8),xlabel='Frequency today [Hz]',ylabel=r'$\Omega_{\rm GW}h^2$',title='Conditional spectra | not a flavor prediction')
axes[1].legend(frameon=False,fontsize=8);axes[1].grid(alpha=.15,which='both')
fig.savefig(ROOT/'receipts/flavor_cosmology/dimensionful_walls.png',dpi=190)
