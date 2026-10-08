"""Plot Goldstone potential, vector profiles and benchmark pair thresholds."""
from pathlib import Path
import json
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
root=Path(__file__).resolve().parents[1]
r=json.loads((root/'receipts/flavor_cosmology/wall_gauge_channels.json').read_text())['physical_scale_candidate'];p=r['profile'];rho=np.array(p['rho'])
fig,axs=plt.subplots(1,3,figsize=(13.2,3.8),constrained_layout=True)
axs[0].plot(rho,p['Higgs_ratio_to_vacuum']);axs[0].axhline(1,color='gray',lw=.7)
axs[0].set(xlim=(0,2500),xlabel='rho = v z',ylabel='h / h0',title='Positive Higgs barrier (sampled)');axs[0].grid(alpha=.2)
axs[1].plot(rho,np.array(p['global_Goldstone_potential_over_v2'])*1e8,label='Global angular potential')
vac=(r['W_vacuum_mass_GeV']/30000)**2
axs[1].plot(rho,(np.array(p['W_transverse_potential_over_v2'])-vac)*1e8,label='W transverse minus vacuum')
axs[1].plot(rho,(np.array(p['W_longitudinal_potential_over_v2'])-vac)*1e8,label='W longitudinal minus vacuum')
axs[1].axhline(0,color='gray',lw=.7);axs[1].set(xlim=(0,2500),xlabel='rho = v z',ylabel='Potential / v^2, scaled by 10^8',title='Factorization controls local wells');axs[1].legend(fontsize=7);axs[1].grid(alpha=.2)
values=[r['mass_GeV'],r['two_W_threshold_GeV'],r['two_Z_threshold_GeV']]
axs[2].barh(['Localized candidate','Two W threshold','Two Z threshold'],values,color=['C0','C1','C2'])
for j,v in enumerate(values):axs[2].text(v+2,j,f'{v:.3f}',va='center',fontsize=9)
axs[2].set(xlim=(0,210),xlabel='Energy (GeV)',title='Declared g = 0.65, gprime = 0.36');axs[2].grid(axis='x',alpha=.2)
fig.savefig(root/'receipts/flavor_cosmology/wall_gauge_channels.png',dpi=180)
