"""Scientific plots for the coupled wall and finite-box spectrum."""
from pathlib import Path
import json
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

root=Path(__file__).resolve().parents[1]
r=json.loads((root/'receipts/flavor_cosmology/wall_stability.json').read_text())
plt.rcParams.update({'font.size':14,'axes.spines.top':False,'axes.spines.right':False})
fig,axes=plt.subplots(2,2,figsize=(12,7.4),constrained_layout=True)
p=r['three_field_wall']['profile'];rho=np.array(p['rho']);u=np.array(p['phi_over_v']);y=np.array(p['S_over_v'])
a=axes[0,0];mask=rho<30
a.plot(rho[mask],u[mask],label=r'$\phi/v$');a.plot(rho[mask],-1000*y[mask],label=r'$-S/(g v^2/M^2)$')
a.set(xlabel=r'$\rho=vz$',ylabel='Normalized fields',title='Coupled source and mediator wall');a.legend(frameon=False)
a=axes[0,1];a.plot(rho,np.array(p['radial_Higgs_GeV'])-246,color='#c85d20')
a.set(xlabel=r'$\rho=vz$',ylabel='Higgs displacement [GeV]',title='Small, broad radial Higgs response')
a=axes[1,0];n=np.array([s['central_nodes'] for s in r['mesh_refinements']]);e=np.array([s['translation']['eigenvalues_over_v2'][0] for s in r['mesh_refinements']])
a.loglog(n,e,'o-',label='Translation mode');a.loglog(n,e[0]*(n[0]/n)**4,'--',color='grey',label=r'$N^{-4}$ reference')
a.set(xlabel='Central element grid points',ylabel=r'$m_{\mathrm{grid}}^2/v^2$',title='Translation zero-mode convergence');a.legend(frameon=False,fontsize=13)
a=axes[1,1];levels=[r['box_refinements'][0]['spectrum'],r['mesh_refinements'][1],r['box_refinements'][1]['spectrum']]
L=np.array([s['half_box_rho'] for s in levels]);gap=np.array([s['opposite']['eigenvalues_over_v2'][0]-s['vacuum_thresholds_over_v2'][0] for s in levels])
a.loglog(L,gap,'o-',label='Lowest Higgs bulk level');a.loglog(L,(np.pi/(2*L))**2,'--',color='grey',label='Free Higgs box spacing')
a.set(xlabel='Half-box length [dimensionless]',ylabel=r'$(m^2-m_H^2)/v^2$',title='Finite-box Higgs continuum levels');a.legend(frameon=False,fontsize=13)
fig.suptitle('Coupled spectator wall and fluctuation spectrum',fontsize=18)
fig.savefig(root/'receipts/flavor_cosmology/wall_stability.png',dpi=190)
