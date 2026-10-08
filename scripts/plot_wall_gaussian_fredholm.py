"""Render coupled-node shift, leakage orders and fixed-Higgs prediction errors."""
from pathlib import Path
import json
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
root=Path(__file__).resolve().parents[1]
r=json.loads((root/'receipts/flavor_cosmology/wall_gaussian_fredholm.json').read_text())
fig,axs=plt.subplots(1,3,figsize=(13.2,3.8),constrained_layout=True)
p=r['strong_Gaussian_response']['profile'];x=np.array(p['x']);axs[0].plot(x,p['source_shape'],label='Coupled source shape')
axs[0].plot(x,p['singlet_shape'],label='Coupled singlet shape');axs[0].plot(x,1/np.cosh(x)*np.tanh(x),'--',label='Decoupled source shape')
axs[0].set(xlim=(0,7),xlabel='x = sqrt(lambda / 2) rho',ylabel='Mode with fixed center derivative',title='Heavy gradients deform the mode')
axs[0].legend(fontsize=7);axs[0].grid(alpha=.2)
w=r['outgoing_width_cases'];kap=np.array([v['portal'] for v in w])
for name,power,label in [('scalar_node',2,'Scalar node'),('Gaussian_node',4,'Coupled node'),('Gaussian_corrected_node',6,'Coupled node + response correction')]:
 y=np.array([v[name]['width_GeV'] for v in w]);line=axs[1].loglog(kap,y,'o-',label=label)[0]
 axs[1].loglog(kap,y[0]*(kap/kap[0])**power,'--',color=line.get_color(),alpha=.7)
axs[1].set(xlabel='Portal kappa',ylabel='Outgoing width (GeV, v = 1 GeV)',title='Second, fourth and sixth powers')
axs[1].legend(fontsize=6.5);axs[1].grid(alpha=.2,which='both')
f=r['fixed_Higgs_physical_predictions'];p=np.array([v['prediction']['portal'] for v in f]);e=np.array([v['source_lambda_prediction_error'] for v in f])
axs[2].loglog(p,e,'o-',label='Independent source-quartic error');axs[2].loglog(p,e[0]*(p/p[0])**2,'--',label='Quadratic portal reference')
axs[2].set(xlabel='Portal kappa',ylabel='Predicted lambda - full candidate lambda',title='Fixed-Higgs physical-scale inversion')
axs[2].legend(fontsize=7);axs[2].grid(alpha=.2,which='both')
fig.savefig(root/'receipts/flavor_cosmology/wall_gaussian_fredholm.png',dpi=180)
