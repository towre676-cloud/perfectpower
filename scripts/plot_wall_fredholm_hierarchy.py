"""Illustrate the derived coefficient, independent curve and leakage orders."""
from pathlib import Path
import json
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
root=Path(__file__).resolve().parents[1]
r=json.loads((root/'receipts/flavor_cosmology/wall_fredholm_hierarchy.json').read_text())
fig,axs=plt.subplots(1,3,figsize=(13.2,3.8),constrained_layout=True)
p=r['universal_responses']['profile'];x=p['x']
for n in ['H','A','T','B','W']:axs[0].plot(x,p[n],label=n)
axs[0].set(xlim=(0,8),xlabel='x = sqrt(lambda / 2) rho',ylabel='Universal response',title='Five forced linear responses')
axs[0].legend(fontsize=8,ncol=2);axs[0].grid(alpha=.2)
for f in r['independent_parameter_families']:
 c=f['predicted_coefficients'];Q=c['quadratic_threshold_coefficient'];cases=f['independent_nonlinear_cases']
 axs[1].plot([t['portal'] for t in cases],[t['quadratic_threshold_difference_quotient']/Q-1 for t in cases],'o-',label=f"lambda={c['source_lambda']}, h0={c['h0']}")
axs[1].axhline(0,color='gray',lw=.7);axs[1].set(xlabel='Portal kappa',ylabel='Measured quadratic coefficient / prediction - 1',title='Independent nonlinear curve check')
axs[1].legend(fontsize=7);axs[1].grid(alpha=.2)
w=r['first_vs_second_correction_outgoing_widths'];kap=np.array([t['portal'] for t in w])
for order,color in [(1,'C0'),(2,'C1')]:
 values=np.array([t[f'order_{order}_outgoing']['width_GeV'] for t in w]);axs[2].loglog(kap,values,'o-',color=color,label=f'Correction through order {order}')
 power=2*order+4;axs[2].loglog(kap,values[0]*(kap/kap[0])**power,'--',color=color,alpha=.7,label=f'kappa^{power} reference')
axs[2].set(xlabel='Portal kappa',ylabel='Outgoing mode width (GeV, v = 1 GeV)',title='Sixth to eighth power leakage')
axs[2].legend(fontsize=7);axs[2].grid(alpha=.2,which='both')
fig.savefig(root/'receipts/flavor_cosmology/wall_fredholm_hierarchy.png',dpi=180)
