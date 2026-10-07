"""Scientific plots for the coupled-channel wall scattering and shape resonance."""
from pathlib import Path
import json
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

root=Path(__file__).resolve().parents[1]
r=json.loads((root/'receipts/flavor_cosmology/wall_jost_scattering.json').read_text())
plt.rcParams.update({'font.size':13,'axes.spines.top':False,'axes.spines.right':False})
fig,axes=plt.subplots(2,2,figsize=(12,7.6),constrained_layout=True)
a=axes[0,0];x=np.linspace(-6,6,400)
for b,m in zip(r['real_axis_Breit_Wigner'],('o','s')):
    a.plot(b['x_over_Gamma'],np.array(b['phase'])-b['phase'][len(b['phase'])//2],m,ms=4,label=r'coupled, $\epsilon=%.0e$'%b['coupling_scale'])
a.plot(x,2*np.arctan(2*x),color='grey',label=r'$2\arctan[2(E-E_r)/\Gamma]$')
a.set(xlabel=r'$(E-E_r)/\Gamma$',ylabel=r'phase of $S/S_{\rm bg}$',title='Real-axis Breit-Wigner, opposite sector');a.legend(frameon=False,fontsize=10)
a=axes[0,1];lad=r['coupling_ladder']['rows']
eps=np.array([l['coupling_scale'] for l in lad]);d=np.array([l['relative_difference_from_Sigma'] for l in lad])
a.loglog(eps,d,'o-',label=r'$|(E_p-E_b)/\epsilon^2-\Sigma|/|\Sigma|$')
a.loglog(eps,d[-1]*(eps/eps[-1])**2,'--',color='grey',label=r'$\epsilon^2$ reference')
a.set(xlabel=r'coupling scale $\epsilon$ on the $\phi$-$h$ entries',ylabel='relative difference',title='Coupled-channel poles vs Feshbach self-energy');a.legend(frameon=False,fontsize=10)
a=axes[1,0];rows=r['physical_scattering']
E=np.array([row['E_over_v2'] for row in rows]);rh=np.array([row['reflection_probabilities'][0][0] for row in rows])
two=[row for row in rows if len(row['open_channels'])>1]
a.loglog(E,rh,'o-',ms=3,label='Higgs quanta')
a.loglog([row['E_over_v2'] for row in two],[row['reflection_probabilities'][1][1] for row in two],'s-',ms=3,label='source quanta')
a.axvline(r['vacuum_thresholds_over_v2'][1],color='grey',lw=.8);a.axhline(1e-15,color='grey',ls=':',lw=.8)
a.set(xlabel=r'$E=\omega^2/v^2$',ylabel=r'$|r|^2$',title='Full-line reflection off the wall',ylim=(1e-24,1e-6));a.legend(frameon=False,fontsize=10)
a=axes[1,1];s=[x for x in r['sensitivity'] if x['variation'].startswith('kappa')]
k=np.array([float(x['variation'].split('=')[1]) for x in s]+[r['declared_Higgs']['portal']])
g=np.array([x['Gamma_over_kappa2'] for x in s]+[r['shape_resonance']['Gamma_E']/r['declared_Higgs']['portal']**2]);o=np.argsort(k)
a.semilogx(k[o],g[o]*1e4,'o-',label='Feshbach, wall re-solved')
a.axhline(r['shape_resonance']['closed_form_Gamma_E']/r['declared_Higgs']['portal']**2*1e4,color='grey',ls='--',label='closed form')
a.set(xlabel=r'portal $\kappa$',ylabel=r'$10^4\,\Gamma_E/\kappa^2$',title='Shape-mode width scaling');a.legend(frameon=False,fontsize=10)
fig.suptitle('Open-channel scattering of the coupled spectator wall',fontsize=17)
fig.savefig(root/'receipts/flavor_cosmology/wall_jost_scattering.png',dpi=170)
