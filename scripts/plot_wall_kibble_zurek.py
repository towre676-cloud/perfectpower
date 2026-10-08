"""Plot receipt data without rerunning evolution; requires NumPy and Matplotlib."""
from pathlib import Path
import json
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
root=Path(__file__).resolve().parents[1];out=root/'docs/figures';out.mkdir(exist_ok=True)
r=json.loads((root/'receipts/flavor_cosmology/wall_kibble_zurek.json').read_text());z=np.load(root/'receipts/flavor_cosmology/wall_kibble_zurek_snapshots.npz')
fig,axs=plt.subplots(2,2,figsize=(9,8),layout='constrained')
for ax,f,q in zip(axs.flat,z['fields'],z['quenches']):
 im=ax.imshow(f,origin='lower',extent=[0,128,0,128],vmin=-.75,vmax=.75,cmap='RdBu_r');ax.contour(np.arange(128)+.5,np.arange(128)+.5,f,levels=[0],colors='black',linewidths=.55);ax.set_title(r'$\tau_Q=%d$ at $5\hat t$'%q);ax.set_xlabel('X');ax.set_ylabel('Y')
fig.colorbar(im,ax=axs,label='Reduced source u',shrink=.85);fig.suptitle('Source walls formed from a stochastic restored phase\nFirst replica; 2D periodic reduced-source model')
fig.savefig(out/'wall_kibble_zurek_domains.png',dpi=140);plt.close(fig)
fig,axs=plt.subplots(1,3,figsize=(15,4.7),layout='constrained');runs=r['primary_runs'];q=np.array([x['quench_time'] for x in runs]);obs=[x['ensemble_summary'][-2] for x in runs];d=np.array([x['mean_wall_density'] for x in obs]);e=np.array([x['standard_error_wall_density'] for x in obs]);fit=r['scaling_fits'][2]
axs[0].errorbar(q,d,yerr=e,fmt='o',capsize=3,label='Mean ± ensemble SE');qq=np.geomspace(60,550,100)
axs[0].plot(qq,np.exp(fit['intercept'])*qq**fit['wall_density_exponent'],label='Fitted slope %.3f'%fit['wall_density_exponent']);axs[0].plot(qq,d[0]*(qq/q[0])**(-.25),'--',label='Mean-field reference −1/4');axs[0].set(xscale='log',yscale='log',xlabel='Quench time',ylabel='Wall length / area',title='Formed interfaces at 5 hat t');axs[0].legend(fontsize=8)
for x in runs:
 o=x['ensemble_summary'][1:];axs[1].plot([a['time_over_hat'] for a in o],[a['mean_broken_amplitude_ratio'] for a in o],'o-',label=str(int(x['quench_time'])))
axs[1].axhline(1,color='gray',ls='--');axs[1].set(xlabel='Time / hat t',ylabel='RMS / instantaneous broken minimum',title='Delayed nonlinear ordering');axs[1].legend(title='Quench',fontsize=8)
controls=[{'label':'base',**runs[1]}]+r['numerical_and_bath_controls'];o=[x['ensemble_summary'][-2] for x in controls];axs[2].errorbar(range(5),[x['mean_wall_density'] for x in o],yerr=[x['standard_error_wall_density'] for x in o],fmt='o',capsize=4);axs[2].set_xticks(range(5),['Base','Half dt','Half dx','2× box','¼ noise'],rotation=25);axs[2].set(ylabel='Wall length / area',title='Controls at quench 128, time 5 hat t')
fig.suptitle('Finite-cutoff Model-A benchmark: bath and quench are declared inputs');fig.savefig(out/'wall_kibble_zurek_scaling.png',dpi=140);plt.close(fig)
