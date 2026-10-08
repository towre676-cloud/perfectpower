"""Plot independently resolved wall pair widths and TE thermal contributions."""
from pathlib import Path
import json
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

root=Path(__file__).resolve().parents[1]
r=json.loads((root/'receipts/flavor_cosmology/wall_pair_decay.json').read_text())
fig,axes=plt.subplots(1,3,figsize=(14,4.3),layout='constrained')
for channel,label in [('W_TE','WW: one polarization'),('Z_TE','ZZ: one polarization')]:
    a=[t for t in r['gauge_coupling_scan'] if t['channel']==channel]
    axes[0].plot([t['declared_g'] for t in a],[t['width_GeV']/1e-9 for t in a],'o-',label=label)
axes[0].set(xlabel='Declared g (g prime = 0.36)',ylabel='Partial width [10⁻⁹ GeV]',title='Physical vector emission');axes[0].legend(fontsize=8)
a=r['near_W_pair_threshold_scan'];e=np.array([t['pair_energy_excess_GeV'] for t in a]);w=np.array([t['width_GeV'] for t in a])
axes[1].loglog(e,w,'o-',label='Resolved WW polarization')
axes[1].loglog(e,w[-1]*(e/e[-1])**3,'--',label='Threshold excess cubed')
axes[1].set(xlabel='M − 2 mW [GeV]',ylabel='Partial width [GeV]',title='Barrier suppresses threshold emission');axes[1].legend(fontsize=8)
for n in [601,1201,2401,4801]:
    a=[t for t in r['thermal_resolution_controls'] if t['nodes']==n]
    axes[2].plot([t['channels']['W_TE']['temperature_GeV'] for t in a],[t['total_TE_thermal_free_energy_per_area_GeV3'] for t in a],'o-',label=f'{n} nodes',alpha=.7)
axes[2].set(xlabel='Declared T [GeV]',ylabel='Relative thermal free energy / area [GeV³]',title='One polarization per W+, W−, Z');axes[2].legend(fontsize=8)
fig.suptitle('154.225 GeV wall mode: continuum emission and fixed-wall thermal bath',fontsize=14)
fig.savefig(root/'receipts/flavor_cosmology/wall_pair_decay.png',dpi=180)
