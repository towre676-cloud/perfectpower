"""Plots from cooling receipt, without solving profiles again."""
from pathlib import Path
import json
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
root=Path(__file__).resolve().parents[1];r=json.loads((root/'receipts/flavor_cosmology/wall_cooling.json').read_text());out=root/'docs/figures';out.mkdir(exist_ok=True)
p=r['profiles'];tr=r['bulk_and_reduced_transitions'];tb=tr['bulk_Higgs_ordering_temperature_GeV'];tw=r['canonical_wall_zero_mode_onset_controls'][-1]['temperature_GeV'];v=r['inputs']['v'];k0=np.sqrt((r['inputs']['lam']+r['inputs']['kappa']**2/r['inputs']['H'])/2)
fig,ax=plt.subplots(2,2,figsize=(14,8),layout='constrained')
T=np.array([x['temperature_GeV'] for x in p]);sigma=np.array([x['tension_GeV3'] for x in p]);ax[0,0].plot(T,sigma/1e11,'o-');ax[0,0].set(xlabel='Temperature [GeV]',ylabel='Tension [10¹¹ GeV³]',title='Canonical three-field thermal wall')
z=[x for x in p if 139<x['temperature_GeV']<141];tx=np.array([1000*(x['temperature_GeV']-tb) for x in z]);ax[0,1].plot(tx,[x['central_Higgs_GeV'] for x in z],'o-',label='Wall center');ax[0,1].plot(tx,[x['bulk']['h']*v for x in z],'s--',label='Bulk');ax[0,1].axvspan(0,1000*(tw-tb),alpha=.16,color='orange',label='Wall-only Higgs phase');ax[0,1].axvline(1000*(tw-tb),ls=':',color='black');ax[0,1].set(xlabel='T − bulk Higgs onset [MeV]',ylabel='Higgs radial field [GeV]',title='Localized ordering precedes bulk ordering');ax[0,1].legend(fontsize=8)
for x in p:
 if 'condensation_energy' not in x:continue
 q=x['profile'];coord=np.array(q['x'])/(v*k0);ax[1,0].plot(coord,q['Higgs_GeV'],label='ΔT = %.2f MeV'%(1000*(x['temperature_GeV']-tb)))
ax[1,0].set(xlim=(0,7),xlabel='Distance from center [GeV⁻¹]',ylabel='Higgs radial field [GeV]',title='Broad Higgs tails around a narrow source core');ax[1,0].legend(fontsize=8)
z=[x for x in p if 'condensation_energy' in x];d=np.array([1000*(tw-x['temperature_GeV']) for x in z]);e=np.array([-x['condensation_energy']['energy_difference_GeV3'] for x in z]);pr=np.array([-x['leading_PT_projection']['predicted_condensation_energy_GeV3'] for x in z]);rb=np.array([-x['matched_Robin_defect']['predicted_condensation_energy_GeV3'] for x in z]);ax[1,1].loglog(d,e,'o-',label='Canonical action gain');ax[1,1].loglog(d,pr,'s--',label='One-mode quartic projection');ax[1,1].loglog(d,rb,'^:',label='Matched nonlinear Robin tail');ax[1,1].set(xlabel='Wall onset − T [MeV]',ylabel='Action gain per area [GeV³]',title='Near-onset condensation energy');ax[1,1].legend(fontsize=8)
fig.suptitle('Cooling source walls: exact bulk polynomial phases, numerical canonical profiles\nDeclared quadratic thermal masses; no gauge-resummed plasma or real-time damping',fontsize=14)
fig.savefig(out/'wall_cooling.png',dpi=140);plt.close(fig)
