"""Plots for the nonlinear second-harmonic radiation of the wall shape mode."""
from pathlib import Path
import json
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

root=Path(__file__).resolve().parents[1]
r=json.loads((root/'receipts/flavor_cosmology/wall_shape_radiation.json').read_text())
plt.rcParams.update({'font.size':13,'axes.spines.top':False,'axes.spines.right':False})
fig,axes=plt.subplots(1,2,figsize=(12,4.4),constrained_layout=True)
a=axes[0];slope=r['pure_kink']['closed_form']['Gamma_NL_over_A2']
for run,c in zip(r['time_domain_kink']['runs'],('#1f77b4','#d95f02')):
    t=np.array(run['envelope_t']);A=np.array(run['envelope_A'])
    a.plot(t,1/A**2-1/A[0]**2,'o',ms=2.5,color=c,label=r'nonlinear simulation, $A_0=%.2f$'%run['A0'])
    a.plot(t,slope*(t-t[0]),'-',lw=1,color='grey')
a.set(xlabel=r'$t$ [units of $1/v$]',ylabel=r'$1/A^2-1/A_0^2$',title=r'Pure kink: $d(1/A^2)/dt$ vs closed form (grey)');a.legend(frameon=False,fontsize=10)
a=axes[1];p=r['physical'];d=np.geomspace(1e-5,1e4,200)
a.loglog(d,p['Gamma_NL_GeV_per_A2']*(d/p['peak_phi_per_unit_A_GeV'])**2,label='second harmonic (source quanta)')
a.axhline(p['linear_Higgs_Gamma_GeV'],color='#c85d20',label='linear single-Higgs width')
a.axvline(p['crossover_peak_field_GeV'],color='grey',ls=':',lw=1)
a.set(xlabel=r'peak shape-mode field $\delta\phi$ [GeV]',ylabel=r'energy loss rate $\Gamma$ [GeV]',title='Coupled wall: nonlinear vs linear decay');a.legend(frameon=False,fontsize=10)
fig.savefig(root/'receipts/flavor_cosmology/wall_shape_radiation.png',dpi=170)
