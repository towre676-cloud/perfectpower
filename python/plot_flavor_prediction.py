"""Plot actual retained forecast draws and withheld PDG measurements."""
from pathlib import Path
import json
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
p=Path(__file__).resolve().parents[1]/'receipts/flavor_prediction'
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':11,'axes.spines.top':False,'axes.spines.right':False})
fig,axes=plt.subplots(1,2,figsize=(12,5.2),layout='constrained')
for ax,key,label,limits in zip(axes,['Vub','sin2beta'],[r'$|V_{ub}|$',r'$\sin(2\beta)$'],[(.001,.008),(.25,1)]):
 for name,color,title in [('smooth','#798597','Smooth coefficient'),('b5','#126b8a','B5 model ensemble')]:
  a=np.load(p/(name+'_draws.npz'))
  ax.hist(a[key],bins=70,range=limits,weights=a['weights'],density=True,histtype='step',lw=2,color=color,label=title)
 held=json.loads((p/'heldout.json').read_text())[key]
 ax.axvspan(held['mean']-held['sigma'],held['mean']+held['sigma'],color='#aab799',alpha=.35,label='Withheld measurement ±1σ')
 locked=json.loads((p/'locked_golden.json').read_text())['predictions'][key]
 ax.axvline(locked['median'],color='#b04c32',lw=2,label='Golden candidate')
 ax.set(xlim=limits,xlabel=label,ylabel='Posterior density')
 ax.grid(axis='y',alpha=.15); ax.legend(frameon=False,fontsize=9)
fig.suptitle('A real-data flavor forecast: the candidate and its competitors',fontsize=17,weight='bold')
fig.text(.5,-.025,'Training: |Vus|, |Vcb|, γ and |Vtd/Vts|.  Retrospective withheld-observable test; numerical inference.',ha='center',fontsize=10)
fig.savefig(p/'prediction_comparison.png',dpi=160,bbox_inches='tight')
