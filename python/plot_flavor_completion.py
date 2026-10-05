"""Rebuild numerical scientific figures from the retained completion receipts."""
from pathlib import Path
import json
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'receipts/flavor_completion'


def main():
    scalar=json.loads((OUT/'single_scalar_loops.json').read_text())['cases']
    soft=json.loads((OUT/'soft_selection.json').read_text())['cases']
    texture=json.loads((OUT/'quark_texture_counterexamples.json').read_text())
    fig,axes=plt.subplots(1,3,figsize=(15,4.4),layout='constrained')
    for lock in (0.,.1,1.):
        rows=[x for x in scalar if x['lock']==lock and x['mu_over_tree_mass']==1]
        axes[0].plot([x['Lambda_over_f'] for x in rows],[100*x['relative_coefficient_change'] for x in rows],marker='o',label=f'lock={lock:g}')
    axes[0].set(xlabel='Lambda / f',ylabel='Coefficient change (%)',title='Scalar-only one-loop examples')
    axes[0].legend(fontsize=8); axes[0].axhline(-1,color='.5',ls=':',lw=1)
    eps=[];phase=[];aux=[];holo=[]
    c=(3-np.sqrt(5))/2
    for study in soft:
        row=next(x for x in study['branches'] if x['root_power']==11)
        eps.append(study['epsilon']);phase.append((row['coefficient_from_angle']/c-1)*100)
        aux.append((row['coefficient_from_auxiliary_operator']/c-1)*100)
        holo.append((row['holomorphic_T_magnitude']/c-1)*100)
    axes[1].semilogx(eps,phase,'o-',label='Angle readout')
    axes[1].semilogx(eps,aux,'o-',label='Real auxiliary readout')
    axes[1].semilogx(eps,holo,'o-',label='Holomorphic T magnitude')
    axes[1].set(xlabel='Scalar selector strength',ylabel='Coefficient change (%)',title='Actual auxiliary-field relaxation')
    axes[1].legend(fontsize=8)
    rows=texture['cases']
    axes[2].plot([x['independent_13_coefficient'] for x in rows],[x['observables']['Vub'] for x in rows],'o-')
    axes[2].axhline(texture['target_chart']['Vub'],color='darkred',ls='--',label='Original conditional forecast')
    axes[2].set(xlabel='Independent 1-3 texture coefficient',ylabel='|Vub|',title='Same Vus and Vcb, different Vub')
    axes[2].legend(fontsize=8)
    for ax in axes: ax.grid(alpha=.2)
    fig.savefig(OUT/'completion_results.png',dpi=160)
    plt.close(fig)


if __name__=='__main__':main()
