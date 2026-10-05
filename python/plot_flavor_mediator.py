"""Scientific plots of canonical mediator matching and the orientation boundary."""
from pathlib import Path
import json
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'receipts/flavor_mediator'


def main():
    rows=json.loads((OUT/'adjoint_matching.json').read_text())['cases']
    transfers=json.loads((OUT/'conditional_frame_transfer.json').read_text())['cases']
    c=(3-np.sqrt(5))/2
    fig,axes=plt.subplots(1,2,figsize=(10.5,4.2),layout='constrained')
    for gu in (0.,.1,.2):
        group=[r for r in rows if r['parameters']['flavon_scale']==1 and r['up_adjoint_coupling']==gu]
        axes[0].plot([r['down_adjoint_coupling'] for r in group],[r['observables']['depth'] for r in group],
                     'o-',label=f'Up coupling = {gu:g}')
    axes[0].axhline(c,color='darkred',ls='--',label='Golden target')
    axes[0].set(xlabel='Down adjoint coupling',ylabel='Observable mixing coefficient',
                title='Adjoint background does not enforce the relation')
    axes[0].legend(fontsize=8)
    axes[1].scatter([r['flavon_column_scale'] for r in transfers],[r['observables']['depth'] for r in transfers],
                    label='Exact canonical frame transfer',s=35)
    axes[1].axhline(c,color='darkred',ls='--',label='Initialized golden frame')
    axes[1].set(xlabel='Flavon column scale',ylabel='Observable mixing coefficient',
                title='Orthogonal frame survives mass normalization',ylim=(.37,.395))
    axes[1].legend(fontsize=8)
    for ax in axes:ax.grid(alpha=.2)
    fig.savefig(OUT/'mediator_results.png',dpi=180);plt.close(fig)


if __name__=='__main__':main()
