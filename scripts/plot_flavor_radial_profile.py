"""Publication figure: complete logarithmic-quartic phase geometry."""
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from scipy.special import lambertw
ROOT=Path(__file__).resolve().parents[1]

def main():
    plt.rcParams.update({'font.size':12,'axes.spines.top':False,'axes.spines.right':False,'figure.facecolor':'white','svg.hashsalt':'PerfectPower-radial-profile-1'})
    fig,axes=plt.subplots(1,2,figsize=(12,4.7),layout='constrained');h=np.linspace(0,1.18,501);y=h*h
    controls=[(-.34,'Broken minimum metastable','#527b96'),(-1/(2*np.sqrt(np.e)),'Equal radial minima','#6a4c93'),(-.1,'Origin metastable','#c27727')]
    for eta,label,color in controls:
        values=np.zeros_like(y);mask=y>0;values[mask]=(y[mask]**2*(np.log(y[mask])-.5)-2*eta*y[mask])/4
        axes[0].plot(h,values,label=label,color=color,lw=2)
    axes[0].axhline(0,color='#aaa',lw=.7);axes[0].set(xlabel=r'$h/s$',ylabel=r'$V/(d s^4)$',title='Radial energy and the barrier',ylim=(-.09,.09));axes[0].legend(fontsize=10,loc='upper left')
    eta=np.linspace(-1/np.e+1e-8,.13,600);stable=np.exp(.5*lambertw(eta,0).real);axes[1].plot(eta,stable,color='#c27727',lw=2.3,label='Broken radial minimum')
    negative=eta[eta<0];barrier=np.exp(.5*lambertw(negative,-1).real);axes[1].plot(negative,barrier,'--',color='#527b96',lw=2,label='Radial barrier')
    axes[1].plot([-.4,0],[0,0],color='#6a4c93',lw=2,label='Locally stable origin');axes[1].plot([0,.13],[0,0],'--',color='#6a4c93',lw=1.5)
    for x,label in [(-1/np.e,'Fold'),(-1/(2*np.sqrt(np.e)),'Coexistence'),(0,'Origin spinodal')]:
        axes[1].axvline(x,color='#aaa',lw=.8);axes[1].text(x+.006,1.08,label,rotation=90,va='top',fontsize=10)
    axes[1].set(xlabel=r'Control $\eta$',ylabel=r'Radius $h/s$',title='Every positive stationary branch',xlim=(-.4,.13),ylim=(-.035,1.16));axes[1].legend(fontsize=10,loc='center right')
    path=ROOT/'receipts/m22_interactions/flavor_radial_profile.png';fig.savefig(path,dpi=180)
    svg=path.with_suffix('.svg');fig.savefig(svg,metadata={'Date':'2026-10-07'});plt.close(fig)
    svg.write_text('\n'.join(line.rstrip() for line in svg.read_text().splitlines())+'\n');print(path)

if __name__=='__main__':main()
