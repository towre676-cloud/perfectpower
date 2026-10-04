"""Render actual computed torus cells; no illustrative surface substitution."""
import json
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
matplotlib.rcParams['svg.hashsalt']='perfectpower-analytic-geometry-v1'
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon
from perfectpower.intrinsic_torus import clip


def render(output='docs/figures/intrinsic_voronoi.svg',png=None):
    rows=json.loads(Path('receipts/analytic_geometry/legendre_intrinsic_voronoi.json').read_text())
    selected=[rows[i] for i in (0,3,6)]
    colors=['#75d7d0','#ffbb77','#bdabef','#6bc6ed','#df8fae','#8ace9b','#e4d577','#85a3ef','#ed937d','#97dcd6','#ccade0','#bad986']
    fig,axes=plt.subplots(1,3,figsize=(16,9),facecolor='#101923')
    fig.subplots_adjust(left=.045,right=.96,bottom=.31,top=.79,wspace=.27)
    for ax,p in zip(axes,selected):
        h=p['height'];ax.set_facecolor('#172536')
        for c in p['cells']:
            poly=c['lifted_polygon']
            for a in (-1,0,1):
                for b in (-1,0,1):
                    shifted=[[x+a,y+b*h] for x,y in poly]
                    for n,bound in (([-1,0],0),([1,0],1),([0,-1],0),([0,1],h)):
                        shifted=clip(shifted,n,bound)
                    if len(shifted)>2:ax.add_patch(Polygon(shifted,closed=True,facecolor=colors[c['site']],edgecolor='#102133',linewidth=1.3))
        ax.scatter([s[0] for s in p['sites']],[s[1] for s in p['sites']],s=19,c='#122030',zorder=4)
        ax.set_xlim(0,1);ax.set_ylim(0,h);ax.set_aspect('equal');ax.tick_params(colors='#bed5e5');
        for spine in ax.spines.values():spine.set_color('#bed5e5')
        ax.set_title(f"lambda = {p['lambda_parameter']}\nIm(tau) = {h:.8f}",color='white',fontsize=14,pad=14)
        ax.set_xlabel('normalized real period coordinate',color='#bed5e5')
        ax.set_ylabel('normalized imaginary period coordinate',color='#bed5e5')
    fig.text(.045,.925,'INTRINSIC GEOMETRY OF THE ACTUAL COMPLEX CURVE',color='#e8f5fa',fontsize=23,weight='bold')
    fig.text(.045,.865,'Legendre period lattices • continuous geodesic Voronoi cells • opposite sides identified',color='#89ccc9',fontsize=15)
    fig.text(.045,.235,'Each diagram: 12 cells, 24 quotient vertices, 36 quotient edges. Euler characteristic 0; total face charge 0.',color='#e4edf4',fontsize=14)
    fig.text(.045,.179,'The lattice comes from enclosed analytic periods. Theta inversion places all 84 saved sites back on their curves.',color='#bcd0df',fontsize=13)
    fig.text(.045,.124,'General cyclic curves: 68 closed continued-sheet period calculations. Genus-two and genus-three meshes retain infinity and sheet gluing.',color='#bcd0df',fontsize=12)
    fig.text(.045,.069,'Flat-torus cells use floating polygon predicates. Higher-genus cells use intrinsic heat distances on a conformal metric approximation.',color='#e2bc8b',fontsize=12)
    fig.savefig(output,facecolor=fig.get_facecolor(),metadata={'Date':None})
    target=Path(output);target.write_text('\n'.join(line.rstrip() for line in target.read_text().splitlines())+'\n')
    if png:fig.savefig(png,dpi=120,facecolor=fig.get_facecolor())
    plt.close(fig)
if __name__=='__main__':render(png='/workspace/scratch/99b8b68fdd43/deliverables/intrinsic_voronoi.png')
