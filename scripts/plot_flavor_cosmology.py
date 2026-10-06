"""Plot saved trial-path data only; no model or vacuum discovery."""
from pathlib import Path
from fractions import Fraction
import json
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

root = Path(__file__).resolve().parents[1]
r = json.loads((root/"receipts/flavor_cosmology/tree_decay.json").read_text())
best = r["candidates"][r["best_candidate_rank"]]
fig,axes = plt.subplots(1,2,figsize=(12,4.3))
q = np.linspace(0,1,301)
for c,label in [(r["candidates"][-1],"Original endpoint"),(best,"Symmetry-related endpoint")]:
    p = [float(Fraction(v)) for v in c["path_potential_coefficients"]]
    axes[0].plot(q,np.polynomial.polynomial.polyval(q,p),label=label,lw=2)
axes[0].axhline(0,color="black",lw=.6)
axes[0].set(xlabel="Position along the source path",ylabel="Tree potential above the CP-breaking branch")
axes[0].legend(frameon=False)
rows = r["completion"]["mass_scan"]
axes[1].loglog([x["mediator_mass"] for x in rows],
              [100*(x["ratio_to_source_candidate"]-1) for x in rows],"o-",lw=2)
axes[1].set(xlabel="Mediator mass in declared model units",ylabel="Extra trial action (%)")
axes[1].grid(alpha=.2,which="both")
fig.suptitle("Published flavor action: trial decay paths and mediator kinetic cost",fontsize=13)
fig.text(.5,.015,"Tree-action trial profiles; no lifetime or physical nucleation rate is inferred.",ha="center",fontsize=9)
fig.tight_layout(rect=[0,.045,1,.93])
fig.savefig(root/"receipts/flavor_cosmology/tree_decay.png",dpi=180)

