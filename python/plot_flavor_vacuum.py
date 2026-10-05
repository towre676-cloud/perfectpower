"""Scientific figure for the constructed vacuum and its coupling sensitivity."""
from pathlib import Path
import json
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from perfectpower.cyclotomic_vacuum import phase_potential, fourier_coefficients

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'receipts/flavor_vacuum'
potential = phase_potential(60, (-1, 3, 0, -1))
f = np.array(list(map(float, fourier_coefficients(potential))))
degrees = np.linspace(0, 180, 6001); theta = np.radians(degrees)
energy = np.cos(theta[:, None] * np.arange(len(f))[None, :]) @ f
energy -= energy.min()
perturb = json.loads((OUT / 'perturbations.json').read_text())
fig, axes = plt.subplots(1, 2, figsize=(13.6, 5.2), layout='constrained')
ax = axes[0]; ax.plot(degrees, energy, color='#203f69', linewidth=2)
ax.axvline(66, color='#a82a39', linestyle='--', linewidth=1.3)
ax.scatter([66], [0], color='#a82a39', s=55, zorder=5)
ax.annotate('Exact global minimum\n66° (CP partner: −66°)', xy=(66, 0), xytext=(78, 1.4), arrowprops={'arrowstyle':'->', 'color':'#a82a39'}, color='#a82a39')
ax.set(xlabel='Angular field θ (degrees)', ylabel='Potential above global minimum (arbitrary units)', title='Six rational harmonics select the candidate', xlim=(0, 180))
ax.grid(alpha=.17)
ax = axes[1]
for i, row in enumerate(perturb['generic_fourier']):
    lo, hi = np.array(row['Vub68_given_valid_chart']) * 1000
    ax.plot([lo, hi], [i, i], linewidth=8, solid_capstyle='round', color=['#6398ab','#2f718d','#203f69'][i])
    ax.scatter([(lo + hi) / 2], [i], color='white', edgecolor='#203f69', zorder=4)
ax.axvline(.003521442182760114 * 1000, color='#a82a39', linestyle='--', label='Unperturbed candidate')
ax.set_yticks(range(3), ['0.01% coupling noise', '0.1% coupling noise', '1% coupling noise'])
ax.set(xlabel='|Vub| × 10³', title='Sensitivity without enforcing coupling relations', ylim=(-.6, 2.6))
ax.grid(axis='x', alpha=.17); ax.legend(loc='upper left', frameon=False)
fig.suptitle('A constructed vacuum-selection mechanism — exact minima, conditional physics', fontsize=15, fontweight='bold')
fig.savefig(OUT / 'vacuum_selection.png', dpi=180)
print(OUT / 'vacuum_selection.png')
