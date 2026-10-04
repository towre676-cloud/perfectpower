"""Actual-curve symplectic period, deformation, canonical metric corpus."""
import json,hashlib
from pathlib import Path
from perfectpower.conformal_mesh import hyperelliptic_mesh
from perfectpower.surface_periods import symplectic_period_matrix,integrate_path,bergman_metric,jacobian_coordinates
import numpy as np
root=Path(__file__).resolve().parents[1];out=root/'receipts/symplectic_periods';out.mkdir(exist_ok=True)
cases=[('square_torus',[-1,0,0,0,1]),('original_genus_two',[0,-1,0,0,0,1]),
       ('real_genus_two',[0,4,0,-5,0,1]),('genus_three',[-1,0,0,0,0,0,0,1]),
       ('genus_four',[-1,0,0,0,0,0,0,0,0,1]),('mixed_roots_genus_two',[0,-2,0,-1,0,1])]
summary=[]
decode=lambda rows:np.array([[complex(*z) for z in row] for row in rows])
for name,coeff in cases:
    mesh=hyperelliptic_mesh(coeff,6)
    p=symplectic_period_matrix(mesh,1e-10)
    q=symplectic_period_matrix(mesh,1e-11,(.2,.3,.5))
    deformation=float(np.max(np.abs(decode(p['generator_periods'])-decode(q['generator_periods']))))
    p['contour_deformation_maximum_difference']=deformation
    p['canonical_metric_samples']=[bergman_metric(p,z) for z in [.3+.7j,.6+.8j,2+1j]]
    path=integrate_path(coeff,2,[.3+.7j,.6+.8j]);p['open_path']=path;p['abel_jacobi']=jacobian_coordinates(p,path)
    (out/(name+'.json')).write_text(json.dumps(p,separators=(',',':'))+'\n')
    row={'name':name,'genus':p['genus'],'cycles':len(p['cycles']),
         'symmetry_residual':p['symmetry_residual'],'first_bilinear_relative_residual':p['first_bilinear_relative_residual'],
         'minimum_imaginary_eigenvalue':min(p['imaginary_part_eigenvalues']),
         'contour_deformation_maximum_difference':deformation,'A_condition_number':p['A_condition_number']}
    print(row,flush=True);summary.append(row)
paths=[]
for coeff,d in [([-1,0,0,1],3),([0,-1,2,-1,0,1,-2,1],2)]:
    paths.append(integrate_path(coeff,d,[.3+.7j,.6+.8j]))
(out/'general_paths.json').write_text(json.dumps(paths,indent=2)+'\n')
(out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
(out/'validation.json').write_text(json.dumps({p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(out.glob('*.json')) if p.name!='validation.json'},indent=2)+'\n')
