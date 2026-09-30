"""Additional exact receipts; run from package root."""
from engine import *
from pathlib import Path
p=Path('receipts')
quartics=[]
for a,b,c in [(1,0,1),(2,3,1),(1,-3,1),(-1,0,25),(3,2,4)]:
 points=[]
 for u in range(-500,501):
  w=a*u**4+b*u*u+c
  if w<0:continue
  v=isqrt(w)
  if v*v!=w:continue
  for z in sorted({v,-v}):
   X,Y=even_quartic_point(a,b,c,u,z)
   lifts=even_quartic_lifts(a,b,c,X,Y)
   assert (u,z) in lifts
   points.append({'source':[u,z],'image':[X,Y],'all_integral_lifts':[list(t) for t in lifts]})
 quartics.append({'coefficients':[a,b,c],'u_interval':[-500,500],'points':points,'status':'bounded_source_scan_with_exact_fibre_checks'})
(p/'quartic_lifts.json').write_text(json.dumps(quartics,indent=2))
counts=[]
for a in range(1,9):
 for b in range(1,9):
  pairs=monomial_pairs(a,b,100000)
  counts.append({'a':a,'b':b,'N':100000,'positive_count':len(pairs),'first_pairs':pairs[:5],'last_pair':pairs[-1]})
(p/'monomial_counts.json').write_text(json.dumps(counts,indent=2))
print('Quartic models:',len(quartics),'source points:',sum(len(q['points']) for q in quartics),'monomial cases:',len(counts))
