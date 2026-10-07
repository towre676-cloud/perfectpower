"""Reproduce source-bound local arithmetic, wheel counts and native proofs."""
import hashlib
import json
from pathlib import Path
from fractions import Fraction
from perfectpower import polyalg as P
from perfectpower.power_free_local import local_admissibility,power_free_wheel,native_certificate

ROOT=Path(__file__).resolve().parents[1]
CASES=[('cyclotomic_quartic',[1,0,0,0,1],2),('reducible_quartic',[4,0,0,0,1],2),
 ('fixed_square_divisor',[4,0,0,0,4],2),('signed_nonmonic',[-3,0,2],2),
 ('cubic',[3,-3,0,1],2),('branch_quartic',[0,-1,0,0,1],2),
 ('negative_quartic',[-1,0,0,0,-1],2),('degree_eight',[1,0,0,0,0,0,0,0,1],2),
 ('cubic_free_quartic',[4,0,0,0,1],3),('fixed_prime_divisor',[0,1,1],1),
 ('linear_unit_bezout',[-1,1],2)]

def main():
 out=ROOT/'receipts/power_free_local';out.mkdir(parents=True,exist_ok=True)
 sources=[];names=[];packets=[]
 for label,coeff,k in CASES:
  p=native_certificate(coeff,k);packets.append(p)
  (out/(label+'.json')).write_text(json.dumps(p,indent=2)+'\n')
  sources.append(p['lean']['source']);names+=p['lean']['declarations']
 audit='import PerfectPower.PowerFreeLocal\n'+'\n'.join(s.removeprefix('import PerfectPower.PowerFreeLocal\n') for s in sources)+'\n'+'\n'.join('#print axioms '+n for n in names)+'\n'
 (ROOT/'audit/PowerFreeLocalPackets.lean').write_text(audit)
 census=[];checks=0
 for d in range(1,9):
  for a in [-5,-3,-2,-1,1,2,3,5]:
   coeff=[a]+[0]*(d-1)+[1]
   packet=local_admissibility(coeff)
   for prime in [2,3,5,7,11,13,17,19]:
    brute=sum(P.evaluate(coeff,x)%(prime**2)==0 for x in range(prime**2));checks+=1
    if prime not in packet['exceptional_primes']:assert brute<=d
    if packet['locally_admissible']:assert brute<prime**2
   wheel=power_free_wheel(coeff,lo=-100,hi=100)
   assert wheel['count']==sum(all(P.evaluate(coeff,x)%(p*p) for p in [2,3,5]) for x in range(-100,101))
   census.append({'degree':d,'constant':a,'bezout_constant':packet['bezout']['constant'],
     'exceptional_primes':packet['exceptional_primes'],'admissible':packet['locally_admissible'],'wheel_count':wheel['count']})
 (out/'census.json').write_text(json.dumps(census,indent=2)+'\n')
 wheels=[power_free_wheel(c,k,lo=-10**30,hi=10**30) for _,c,k in CASES]
 (out/'huge_interval_wheels.json').write_text(json.dumps(wheels,indent=2)+'\n')
 reusable=['derivative_not_dvd_of_bezout','divided_difference_eval','eval_sub_eq_mul_divided_difference',
 'prime_power_root_unique','map_zmod_ne_zero_of_good','rho_prime_pow_le_degree','admissible_iff_finite',
 'rho_coefficients','eval_mod_dvd','rootResidues_complete','fixed_divisor_obstruction']
 (ROOT/'audit/PowerFreeLocal.lean').write_text('import PerfectPower.PowerFreeLocal\n'+
  '\n'.join('#print axioms PerfectPower.PowerFreeLocal.'+n for n in reusable)+'\n')
 summary={'schema':'pp-power-free-release/1','upstream':packets[0]['upstream'],
  'publication_parent':None,'fixtures':len(CASES),'admissible_fixtures':sum(p['locally_admissible'] for p in packets),
  'obstructed_fixtures':sum(not p['locally_admissible'] for p in packets),'census_polynomials':len(census),
  'independent_prime_square_checks':checks,'huge_interval_width':str(2*10**30+1),
  'reusable_theorems':len(reusable),'generated_declarations':len(names),
  'generated_source_sha256':hashlib.sha256(audit.encode()).hexdigest(),'kernel_checked':False,
  'remaining':['global power-free density','repeated-factor all-prime admissibility','generic JSON interpreter',
    'formal prime-power lifting producer and wheel assembly'],'source_hashes':{}}
 (out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
 print(json.dumps({k:summary[k] for k in ['fixtures','reusable_theorems','generated_declarations','census_polynomials','independent_prime_square_checks']}))

if __name__=='__main__':main()
