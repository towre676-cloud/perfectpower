"""Rebuild exact fixed-divisor and repeated-factor evidence."""
from pathlib import Path
import hashlib,json,math,random
from perfectpower import polyalg as P
from perfectpower.fixed_divisor import fixed_divisor,admissibility,native_certificate,repeated_power_free,native_repeated_power_free,generalized_choose

OUT=Path('receipts/fixed_divisor');OUT.mkdir(parents=True,exist_ok=True)
def falling(d):
 f=P.ONE
 for j in range(d):f=P.mul(f,P.poly([-j,1]))
 return [int(c) for c in f]
def write(name,obj):(OUT/name).write_text(json.dumps(obj,indent=2)+'\n')
local=[('repeated_admissible',[1,0,2,0,1],{}),('local_without_global',[4,0,4,0,1],{}),
 ('repeated_obstruction',[0,0,1,-2,1],{}),('repeated_cubic_free',[0,0,1,-2,1],{'exponent':3}),
 ('falling_eight',falling(8),{'exponent':8}),('falling_sixteen',falling(16),{}),
 ('odd_progression',[1,0,1],{'start':1,'step':2}),('odd_fixed_prime',[1,0,1],{'start':1,'step':2,'exponent':1}),
 ('negative_progression',[-3,0,2],{'start':-5,'step':-2}),('zero',[0],{}),
 ('negative_constant',[-12],{}),('negative_constant_cubic',[-12],{'exponent':3}),
 ('large_prime',[10007**2],{}),('large_prime_cubic',[10007**2],{'exponent':3}),
 ('constant_progression',[-4,0,1],{'start':2,'step':0})]
repeated=[('square_no_hits',[4,0,4,0,1],2),('square_one_hit',[1,0,2,0,1],2),
 ('square_two_hits',[0,0,1],2),('negative_square',[0,0,-1],2),('square_times_three',[0,0,3],2),
 ('square_times_twelve',[0,0,12],2),('square_times_linear',[0,0,1,1],2),('shifted_cube',[-8,12,-6,1],3)]
packets=[];decls=[];sources=[]
for name,f,kw in local:
 p=native_certificate(f,**kw);write(name+'.json',p);packets.append(p);sources.append(p['lean']['source']);decls+=p['lean']['declarations']
for name,f,k in repeated:
 p=native_repeated_power_free(f,exponent=k);write(name+'.json',p);packets.append(p);sources.append(p['lean']['source']);decls+=p['lean']['declarations']
combined='import PerfectPower.FixedDivisor\n'+''.join(s.split('\n',1)[1] for s in sources)+'\n'+''.join('#print axioms '+n+'\n' for n in decls)
Path('audit/FixedDivisorPackets.lean').write_text(combined)

# Independent Horner, gcd, and full residue enumeration. No producer evaluation reuse.
def ev(f,x):
 v=0
 for c in reversed(f):v=c+x*v
 return v
rng=random.Random(6607);census=[];root_checks=0;newton_checks=0
for _ in range(180):
 f=[rng.randint(-12,12) for _ in range(rng.randrange(1,10))]
 a,b=rng.randint(-7,7),rng.randint(-3,3);p=fixed_divisor(f,start=a,step=b);D=p['fixed_divisor']
 broad=[ev(f,a+b*n) for n in range(-30,31)]
 assert math.gcd(*broad)==D
 assert sum(w*y for w,y in zip(p['sample_bezout_weights'],p['sample_values']))==D
 for n in [-10**12,-19,-1,0,1,21,10**12]:
  assert sum(c*generalized_choose(n,j) for j,c in enumerate(p['forward_differences']))==ev(f,a+b*n);newton_checks+=1
 for prime in [2,3,5,7,11]:
  for k in [1,2,3]:
   q=prime**k;full=all(ev(f,a+b*n)%q==0 for n in range(q))
   assert full==(D%q==0);root_checks+=1
 census.append({'coefficients':f,'start':a,'step':b,'fixed_divisor':D})
write('census.json',census)
# Broad squarefree crosscheck for the finite repeated-factor solver.
def kfree(v,k):
 if not v:return False
 v=abs(v);p=2
 while p*p<=v:
  e=0
  while v%p==0:e+=1;v//=p
  if e>=k:return False
  p=3 if p==2 else p+2
 return True
checks=0
for name,f,k in repeated:
 p=repeated_power_free(f,exponent=k)
 actual=[n for n in range(-150,151) if kfree(ev(f,n),k)]
 assert actual==p['solutions'],(name,actual,p['solutions']);checks+=301
write('scaling.json',[{'degree':d,'sample_count':d+1,'fixed_divisor':fixed_divisor(falling(d))['fixed_divisor'],
                       'expected_factorial':math.factorial(d),'coefficient_content':1} for d in [8,16,32,64,128]])
assert all(r['fixed_divisor']==r['expected_factorial'] for r in json.loads((OUT/'scaling.json').read_text()))
summary={'schema':'pp-fixed-divisor-release/1','kernel_checked':False,'local_packets':len(local),
 'global_repeated_packets':len(repeated),'generated_declarations':len(decls),
 'census_polynomials':len(census),'independent_local_checks':root_checks,'signed_newton_checks':newton_checks,
 'global_repeated_checks':checks,'source_sha256':hashlib.sha256(combined.encode()).hexdigest(),
 'remaining':['global density for separable polynomial values','generic JSON/compiler refinement','formal Newton/binomial execution','formal factorization producer execution']}
write('summary.json',summary);print(json.dumps(summary))
