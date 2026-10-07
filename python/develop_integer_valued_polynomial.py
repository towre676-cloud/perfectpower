"""Reproduce denominator-aware arithmetic and source-bound native packets."""
from pathlib import Path
from fractions import Fraction as Q
import hashlib,json,math,random
from perfectpower.integer_valued_polynomial import analyze,native_certificate,gamma_packet

OUT=Path('receipts/integer_valued_polynomial');OUT.mkdir(parents=True,exist_ok=True)
def write(name,obj):(OUT/name).write_text(json.dumps(obj,indent=2)+'\n')
def ev(f,x):
    v=0
    for c in reversed(f):v=v*x+c
    return v
cases=[('triangular',[0,'-1/2','1/2'],{}),('odd_integral',['1/2',0,'1/2'],{}),
 ('odd_obstruction',['7/2',0,'1/2'],{}),('four_charts',[0,'1/6','1/6'],{}),
 ('third_square',[0,0,'1/3'],{}),('third_square_units',[0,0,'1/3'],{'exponent':1}),
 ('even_linear',[0,'1/2'],{}),('empty',['1/2'],{}),('zero',[0],{}),
 ('negative_constant',[-12],{}),('negative_cubic_admissible',[-12],{'exponent':3})]
gamma=[]
for d in [8,16]:
 p=gamma_packet({'kind':'binomial','width':d},interval=[0,10**100],period_limit=1)
 gamma.append(p);cases.append(('binomial_'+str(d),p['rational_coefficients'],{}))
gamma.append(gamma_packet({'kind':'gamma_shift','a':2,'b':3,'shift':4},interval=[0,10**100]))
write('gamma_bridge.json',gamma)
declarations=[];sources=[]
for name,cs,kwargs in cases:
 p=native_certificate(cs,interval=[-10**100,10**100],**kwargs)
 write(name+'.json',p);sources.append(p['lean']['source']);declarations+=p['lean']['declarations']
combined='import PerfectPower.IntegerValuedPolynomial\n'+''.join(s.split('\n',1)[1] for s in sources)+'\n'+''.join('#print axioms '+n+'\n' for n in declarations)
Path('audit/IntegerValuedPolynomialPackets.lean').write_text(combined)
reusable=[]
import re
for n in re.findall(r'^theorem (\w+)',Path('PerfectPower/IntegerValuedPolynomial.lean').read_text(),re.M):reusable.append('PerfectPower.IntegerValuedPolynomial.'+n)
Path('audit/IntegerValuedPolynomial.lean').write_text('import PerfectPower.IntegerValuedPolynomial\n'+''.join('#print axioms '+n+'\n' for n in reusable))
rng=random.Random(71007);census=[];value_checks=0;local_checks=0;chart_checks=0;interval_checks=0
for _ in range(150):
 L=rng.randint(1,12);cs=[str(Q(rng.randint(-10,10),L)) for _ in range(rng.randint(1,7))]
 packet=analyze(cs,interval=[-61,67]);F,L=packet['numerator'],packet['denominator'];d=len(F)-1
 values=[ev(F,x)//L for x in range((d+1)*L) if ev(F,x)%L==0]
 D=math.gcd(*values) if values else 0
 assert D==packet['integer_domain_fixed_divisor']
 assert packet['integral_everywhere']==all(ev(F,x)%L==0 for x in range(L))
 for x in range(-61,68):
  integral=ev(F,x)%L==0
  assert integral==(packet['integral_everywhere'] or x%L in packet['integral_residues']);value_checks+=1
 assert sum(ev(F,x)%L==0 for x in range(-61,68))==packet['integral_input_count'];interval_checks+=1
 for c in packet['charts']:
  for n in [-10**30,-17,-1,0,1,19,10**30]:
   assert ev(F,c['residue']+L*n)==L*ev(c['coefficients'],n);chart_checks+=1
 for p in [2,3,5]:
  for k in [1,2,3]:
   q=p**k
   universal=all(ev(F,x)%(L*q)==0 for x in range(L*q) if ev(F,x)%L==0)
   assert universal==(D%q==0);local_checks+=1
 census.append({'rational_coefficients':cs,'denominator':L,'integer_domain_fixed_divisor':D,
                'integral_everywhere':packet['integral_everywhere'],'integral_residues':packet['integral_residues']})
write('census.json',census)
scaling=[]
for d in [8,16,32,64]:
 p=gamma_packet({'kind':'binomial','width':d},period_limit=1)
 assert p['denominator']==math.factorial(d) and p['integer_domain_fixed_divisor']==1
 scaling.append({'width':d,'denominator':p['denominator'],'numerator_fixed_divisor':p['numerator_fixed_divisor'],
                 'quotient_fixed_divisor':p['integer_domain_fixed_divisor'],'samples':d+1,'residue_enumeration':False})
write('scaling.json',scaling)
summary={'schema':'pp-integer-valued-polynomial-release/1','kernel_checked':False,
 'worked_packets':len(cases),'generated_declarations':len(declarations),'reusable_theorems':len(reusable),
 'census_polynomials':len(census),'signed_domain_checks':value_checks,'quotient_local_checks':local_checks,
 'signed_chart_checks':chart_checks,'interval_count_checks':interval_checks,
 'source_sha256':hashlib.sha256(combined.encode()).hexdigest(),
 'remaining':['generic rational JSON/compiler execution refinement','formal Gamma normalization execution',
              'global power-free density for separable polynomials','efficient high-denominator partial-domain enumeration']}
write('summary.json',summary);print(json.dumps(summary))
