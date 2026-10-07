"""Exact finite local admissibility for integral polynomial values.

An integer Bezout identity isolates all exceptional primes. Local root sets
are built by prime-power lifting. Admissibility means absence of a fixed
prime-power divisor; it is not a density or integral-point theorem.
"""
from fractions import Fraction as Q
from math import gcd, lcm, isqrt
import hashlib
import json
from . import polyalg as P
from .coefficient_charts import factor_integer
from .divisor_square import WorkLimit

UPSTREAM = {'repository':'https://github.com/openai/math',
            'commit':'adc7f1241b42e322a6451854ab7e4b4c146bf78a',
            'path':'lean/OAI/NumberTheory/PowerFree/Sieve.lean','license':'Apache-2.0'}


def _positive_budget(v,name,cap):
    if type(v) is not int or not 1 <= v <= cap:
        raise ValueError(f'{name} must be an integer in [1,{cap}]')
    return v


def _coefficients(coefficients):
    if not isinstance(coefficients,(list,tuple)) or not coefficients:
        raise ValueError('nonempty ascending integer coefficient list required')
    if len(coefficients)>64: raise WorkLimit('coefficient list budget exceeded')
    if any(type(c) is not int for c in coefficients):
        raise ValueError('coefficients must be integers')
    f=P.poly(coefficients)
    if P.degree(f)<1: raise ValueError('nonconstant polynomial required')
    if P.degree(f)>32 or max(abs(int(c)).bit_length() for c in f)>512:
        raise WorkLimit('polynomial degree or coefficient bit budget exceeded')
    return tuple(int(c) for c in f)


def _bounded(*polys):
    if any(max(max(c.numerator.bit_length(),c.denominator.bit_length()) for c in p)>16384 for p in polys):
        raise WorkLimit('Bezout intermediate bit budget exceeded')


def bezout_certificate(coefficients):
    f=P.poly(_coefficients(coefficients)); a,b=f,P.derivative(f)
    u0,u1,v0,v1=P.ONE,P.ZERO,P.ZERO,P.ONE
    while not P.is_zero(b):
        q,r=P.divmod_poly(a,b)
        a,b=b,r
        u0,u1=u1,P.subtract(u0,P.mul(q,u1))
        v0,v1=v1,P.subtract(v0,P.mul(q,v1))
        _bounded(a,b,u0,u1,v0,v1)
    if P.degree(a)!=0:
        raise ValueError('repeated rational factor: no nonzero derivative Bezout certificate')
    u=P.scale(u0,1/a[0]);v=P.scale(v0,1/a[0])
    D=lcm(*(c.denominator for c in (*u,*v)))
    ui=tuple(int(c*D) for c in u);vi=tuple(int(c*D) for c in v)
    common=gcd(D,gcd(*ui,*vi)); R=D//common
    ui=tuple(c//common for c in ui);vi=tuple(c//common for c in vi)
    if P.add(P.mul(P.poly(ui),f),P.mul(P.poly(vi),P.derivative(f))) != P.poly((R,)):
        raise ArithmeticError('Bezout construction failed')
    return {'u':list(ui),'v':list(vi),'constant':R}


def _prime(n):
    return n>=2 and all(n%d for d in range(2,isqrt(n)+1))


def root_lifts(coefficients,prime,exponent,*,modulus_limit=4096,work_limit=100000):
    """Full lifting tree, including singular roots with zero or many children."""
    f=_coefficients(coefficients)
    if type(prime) is not int or not 2<=prime<=65536 or not _prime(prime):
        raise ValueError('prime must be a prime integer at most 65536')
    _positive_budget(exponent,'exponent',64)
    _positive_budget(modulus_limit,'modulus_limit',65536)
    _positive_budget(work_limit,'work_limit',2000000)
    if prime**exponent>modulus_limit: raise WorkLimit('prime-power modulus budget exceeded')
    used=prime
    if used>work_limit:raise WorkLimit('root lifting work budget exceeded')
    roots=[r for r in range(prime) if P.evaluate(f,r)%prime==0]
    levels=[{'power':1,'modulus':prime,'roots':roots.copy()}];modulus=prime
    for e in range(2,exponent+1):
        used+=len(roots)*prime
        if used>work_limit:raise WorkLimit('root lifting work budget exceeded')
        next_modulus=modulus*prime
        roots=sorted(r+t*modulus for r in roots for t in range(prime)
                     if P.evaluate(f,r+t*modulus)%next_modulus==0)
        modulus=next_modulus
        levels.append({'power':e,'modulus':modulus,'roots':roots.copy()})
    return {'prime':prime,'exponent':exponent,'modulus':modulus,
            'roots':roots,'rho':len(roots),'local_factor':str(1-Q(len(roots),modulus)),
            'levels':levels,'work':used}


def local_admissibility(coefficients,exponent=2,*,factor_limit=100000,
                        modulus_limit=4096,work_limit=100000):
    f=_coefficients(coefficients);_positive_budget(exponent,'exponent',64)
    _positive_budget(factor_limit,'factor_limit',1000000)
    _positive_budget(modulus_limit,'modulus_limit',65536)
    _positive_budget(work_limit,'work_limit',2000000)
    cert=bezout_certificate(f);R=cert['constant']
    factors=factor_integer(abs(R),work_limit=factor_limit)
    degree=len(f)-1
    exceptional=sorted(set(factors)|{p for p in range(2,degree+1) if _prime(p)})
    rows=[];used=0
    for p in exceptional:
        row=root_lifts(f,p,exponent,modulus_limit=modulus_limit,work_limit=work_limit)
        used+=row['work']
        if used>work_limit:raise WorkLimit('total local root work budget exceeded')
        rows.append(row)
    obstruction=next((r['prime'] for r in rows if r['rho']==r['modulus']),None)
    product=Q(1)
    for row in rows:product*=Q(row['local_factor'])
    return {'schema':'pp-power-free-local/1','coefficients':list(f),'exponent':exponent,
            'degree':degree,'bezout':cert,'constant_factors':[[p,e] for p,e in sorted(factors.items())],
            'exceptional_primes':exceptional,'local_roots':rows,
            'locally_admissible':obstruction is None,'fixed_divisor_prime':obstruction,
            'exceptional_factor_product':str(product),'root_work':used,
            'complete':True,'execution_verified':False,'density_proved':False,
            'scope':'all-prime absence or presence of a fixed prime-power divisor; no global density or point classification',
            'upstream':UPSTREAM.copy()}


def power_free_wheel(coefficients,exponent=2,primes=(2,3,5),*,lo=None,hi=None,
                     period_limit=1000000,work_limit=2000000,modulus_limit=4096):
    """Exact finite-prime avoidance domain; counts use floor quotients."""
    f=_coefficients(coefficients);_positive_budget(exponent,'exponent',64)
    _positive_budget(period_limit,'period_limit',1000000)
    _positive_budget(work_limit,'work_limit',2000000)
    if not isinstance(primes,(list,tuple)) or not primes:raise ValueError('nonempty prime list required')
    if len(primes)>32:raise WorkLimit('wheel prime count budget exceeded')
    if any(type(p) is not int for p in primes):raise ValueError('integer primes required')
    selected=sorted(set(primes));period=1;allowed=[0];rows=[];work=0
    for p in selected:
        row=root_lifts(f,p,exponent,modulus_limit=modulus_limit,work_limit=work_limit)
        q=row['modulus'];new_period=period*q
        if new_period>period_limit:raise WorkLimit('wheel period budget exceeded')
        work+=row['work']+len(allowed)*q
        if work>work_limit:raise WorkLimit('wheel expansion work budget exceeded')
        forbidden=set(row['roots'])
        allowed=sorted(r+t*period for r in allowed for t in range(q) if (r+t*period)%q not in forbidden)
        period=new_period;rows.append(row)
    out={'schema':'pp-power-free-wheel/1','coefficients':list(f),'exponent':exponent,
         'primes':selected,'local_roots':rows,'modulus':period,'allowed':allowed,
         'density':str(Q(len(allowed),period)),'global_obstruction':not allowed,
         'complete_for_selected_primes':True,'execution_verified':False,
         'scope':'finite-prime avoidance; survivors need not be globally power-free','work':work}
    if lo is not None or hi is not None:
        if type(lo) is not int or type(hi) is not int or lo>hi:raise ValueError('ordered closed integer interval required')
        out['interval']=[lo,hi]
        out['count']=sum((hi-r)//period-(lo-1-r)//period for r in allowed)
    return out


def _poly(cs):
    terms=[]
    for i,c in enumerate(cs):
        if c:terms.append(f'C ({c})' if i==0 else f'C ({c}) * X' if i==1 else f'C ({c}) * X^{i}')
    return ' + '.join(terms) or '0'


def _finset(xs):
    return '({' + ','.join(map(str,xs)) + '} : Finset ℕ)' if xs else '(∅ : Finset ℕ)'


def native_certificate(coefficients,exponent=2,**budgets):
    packet=local_admissibility(coefficients,exponent,**budgets)
    if any(row['modulus']>4096 for row in packet['local_roots']):
        raise WorkLimit('kernel root enumeration modulus budget exceeded')
    digest=hashlib.sha256(json.dumps(packet,sort_keys=True,separators=(',',':')).encode()).hexdigest()[:16]
    ns='PerfectPower.PowerFreePacket_'+digest;f=packet['coefficients'];bc=packet['bezout'];k=exponent
    factors=[prime for prime,e in packet['constant_factors'] for _ in range(e)]
    exceptions=sorted(set(factors)|set(range(len(f))))
    declarations=[];names=[]
    for row in packet['local_roots']:
        p=row['prime'];q=row['modulus'];r=row['rho'];roots=_finset(row['roots'])
        declarations.append(f'''theorem roots_{p}_checked : rootResidues coefficients {q} = {roots} := by decide
theorem rho_{p}_checked : rho source ({p}^{k}) = {r} := by
  rw [source_polynomial, rho_coefficients, show ({p}^{k} : ℕ) = {q} by norm_num, roots_{p}_checked]
  decide
theorem roots_{p}_complete (x : ℤ) : ({q} : ℤ) ∣ source.eval x ↔
    (x % {q}).toNat ∈ {roots} := by
  rw [source_polynomial, PerfectPower.NativePolynomialSquare.polynomial_eval]
  have h := rootResidues_complete coefficients {q} (by norm_num) x
  norm_num only [Nat.cast_ofNat] at h
  rwa [roots_{p}_checked] at h
''');names.extend([f'roots_{p}_checked',f'rho_{p}_checked',f'roots_{p}_complete'])
    status='locally_admissible_checked' if packet['locally_admissible'] else 'fixed_divisor_checked'
    if packet['locally_admissible']:
        result=f'''theorem {status} : LocallyAdmissible source {k} := by
  apply (admissible_iff_finite source u v {bc['constant']} {k} bezout_checked (by norm_num) (by norm_num)).mpr
  rw [degree_checked, exceptional_checked]
  intro p hp hprime
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
'''
        ps=exceptions
        result+='  rcases hp with '+ ' | '.join('rfl' for _ in ps)+'\n'
        for prime in ps:
            result+=(f'  · rw [rho_{prime}_checked]; norm_num\n' if prime in packet['exceptional_primes'] else '  · norm_num at hprime\n')
    else:
        p=packet['fixed_divisor_prime']
        result=f'''theorem {status} (x : ℤ) : ¬ PowerFree {k} (source.eval x) := by
  apply fixed_divisor_obstruction source {p} {k} (by norm_num)
  rw [rho_{p}_checked]
  norm_num
'''
    names=[*names,'source_polynomial','degree_checked','bezout_checked','exceptional_checked',status]
    source=f'''import PerfectPower.PowerFreeLocal
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
namespace {ns}
open Polynomial PerfectPower.PowerFreeLocal
def coefficients : List ℤ := {f}
noncomputable def source : Polynomial ℤ := {_poly(f)}
noncomputable def u : Polynomial ℤ := {_poly(bc['u'])}
noncomputable def v : Polynomial ℤ := {_poly(bc['v'])}
theorem source_polynomial : source = PerfectPower.NativePolynomialSquare.polynomial coefficients := by
  norm_num [source, coefficients, PerfectPower.NativePolynomialSquare.polynomial]
  <;> ring
theorem degree_checked : source.natDegree = {len(f)-1} := by
  unfold source
  compute_degree <;> norm_num
theorem bezout_checked : Bezout source u v {bc['constant']} := by
  norm_num [Bezout,source,u,v,Polynomial.derivative_add,Polynomial.derivative_mul,Polynomial.derivative_pow]
  <;> ring
theorem exceptional_checked : exceptional {bc['constant']} {len(f)-1} = {_finset(exceptions)} := by
  have hf : ({factors} : List ℕ).Perm ({bc['constant']} : ℤ).natAbs.primeFactorsList := by
    apply Nat.primeFactorsList_unique
    · norm_num
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      {'' if not factors else 'rcases hp with ' + ' | '.join('rfl' for _ in factors)}
      {'' if not factors else 'all_goals norm_num'}
  have hs := (List.toFinset_eq_of_perm _ _ hf).symm
  rw [exceptional, hs]
  decide
{''.join(declarations)}
{result}
end {ns}
'''
    source='\n'.join(line.rstrip() for line in source.splitlines())+'\n'
    packet['lean']={'namespace':ns,'source':source,'source_sha256':hashlib.sha256(source.encode()).hexdigest(),
                    'theorem':ns+'.'+status,'declarations':[ns+'.'+n for n in names],
                    'kernel_checked':False}
    return packet
