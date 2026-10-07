"""Universal divisibility from consecutive values, including repeated factors.

Finite differences expose the integer-valued binomial expansion. A signed
integer combination of the sample values witnesses the gcd in both directions.
Local admissibility is not a global density or existence theorem.
"""
from math import gcd
import hashlib
import json
from . import polyalg as P
from .coefficient_charts import factor_integer
from .divisor_square import WorkLimit


def _coefficients(xs):
    if not isinstance(xs,(list,tuple)) or not xs or any(type(x) is not int for x in xs):
        raise ValueError('nonempty ascending integer coefficients required')
    if len(xs)>129 or max(abs(x).bit_length() for x in xs)>2048:
        raise WorkLimit('degree 128 or coefficient 2048-bit budget exceeded')
    return tuple(int(x) for x in P.poly(xs))


def _egcd(a,b):
    old_r,r=abs(a),abs(b);old_s,s=1,0;old_t,t=0,1
    while r:
        q=old_r//r;old_r,r=r,old_r-q*r;old_s,s=s,old_s-q*s;old_t,t=t,old_t-q*t
    return old_r,old_s*(-1 if a<0 else 1),old_t*(-1 if b<0 else 1)


def fixed_divisor(coefficients,*,start=0,step=1):
    """Exact gcd of every f(start+step*n), n in Z. No factoring or roots."""
    f=_coefficients(coefficients)
    if any(type(x) is not int for x in (start,step)):
        raise ValueError('start and step must be integers')
    if max(abs(start).bit_length(),abs(step).bit_length())>512:
        raise WorkLimit('affine parameter bit budget exceeded')
    g=tuple(int(x) for x in P.compose_linear(P.poly(f),start,step))
    d=len(g)-1;values=[int(P.evaluate(g,i)) for i in range(d+1)]
    if max(abs(v).bit_length() for v in values)>131072:
        raise WorkLimit('sample value bit budget exceeded')
    row=values[:];newton=[]
    while row:
        newton.append(row[0]);row=[b-a for a,b in zip(row,row[1:])]
    D=0;weights=[]
    for v in values:
        D,a,b=_egcd(D,v);weights=[a*w for w in weights]+[b]
    if sum(w*v for w,v in zip(weights,values))!=D or gcd(*newton)!=D:
        raise ArithmeticError('finite-window gcd construction failed')
    return {'schema':'pp-fixed-divisor/1','coefficients':list(f),
            'start':start,'step':step,'pullback_coefficients':list(g),'degree':d,
            'domain':'all signed integers n; original coordinate x=start+step*n',
            'sample_values':values,'sample_coordinates':[start+step*i for i in range(d+1)],
            'fixed_divisor':D,'sample_bezout_weights':weights,
            'forward_differences':newton,
            'primitive_binomial_coefficients':None if D==0 else [v//D for v in newton],
            'complete':True,'kernel_checked':False,
            'meaning':'q divides the fixed divisor iff q divides every value in the stated domain'}


def generalized_choose(n,j):
    """Integral binomial coefficient for signed n and nonnegative j."""
    if type(n) is not int or type(j) is not int or j<0:raise ValueError('integer n and nonnegative integer j required')
    r=1
    for i in range(j):r=r*(n-i)//(i+1)
    return r


def admissibility(coefficients,*,exponent=2,start=0,step=1,factor_limit=100000):
    if type(exponent) is not int or not 1<=exponent<=1024:
        raise ValueError('exponent must be in [1,1024]')
    if type(factor_limit) is not int or not 1<=factor_limit<=1000000:
        raise ValueError('factor_limit must be in [1,1000000]')
    packet=fixed_divisor(coefficients,start=start,step=step);D=packet['fixed_divisor']
    fs={} if D==0 else factor_integer(D,work_limit=factor_limit)
    rows=[]
    for p,v in sorted(fs.items()):
        obstruction=v>=exponent
        witness=None if obstruction else next(i for i,y in enumerate(packet['sample_values']) if y%(p**exponent))
        rows.append({'prime':p,'valuation':v,'universal_obstruction':obstruction,
                     'witness_parameter':witness,'witness_coordinate':None if witness is None else start+step*witness,
                     'witness_value':None if witness is None else packet['sample_values'][witness]})
    obstructing=[r['prime'] for r in rows if r['universal_obstruction']]
    if D==0:obstructing=[2]
    return {**packet,'schema':'pp-fixed-divisor-admissibility/1','exponent':exponent,
            'prime_factors':[[p,v] for p,v in sorted(fs.items())],'valuation_rows':rows,
            'locally_admissible':not obstructing,'fixed_divisor_prime':next(iter(obstructing),None),
            'zero_polynomial':D==0,'density_proved':False,'globally_power_free_value_produced':False,
            'route':'finite consecutive-value gcd; no derivative Bezout hypothesis or residue enumeration'}


def native_certificate(coefficients,**kwargs):
    packet=admissibility(coefficients,**kwargs);f=packet['coefficients'];g=packet['pullback_coefficients'];D=packet['fixed_divisor'];d=packet['degree'];k=packet['exponent']
    if max(len(f),len(g))>33 or max(abs(c).bit_length() for c in g)>4096:
        raise WorkLimit('native degree 32 or coefficient 4096-bit budget exceeded')
    if D.bit_length()>4096:raise WorkLimit('native fixed-divisor bit budget exceeded')
    key=json.dumps(packet,sort_keys=True,separators=(',',':'));ns='FixedDivisor_'+hashlib.sha256(key.encode()).hexdigest()[:16]
    from .power_free_local import _poly
    names=['pullback_checked','degree_bound_checked','window_checked','all_divisors_checked','universal_checked']
    source=f'''import PerfectPower.FixedDivisor
set_option maxHeartbeats 6000000
set_option maxRecDepth 30000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace {ns}
open Polynomial PerfectPower.FixedDivisor PerfectPower.PowerFreeLocal
noncomputable def original : Polynomial ℤ := {_poly(f)}
noncomputable def source : Polynomial ℤ := {_poly(g)}
theorem pullback_checked : source = original.comp (C ({packet['start']} : ℤ) + C ({packet['step']} : ℤ)*X) := by
  norm_num [source, original, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.C_comp, Polynomial.X_comp]
  <;> ring
theorem degree_bound_checked : source.natDegree ≤ {d} := by
  unfold source
  compute_degree <;> norm_num
theorem window_checked : windowGcd source {d} = {D} := by
  norm_num [windowGcd,source,List.range_succ, List.map_append, valueGcd, Nat.gcd_eq_zero_iff]
theorem all_divisors_checked (q : ℕ) : q ∣ {D} ↔ ∀ n : ℤ, (q : ℤ) ∣ original.eval ({packet['start']}+{packet['step']}*n) := by
  rw [← window_checked, dvd_windowGcd_iff source {d} q degree_bound_checked]
  simp only [pullback_checked, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
theorem universal_checked (n : ℤ) : ({D} : ℤ) ∣ original.eval ({packet['start']}+{packet['step']}*n) :=
  (all_divisors_checked {D}).mp (dvd_refl _) n
'''
    if packet['locally_admissible']:
        status='admissible_checked';names+=['fixed_divisor_checked','power_free_checked',status]
        factors=[p for p,v in packet['prime_factors'] for _ in range(v)];ps=[p for p,v in packet['prime_factors']]
        source+=f'''theorem fixed_divisor_checked : fixedDivisor source = {D} := by
  rw [← windowGcd_eq_fixedDivisor source {d} degree_bound_checked, window_checked]
theorem power_free_checked : PowerFree {k} ({D} : ℤ) := by
  intro p hp hd
  have hd' : p^{k} ∣ {D} := by exact_mod_cast hd
  have hpd : p ∣ {D} := (dvd_pow_self p (by norm_num : {k} ≠ 0)).trans hd'
  have hf : ({factors} : List ℕ).Perm ({D} : ℕ).primeFactorsList := by
    apply Nat.primeFactorsList_unique
    · norm_num
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
'''
        if factors:source+='      rcases hp with '+' | '.join('rfl' for _ in factors)+'\n      all_goals norm_num\n'
        source+=f'''  have hm := (Nat.mem_primeFactorsList_iff_dvd (by norm_num : {D} ≠ 0) hp).mpr hpd
  rw [← hf.mem_iff] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
'''
        if factors:source+='  rcases hm with '+' | '.join('rfl' for _ in factors)+'\n  all_goals norm_num at hd\n'
        else:pass
        source+=f'''theorem {status} : LocallyAdmissible source {k} := by
  rw [admissible_iff_fixedDivisor, fixed_divisor_checked]
  exact power_free_checked
'''
    else:
        status='obstruction_checked';names+=[status];p=packet['fixed_divisor_prime']
        source+=f'''theorem {status} (n : ℤ) : ¬ PowerFree {k} (original.eval ({packet['start']}+{packet['step']}*n)) := by
  intro h
  apply h {p} (by norm_num)
  exact (by norm_num : ({p} : ℤ)^{k} ∣ {D}).trans (universal_checked n)
'''
    source+=f'end {ns}\n';source='\n'.join(line.rstrip() for line in source.splitlines())+'\n'
    packet['lean']={'namespace':ns,'source':source,'source_sha256':hashlib.sha256(source.encode()).hexdigest(),
                    'theorem':ns+'.'+status,'declarations':[ns+'.'+n for n in names],'kernel_checked':False}
    return packet


def repeated_power_free(coefficients,*,exponent=2,factor_limit=100000):
    """Complete finite k-free values when a nonconstant k-fold factor exists."""
    f=_coefficients(coefficients)
    if type(exponent) is not int or not 2<=exponent<=128:raise ValueError('exponent must be in [2,128]')
    if type(factor_limit) is not int or not 1<=factor_limit<=1000000:raise ValueError('factor_limit must be in [1,1000000]')
    if len(f)<2:raise ValueError('nonconstant polynomial required for finite repeated-factor route')
    _,parts=P.squarefree_decomposition(P.poly(f))
    choices=[(len(g),m,P.integer_primitive(g)) for m,g in parts.items() if m>=exponent]
    if not choices:raise ValueError('no nonconstant factor of multiplicity at least the exponent')
    _,m,g=min(choices);h=P.exact_div(P.poly(f),P.power(P.poly(g),exponent))
    if any(c.denominator!=1 for c in h):raise ArithmeticError('primitive factor quotient failed integrality')
    h=tuple(int(c) for c in h)
    candidates=sorted(set(P.integer_roots(P.subtract(P.poly(g),P.ONE)))|set(P.integer_roots(P.add(P.poly(g),P.ONE))))
    rows=[];solutions=[]
    for x in candidates:
        value=int(P.evaluate(f,x));fs={} if value==0 else factor_integer(abs(value),work_limit=factor_limit)
        obstruction=2 if value==0 else next((p for p,v in sorted(fs.items()) if v>=exponent),None)
        if obstruction is None:solutions.append(x)
        rows.append({'input':x,'value':value,'prime_factors':[[p,v] for p,v in sorted(fs.items())],
                     'power_free':obstruction is None,'obstruction_prime':obstruction})
    return {'schema':'pp-repeated-power-free/1','coefficients':list(f),'exponent':exponent,
            'repeated_factor':list(g),'multiplicity':m,'cofactor':list(h),
            'candidates':candidates,'candidate_values':rows,'solutions':solutions,
            'complete':True,'kernel_checked':False,'global_finiteness':True,'global_density':0,
            'meaning':'exact k-free values for all signed integer inputs; f=g^k*h forces g(x)=±1'}


def _constant_power_free_proof(value,k,factors,name):
    """A universal-prime proof from an explicit checked prime factor list."""
    D=abs(value);fs=[p for p,v in factors for _ in range(v)]
    s=f'''theorem {name} : PowerFree {k} ({value} : ℤ) := by
  intro p hp hd
  have hd' : p^{k} ∣ {D} := by
    have hc : ((p^{k} : ℕ) : ℤ) ∣ ({value} : ℤ) := by simpa only [Nat.cast_pow] using hd
    have hh := Int.natCast_dvd.mp hc
    simpa using hh
  have hpd : p ∣ {D} := (dvd_pow_self p (by norm_num : {k} ≠ 0)).trans hd'
  have hf : ({fs} : List ℕ).Perm ({D} : ℕ).primeFactorsList := by
    apply Nat.primeFactorsList_unique
    · norm_num
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
'''
    if fs:s+='      rcases hp with '+' | '.join('rfl' for _ in fs)+'\n      all_goals norm_num\n'
    s+=f'''  have hm := (Nat.mem_primeFactorsList_iff_dvd (by norm_num : {D} ≠ 0) hp).mpr hpd
  rw [← hf.mem_iff] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
'''
    if fs:s+='  rcases hm with '+' | '.join('rfl' for _ in fs)+'\n  all_goals norm_num at hd\n'
    else:pass
    return s


def native_repeated_power_free(coefficients,*,exponent=2,factor_limit=100000,divisor_limit=4096):
    packet=repeated_power_free(coefficients,exponent=exponent,factor_limit=factor_limit)
    from math import isqrt
    f,g,h=packet['coefficients'],packet['repeated_factor'],packet['cofactor'];k=exponent
    if max(len(f),len(g),len(h))>33 or max(abs(c).bit_length() for c in [*f,*g,*h])>4096:
        raise WorkLimit('native degree 32 or coefficient 4096-bit budget exceeded')
    if type(divisor_limit) is not int or not 1<=divisor_limit<=65536:raise ValueError('divisor_limit must be in [1,65536]')
    for delta in [1,-1]:
        coeff=list(g);coeff[0]-=delta;first=next(c for c in coeff if c)
        if isqrt(abs(first))>divisor_limit:raise WorkLimit('native unit-fibre divisor budget exceeded')
    from .power_free_local import _poly
    ns='RepeatedPowerFree_'+hashlib.sha256(json.dumps(packet,sort_keys=True).encode()).hexdigest()[:16]
    fin=lambda xs:'({' + ','.join(map(str,xs)) + '} : Finset ℤ)' if xs else '(∅ : Finset ℤ)'
    cands=fin(packet['candidates']);sols=fin(packet['solutions']);names=['factorization_checked','factor_source_checked','candidates_checked','finite_reduction_checked']
    s=f'''import PerfectPower.FixedDivisor
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace {ns}
open Polynomial PerfectPower PerfectPower.FixedDivisor PerfectPower.PowerFreeLocal
noncomputable def source : Polynomial ℤ := {_poly(f)}
noncomputable def repeated : Polynomial ℤ := {_poly(g)}
noncomputable def cofactor : Polynomial ℤ := {_poly(h)}
def coefficients : List ℤ := {g}
theorem factorization_checked : source = repeated^{k}*cofactor := by
  norm_num [source,repeated,cofactor]
  <;> ring
theorem factor_source_checked : repeated = NativePolynomialSquare.polynomial coefficients := by
  norm_num [repeated,coefficients,NativePolynomialSquare.polynomial]
  <;> ring
theorem candidates_checked : NativePolynomialRoots.fibre coefficients 1 ∪ NativePolynomialRoots.fibre coefficients (-1) = {cands} := by
  decide
theorem finite_reduction_checked (x : ℤ) (hx : PowerFree {k} (source.eval x)) : x ∈ {cands} := by
  rw [← candidates_checked]
  exact repeated_candidate_complete source repeated cofactor coefficients {k} factorization_checked factor_source_checked (by decide) (by decide) x hx
'''
    for i,row in enumerate(packet['candidate_values']):
        name=f'candidate_{i}_checked';names.append(name);v=row['value'];x=row['input']
        if row['power_free']:
            pn=f'constant_{i}_checked';names.append(pn);s+=_constant_power_free_proof(v,k,row['prime_factors'],pn)
            s+=f'''theorem {name} : PowerFree {k} (source.eval ({x} : ℤ)) := by
  have he : source.eval ({x} : ℤ) = {v} := by norm_num [source]
  rw [he]
  exact {pn}
'''
        else:
            p=row['obstruction_prime']
            s+=f'''theorem {name} : ¬ PowerFree {k} (source.eval ({x} : ℤ)) := by
  intro hx
  apply hx {p} (by norm_num)
  norm_num [source]
'''
    s+=f'''theorem all_solutions_checked (x : ℤ) : PowerFree {k} (source.eval x) ↔ x ∈ {sols} := by
  constructor
  · intro hx
    have hc := finite_reduction_checked x hx
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.not_mem_empty] at hc
'''
    if not packet['candidates']:pass
    else:
        s+='    rcases hc with '+' | '.join('rfl' for _ in packet['candidates'])+'\n'
        for i,row in enumerate(packet['candidate_values']):
            s+='    · '+('decide\n' if row['power_free'] else f'exact False.elim (candidate_{i}_checked hx)\n')
    s+='  · intro hx\n    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.not_mem_empty] at hx\n'
    if not packet['solutions']:pass
    else:
        s+='    rcases hx with '+' | '.join('rfl' for _ in packet['solutions'])+'\n'
        for i,row in enumerate(packet['candidate_values']):
            if row['power_free']:s+=f'    · exact candidate_{i}_checked\n'
    s+=f'end {ns}\n';names+=['all_solutions_checked']
    packet['lean']={'namespace':ns,'source':s,'source_sha256':hashlib.sha256(s.encode()).hexdigest(),
                    'theorem':ns+'.all_solutions_checked','declarations':[ns+'.'+n for n in names],'kernel_checked':False}
    return packet
