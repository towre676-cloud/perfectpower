"""Exact rational polynomial domains and denominator-aware universal divisors.

Charts cover signed integer inputs; Gamma wrappers retain their natural domain.
Local admissibility is not a global existence or density assertion.
"""
from fractions import Fraction
from math import gcd, lcm
import hashlib
import json
from . import polyalg as P
from .fixed_divisor import fixed_divisor, _constant_power_free_proof
from .coefficient_charts import factor_integer
from .divisor_square import WorkLimit


def normalize(coefficients):
    if not isinstance(coefficients, (list, tuple)) or not coefficients:
        raise ValueError('nonempty ascending rational coefficients required')
    if len(coefficients)>129: raise WorkLimit('degree 128 budget exceeded')
    values=[]
    for c in coefficients:
        if type(c) not in (int,str): raise ValueError('integer or exact rational string required')
        if isinstance(c,str) and (len(c)>1300 or any(ch not in '+-0123456789/ ' for ch in c)):
            raise ValueError('bounded exact rational string required')
        try: v=Fraction(c)
        except (ValueError,ZeroDivisionError): raise ValueError('invalid rational coefficient') from None
        if max(abs(v.numerator).bit_length(),v.denominator.bit_length())>2048:
            raise WorkLimit('coefficient 2048-bit budget exceeded')
        values.append(v)
    values=P.poly(values);L=lcm(*(v.denominator for v in values))
    if L.bit_length()>4096: raise WorkLimit('common denominator 4096-bit budget exceeded')
    F=[int(v*L) for v in values]
    if max(abs(c).bit_length() for c in F)>2048: raise WorkLimit('numerator coefficient budget exceeded')
    return F,L,[str(v) for v in values]


def analyze(coefficients, *, exponent=2, interval=None, period_limit=65536, factor_limit=100000):
    if type(exponent) is not int or not 1<=exponent<=1024: raise ValueError('exponent in [1,1024] required')
    if type(period_limit) is not int or not 1<=period_limit<=65536: raise ValueError('period_limit in [1,65536] required')
    if type(factor_limit) is not int or not 1<=factor_limit<=1000000: raise ValueError('factor_limit in [1,1000000] required')
    if interval is not None and (not isinstance(interval,(list,tuple)) or len(interval)!=2 or
            any(type(x) is not int for x in interval) or interval[0]>interval[1]):
        raise ValueError('ordered closed integer interval required')
    F,L,canonical=normalize(coefficients);base=fixed_divisor(F);D=base['fixed_divisor'];whole=D%L==0
    charts=[];residues=None
    if whole:
        quotient_gcd=D//L
    else:
        if L>period_limit: raise WorkLimit('integral-domain residue period budget exceeded')
        residues=[r for r in range(L) if P.evaluate(F,r)%L==0]
        for r in residues:
            values=P.compose_linear(P.poly(F),r,L)
            if any(v.denominator!=1 or int(v)%L for v in values):
                raise ArithmeticError('integral residue chart failed coefficient divisibility')
            G=[int(v)//L for v in values];chart=fixed_divisor(G)
            charts.append({'residue':r,'step':L,'coefficients':G,'fixed_divisor':chart['fixed_divisor'],
                           'finite_window':chart})
        quotient_gcd=gcd(*(c['fixed_divisor'] for c in charts)) if charts else 0
    fs={} if quotient_gcd==0 else factor_integer(quotient_gcd,work_limit=factor_limit)
    obstruction=2 if quotient_gcd==0 else next((p for p,v in sorted(fs.items()) if v>=exponent),None)
    count=None
    if interval is not None:
        lo,hi=interval
        count=hi-lo+1 if whole else sum((hi-r)//L-(lo-1-r)//L for r in residues)
    return {'schema':'pp-integer-valued-polynomial/1','rational_coefficients':canonical,
            'numerator':F,'denominator':L,'numerator_fixed_divisor':D,
            'rational_value_lattice':str(Fraction(D,L)), 'numerator_window':base,
            'integral_everywhere':whole,'integral_domain_empty':not whole and not residues,
            'integral_residues':residues,'charts':charts,'integer_domain_fixed_divisor':quotient_gcd,
            'exponent':exponent,'prime_factors':[[p,v] for p,v in sorted(fs.items())],
            'locally_admissible_on_integer_domain':obstruction is None,'obstruction_prime':obstruction,
            'interval':None if interval is None else list(interval),'integral_input_count':count,
            'domain':'all signed integer x with F(x) divisible by L',
            'complete':True,'kernel_checked':False,'density_proved':False,
            'meaning':'q divides the integer-domain fixed divisor iff q divides every integral quotient value'}


def gamma_packet(spec, **kwargs):
    from .gamma_arithmetic import normalize as gamma_normalize
    normal=gamma_normalize(spec)
    packet=analyze([str(Fraction(c,normal['denominator'])) for c in normal['numerator']],**kwargs)
    if packet['interval'] is not None and packet['interval'][0]<0:
        raise ValueError('Gamma wrapper requires a nonnegative interval')
    packet.update(gamma_normalization=normal,domain='natural indices n >= 0 with integral finite-product value',
                  fixed_divisor_scope='natural and signed polynomial extensions have the same universal divisors')
    return packet


def native_certificate(coefficients, **kwargs):
    packet=analyze(coefficients,**kwargs);F=packet['numerator'];L=packet['denominator'];D=packet['numerator_fixed_divisor']
    G=packet['integer_domain_fixed_divisor'];k=packet['exponent'];charts=packet['charts'];d=len(F)-1
    if d>32 or any(abs(c).bit_length()>4096 for chart in charts for c in chart['coefficients']):
        raise WorkLimit('native degree 32 or chart coefficient budget exceeded')
    if not packet['integral_everywhere'] and (L>4096 or len(charts)>32):
        raise WorkLimit('native residue period 4096 or chart count 32 budget exceeded')
    from .power_free_local import _poly, _finset
    qterms=[]
    for i,v in enumerate(map(Fraction,packet['rational_coefficients'])):
        if v:
            term=f'C (({v.numerator} : ℚ)/{v.denominator})'
            qterms.append(term if i==0 else term+' * X' if i==1 else term+f' * X^{i}')
    qpoly=' + '.join(qterms) or '0'
    ns='IntegerValued_'+hashlib.sha256(json.dumps(packet,sort_keys=True).encode()).hexdigest()[:16]
    names=[]
    source=f'''import PerfectPower.IntegerValuedPolynomial
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
namespace {ns}
open PerfectPower Polynomial PerfectPower.FixedDivisor PerfectPower.PowerFreeLocal PerfectPower.IntegerValuedPolynomial
noncomputable def source : Polynomial ℤ := NativePolynomialSquare.polynomial {F}
theorem source_checked : source = {_poly(F)} := by
  norm_num [source, NativePolynomialSquare.polynomial]
  <;> ring
theorem degree_checked : source.natDegree ≤ {d} := by
  rw [source_checked]
  compute_degree <;> norm_num
theorem numerator_gcd_checked : fixedDivisor source = {D} := by
  rw [← windowGcd_eq_fixedDivisor source {d} degree_checked]
  norm_num [windowGcd,source,NativePolynomialSquare.polynomial,List.range_succ,List.map_append,valueGcd,Nat.gcd_eq_zero_iff]
'''
    names+=['source_checked','degree_checked','numerator_gcd_checked']
    source+=f'''noncomputable def rationalSource : Polynomial ℚ := {qpoly}
theorem rational_source_checked : rationalSource * C ({L} : ℚ) = source.map (Int.castRingHom ℚ) := by
  rw [source_checked]
  simp only [rationalSource,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_C,Polynomial.map_X,add_mul,mul_assoc,mul_left_comm,← Polynomial.C_mul]
  ring_nf
  norm_num [← Polynomial.C_mul,← Polynomial.C_pow]
  <;> ring
theorem rational_value_checked (x : ℤ) (hx : IntegralAt source {L} x) :
    rationalSource.eval (x : ℚ) = (quotientValue source {L} x : ℚ) := by
  have he := congrArg (Polynomial.eval (x : ℚ)) rational_source_checked
  have h : rationalSource.eval (x : ℚ) * ({L} : ℚ) = ((source.eval x : ℤ) : ℚ) := by
    simpa using he
  rw [← quotient_rational_value source {L} (by norm_num) x hx]
  exact (eq_div_iff (by norm_num : ({L} : ℚ) ≠ 0)).mpr h
'''
    names+=['rational_source_checked','rational_value_checked']
    if packet['integral_everywhere']:
        source+=f'''theorem integral_checked (x : ℤ) : IntegralAt source {L} x := by
  apply (integral_everywhere_iff source {L}).mpr
  rw [numerator_gcd_checked] <;> norm_num
theorem domain_gcd_checked (q : ℕ) : q ∣ {G} ↔ ∀ x : ℤ, (q : ℤ) ∣ quotientValue source {L} x := by
  have hL : {L} ∣ fixedDivisor source := by rw [numerator_gcd_checked] <;> norm_num
  have h := quotient_divisors_iff source {L} q hL
  rw [numerator_gcd_checked] at h
  convert h using 1 <;> norm_num
'''
        source+=f'''theorem natural_gcd_checked (q : ℕ) : q ∣ {G} ↔ ∀ n : ℕ, (q : ℤ) ∣ quotientValue source {L} n := by
  have hL : {L} ∣ fixedDivisor source := by rw [numerator_gcd_checked] <;> norm_num
  have h := quotient_natural_divisors_iff source {L} q hL
  rw [numerator_gcd_checked] at h
  convert h using 1 <;> norm_num
'''
        names+=['integral_checked','domain_gcd_checked','natural_gcd_checked']
    else:
        roots=packet['integral_residues'];literal=_finset(roots)
        source+=f'''theorem residues_checked : rootResidues {F} {L} = {literal} := by decide +kernel
theorem domain_checked (x : ℤ) : IntegralAt source {L} x ↔
    ∃ r ∈ {literal}, ∃ n : ℤ, x = (r : ℤ)+{L}*n := by
  simpa only [source, residues_checked] using integer_domain_cover {F} {L} (by norm_num) x
'''
        names+=['residues_checked','domain_checked']
        for i,c in enumerate(charts):
            r=c['residue'];cs=c['coefficients'];cd=len(cs)-1
            source+=f'''noncomputable def chart{i} : Polynomial ℤ := {_poly(cs)}
theorem chart{i}_checked : source.comp (C ({r} : ℤ)+C ({L} : ℤ)*X) = C ({L} : ℤ)*chart{i} := by
  rw [source_checked]
  norm_num [chart{i},Polynomial.add_comp,Polynomial.mul_comp,Polynomial.pow_comp,Polynomial.C_comp,Polynomial.X_comp]
  <;> ring
theorem chart{i}_quotient (n : ℤ) : quotientValue source {L} ({r}+{L}*n) = chart{i}.eval n :=
  chart_quotient source chart{i} {L} {r} (by norm_num) chart{i}_checked n
theorem chart{i}_gcd : fixedDivisor chart{i} = {c['fixed_divisor']} := by
  have hd : chart{i}.natDegree ≤ {cd} := by unfold chart{i}; compute_degree <;> norm_num
  rw [← windowGcd_eq_fixedDivisor chart{i} {cd} hd]
  norm_num [windowGcd,chart{i},List.range_succ,List.map_append,valueGcd,Nat.gcd_eq_zero_iff]
'''
            names +=[f'chart{i}_checked',f'chart{i}_quotient',f'chart{i}_gcd']
        branches='0'
        for i,c in reversed(list(enumerate(charts))): branches=f'if r = {c["residue"]} then chart{i} else ({branches})'
        source+=f'noncomputable def charts (r : ℕ) : Polynomial ℤ := {branches}\n'
        source+=f'''theorem charts_checked (r : ℕ) (hr : r ∈ rootResidues {F} {L}) :
    source.comp (C (r : ℤ)+C ({L} : ℤ)*X) = C ({L} : ℤ)*charts r := by
  rw [residues_checked] at hr
  simp only [Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false] at hr
'''
        if roots:
            source+='  rcases hr with '+' | '.join('rfl' for _ in roots)+'\n'
            for i in range(len(roots)):source+=f'  · simpa [charts] using chart{i}_checked\n'
        chartlist='['+','.join('chart'+str(i) for i in range(len(charts)))+']'
        source+=f'''theorem family_members_checked (f : Polynomial ℤ) :
    f ∈ ((rootResidues {F} {L}).toList.map charts) ↔ f ∈ {chartlist} := by
  simp [List.mem_map,Finset.mem_toList,residues_checked,charts,or_and_left,exists_or,eq_comm]
theorem family_gcd_checked : familyGcd ((rootResidues {F} {L}).toList.map charts) = {G} := by
  rw [familyGcd_congr _ {chartlist} family_members_checked]
  norm_num [familyGcd{''.join(',chart'+str(i)+'_gcd' for i in range(len(charts)))}]
theorem domain_gcd_checked (q : ℕ) : q ∣ {G} ↔ ∀ x : ℤ, IntegralAt source {L} x →
    (q : ℤ) ∣ quotientValue source {L} x := by
  have h := domain_divisors_iff {F} {L} q (by norm_num) charts charts_checked
  rw [family_gcd_checked] at h
  exact h
'''
        names+=['charts_checked','family_members_checked','family_gcd_checked','domain_gcd_checked']
    if packet['locally_admissible_on_integer_domain']:
        source+=_constant_power_free_proof(G,k,packet['prime_factors'],'power_free_gcd_checked')
        # A common proof works on the full domain and on a union of charts.
        source+=f'''theorem admissible_checked : QuotientAdmissible source {L} {k} := by
  intro p hp
  by_contra hn
  have hu : ∀ x : ℤ, IntegralAt source {L} x → (p : ℤ)^{k} ∣ quotientValue source {L} x := by
    intro x hx
    by_contra he
    exact hn ⟨x,hx,he⟩
'''
        arg='(by simpa only [Nat.cast_pow] using hu)' if not packet['integral_everywhere'] else '(by intro x; simpa only [Nat.cast_pow] using hu x (integral_checked x))'
        source+=f'''  have hd := (domain_gcd_checked (p^{k})).mpr {arg}
  apply power_free_gcd_checked p hp
  exact_mod_cast hd
'''
        names+=['power_free_gcd_checked','admissible_checked']
    else:
        p=packet['obstruction_prime']
        source+=f'''theorem obstruction_checked (x : ℤ) (hx : IntegralAt source {L} x) :
    ¬ PowerFree {k} (quotientValue source {L} x) := by
  intro h
  apply h {p} (by norm_num)
  have hd := (domain_gcd_checked ({p}^{k})).mp (by norm_num : {p}^{k} ∣ {G})
  simpa only [Nat.cast_pow] using hd x{' hx' if not packet['integral_everywhere'] else ''}
'''
        names+=['obstruction_checked']
    source+=f'end {ns}\n'
    packet['lean']={'namespace':ns,'source':source,'source_sha256':hashlib.sha256(source.encode()).hexdigest(),
                    'declarations':[ns+'.'+n for n in names],'kernel_checked':False}
    return packet
