"""Literal finite projectors and original Fourier/chirp source identities in Lean.

Python generates witnesses only. Lean checks every rational and polynomial entry.
"""
from fractions import Fraction as Q
from .weil_spectral import _spectral
from .branched_geometry import cyclotomic
from . import polyalg as P


def rat(x):
    x=Q(x)
    return str(x.numerator) if x.denominator==1 else f'({x.numerator} / {x.denominator})'


def poly(cs):
    return ' + '.join(f'C ({rat(c)}) * X^{i}' for i,c in enumerate(cs) if c) or '0'


def matrix(A,entry=rat):return '!!['+';\n  '.join(', '.join(entry(x) for x in row) for row in A)+']'


def native_spectral(level):
    if type(level) is not int or level not in (3,4,8,9):raise ValueError('native worked levels are 3,4,8,9')
    n=level;_,_,_,projects,rows,_=_spectral(n);d=len(projects);phi=cyclotomic(n)
    ns=f'PerfectPower.WeilSpectralExample{n}'
    lines=['import PerfectPower.WeilSpectral','set_option maxRecDepth 4096','set_option maxHeartbeats 0',
           f'namespace {ns}','noncomputable section','open Matrix Polynomial','open scoped BigOperators',
           f'abbrev M := Matrix (Fin {n}) (Fin {n}) ℚ',f'def phi : Polynomial ℚ := {poly(phi)}',
           f'def fourier : Matrix (Fin {n}) (Fin {n}) (Polynomial ℚ) := '+matrix([[[(Q(1) if k==x*y%n else Q(0)) for k in range(n)] for y in range(n)] for x in range(n)],poly),
           f'def chirp : Matrix (Fin {n}) (Fin {n}) (Polynomial ℚ) := '+matrix([[[(Q(1) if x==y and k==x*x%n else Q(0)) for k in range(n)] for y in range(n)] for x in range(n)],poly)]
    names=[]
    for j,E in enumerate(projects):
        lines.append(f'def P{j} : M := '+matrix(E))
        quotient=[]
        for x in range(n):
            row=[]
            for y in range(n):
                cs=[Q(0)]*n
                for k in range(n):cs[k*y%n]+=E[x][k];cs[x*k%n]-=E[k][y]
                row.append(P.exact_div(cs,phi))
            quotient.append(row)
        lines += [f'def Q{j} : Matrix (Fin {n}) (Fin {n}) (Polynomial ℚ) := '+matrix(quotient,poly),
          f'theorem fourier_factor_{j} : (P{j}.map C)*fourier-fourier*(P{j}.map C)=phi • Q{j} := by',
          '  ext x y : 2; simp only [Matrix.sub_apply,Matrix.smul_apply,Matrix.mul_apply,Matrix.map_apply]; fin_cases x <;> fin_cases y <;>',
          f'    norm_num [P{j},fourier,phi,Q{j},Matrix.mul_apply,Fin.sum_univ_succ,Matrix.map_apply,Matrix.sub_apply,Matrix.smul_apply] <;> ring <;> simp [Polynomial.coeff_C,Polynomial.coeff_one] <;> split_ifs <;> norm_num',
          f'theorem chirp_commutes_{j} : Commute (P{j}.map C) chirp := by',
          '  change (P'+str(j)+'.map C)*chirp=chirp*(P'+str(j)+'.map C)',
          '  ext x y : 2; simp only [Matrix.sub_apply,Matrix.smul_apply,Matrix.mul_apply,Matrix.map_apply]; fin_cases x <;> fin_cases y <;>',
          f'    norm_num [P{j},chirp,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.map_apply] <;> ring <;> simp [Polynomial.coeff_C,Polynomial.coeff_one] <;> split_ifs <;> norm_num',
          f'theorem source_fourier_commutes_{j} {{K : Type*}} [Field K] (f : Polynomial ℚ →+* K) (hf : f phi=0) :',
          f'    Commute ((P{j}.map C).map f) (fourier.map f) :=',
          f'  PerfectPower.WeilSpectral.polynomial_commute_of_factor phi fourier_factor_{j} f hf',
          f'theorem source_chirp_commutes_{j} {{K : Type*}} [Field K] (f : Polynomial ℚ →+* K) :',
          f'    Commute ((P{j}.map C).map f) (chirp.map f) := by',
          f'  have h := congrArg (fun A => A.map f) chirp_commutes_{j}.eq',
          '  simpa only [Matrix.map_mul] using h']
        names.extend(f'{ns}.{t}_{j}' for t in ['fourier_factor','chirp_commutes','source_fourier_commutes','source_chirp_commutes'])
    lines += [f'def projectors : Fin {d} → M := !['+', '.join('P'+str(j) for j in range(d))+']',
              f'def ranks : Fin {d} → ℚ := !['+', '.join(str(r['rank']) for r in rows)+']']
    simpdefs='projectors, ranks, '+', '.join('P'+str(j) for j in range(d))+', Matrix.mul_apply, Fin.sum_univ_succ, Matrix.trace'
    checks={
       'orthogonal_entries': f'∀ i j : Fin {d}, ∀ x y : Fin {n}, (projectors i * projectors j) x y = if i=j then projectors i x y else 0',
       'symmetric_entries': f'∀ i : Fin {d}, ∀ x y : Fin {n}, projectors i x y = projectors i y x',
       'partition_entries': f'∀ x y : Fin {n}, (∑ i,projectors i) x y = if x=y then 1 else 0',
       'trace_ranks': f'∀ i : Fin {d}, Matrix.trace (projectors i)=ranks i'}
    for name,statement in checks.items():
        lines += [f'theorem {name} : {statement} := by',f'  decide +kernel']
        names.append(ns+'.'+name)
    lines += [f'theorem orthogonal_partition (i j : Fin {d}) : projectors i * projectors j = if i=j then projectors i else 0 := by',
              '  ext x y; by_cases h : i=j <;> simpa [h] using orthogonal_entries i j x y',
              'theorem partition : (∑ i,projectors i) = 1 := by',
              '  ext x y; simpa only [Matrix.one_apply] using partition_entries x y',
              'end',f'end {ns}']
    names.extend([ns+'.orthogonal_partition',ns+'.partition'])
    return {'level':n,'lean_source':'\n'.join(lines)+'\n','declarations':names,'kernel_checked':False}
