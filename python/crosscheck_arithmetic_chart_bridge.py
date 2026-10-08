"""Independent direct rational/source census and symbolic weighted determinants."""
import json,random
from fractions import Fraction
from math import prod,comb,lcm
from pathlib import Path
from itertools import combinations
import sympy as S
from perfectpower.rational_power_atlas import power_atlas,verify_power_atlas,power_population,power_scan,power_rank,power_select
from perfectpower.weighted_gram_determinant import weighted_determinant,parse

def main():
    rng=random.Random(20261008);cases=120;candidate_checks=0;modular_checks=0;empty=0
    for i in range(cases):
        L=1+i%6;coefficients=[str(Fraction(rng.randint(-3,3),L)) for _ in range(4)]
        d=2+i%2;factors=[[2,1+i%2],[3,1]];restrictions=[]
        if i%3==0:restrictions=[{'terms':[[1,1,0],[1,0,1]],'prime':2,'exponent':2}]
        a=power_atlas(coefficients,d,factors,restrictions=restrictions,explicit_limit=1 if i%2 else 4096);assert verify_power_atlas(a)
        F=a['numerator'];L=a['denominator'];M=a['parameter_period'];B=a['equation_period'];b=[[-9,10],[-6,7]]
        def numerator(x):return sum(c*x**j for j,c in enumerate(F))
        def allowed(x,y):return not restrictions or (x+y)%4==0
        candidates=[[x,y] for x in range(-9,11) for y in range(-6,8) if (numerator(x)-L*y**d)%(L*B)==0 and allowed(x,y)]
        points=[[x,y] for x in range(-9,11) for y in range(-6,8) if Fraction(numerator(x),L)==y**d and allowed(x,y)]
        count=power_population(a,b)['count'];assert count==len(candidates)
        assert power_scan(a,b)['points']==points;candidate_checks+=20*14
        # Independent original-coordinate anisotropic period census.
        full=[[x,y] for x in range(L*M) for y in range(M) if (numerator(x)-L*y**d)%(L*B)==0 and allowed(x,y)]
        classes=sum(c['cover']['combination_count'] for c in a['charts']);assert len(full)==classes
        modular_checks+=L*M*M;empty+=not full
        if count:
            j=rng.randrange(count);z=power_select(a,b,j);assert z in candidates and power_rank(a,b,z)==j
    weighted_cases=120;subsets=0
    def scalar(v):
        a,b=parse(v);return S.Rational(a.numerator,a.denominator)+S.I*S.Rational(b.numerator,b.denominator)
    for i in range(weighted_cases):
        rows=1+i%7;n=1+i%4
        B=[[[rng.randint(-3,3),rng.randint(-2,2)] for _ in range(n)] for _ in range(rows)]
        w=[[rng.randint(-2,3),0 if i%2 else rng.randint(-2,2)] for _ in range(rows)]
        packet=weighted_determinant(B,w);matrix=S.Matrix([[scalar(v) for v in row] for row in B]);weights=[scalar(v) for v in w]
        gram=matrix.conjugate().T*S.diag(*weights)*matrix;det=S.expand(gram.det(method='domain-ge'))
        assert det==scalar(packet['determinant'])
        total=0
        for indices in combinations(range(rows),n):
            minor=matrix[list(indices),:].det(method='domain-ge');total+=prod(weights[j] for j in indices)*S.conjugate(minor)*minor;subsets+=1
        assert S.expand(total)==det
    result={'seed':20261008,'power_cases':cases,'direct_original_box_checks':candidate_checks,
      'anisotropic_period_checks':modular_checks,'empty_modular_power_domains':empty,
      'weighted_cases':weighted_cases,'unordered_subsets_checked':subsets,'rank_select_agree':True,
      'source_lists_agree':True,'denominator_scaled_periods_agree':True,'sympy_weighted_determinants_agree':True,
      'engine':'direct rational arithmetic in original coordinates; independent SymPy Gaussian determinant and subset enumeration'}
    out=Path(__file__).resolve().parents[1]/'receipts'/'arithmetic_chart_bridge'/'crosscheck.json';out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))

if __name__=='__main__':main()
