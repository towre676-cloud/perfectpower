"""Weighted Cauchy-Binet over unordered local-vector subsets, in exact integers."""
from itertools import combinations
from math import factorial
import hashlib
import json
from .residue_determinant import integer,determinant,multiply,_lean_matrix,_lean_vector
from .residue_atlas import _canonical_equal


def _matrix(a,rows,columns):
    if not isinstance(a,list) or not 1<=len(a)<=rows or not isinstance(a[0],list) or not 1<=len(a[0])<=columns:
        raise ValueError('bounded nonempty matrix required')
    if any(not isinstance(r,list) or len(r)!=len(a[0]) for r in a):raise ValueError('rectangular matrix required')
    return [[integer(x,256) for x in r] for r in a]


def weighted_determinant(coefficients,vectors,weights,modulus):
    C=_matrix(coefficients,6,8);V=_matrix(vectors,8,6);n=len(C);h=len(C[0]);q=integer(modulus,32)
    if len(V)!=h or len(V[0])!=n:raise ValueError('C is n by h and V is h by n')
    if abs(q)<2:raise ValueError('absolute modulus at least two required')
    if not isinstance(weights,list) or len(weights)!=h or any(type(w) is not int or not 0<=w<=32 for w in weights):
        raise ValueError('one weight in [0,32] for each local vector required')
    scaled=[[integer(q**w*x) for x in row] for row,w in zip(V,weights)]
    A=multiply(C,scaled);records=[]
    for subset in combinations(range(h),n):
        dc=integer(determinant([[row[j] for j in subset] for row in C]))
        dv=integer(determinant([V[j] for j in subset]))
        weight=sum(weights[j] for j in subset)
        coefficient=integer(dc*dv);value=integer(q**weight*coefficient)
        records.append({'subset':list(subset),'weight':weight,'coefficient_minor':dc,
                        'vector_minor':dv,'alternating_coefficient':coefficient,'term':value})
    det=integer(determinant(A));total=integer(sum(r['term'] for r in records))
    if total!=det:raise ArithmeticError('unordered weighted determinant identity failed')
    active=[r['weight'] for r in records if r['alternating_coefficient']]
    minimum=min(active,default=0);divisor=integer(abs(q)**minimum)
    bound=integer(factorial(n)*__import__('math').prod(max(abs(x) for x in row) for row in A))
    return {'schema':'pp-unordered-weighted-determinant/1','coefficients':C,'vectors':V,
            'weights':weights[:],'modulus':q,'matrix':A,'subsets':records,
            'determinant':det,'unordered_sum':total,'subset_count':len(records),
            'minimum_active_weight':minimum,'guaranteed_divisor':divisor,
            'determinant_quotient':det//divisor,'row_product_bound':bound,
            'structural_zero':not active,'zero_from_divisor_bound':divisor>bound,
            'execution_verified':False}


def verify_weighted_determinant(packet):
    try:
        return _canonical_equal(packet,weighted_determinant(packet['coefficients'],packet['vectors'],
                                                           packet['weights'],packet['modulus']))
    except (ValueError,TypeError,KeyError,IndexError,OverflowError):return False


def native_weighted_determinant(packet):
    if not verify_weighted_determinant(packet):raise ValueError('exact weighted determinant packet required')
    n=len(packet['coefficients']);h=len(packet['vectors']);q=packet['modulus']
    if n>4 or h>6:raise ValueError('native dimension four and vector count six budgets exceeded')
    ns='Weighted_'+hashlib.sha256(json.dumps(packet,sort_keys=True).encode()).hexdigest()[:16]
    lines=['import PerfectPower.UnorderedWeightedDeterminant','set_option maxHeartbeats 0',
           'set_option maxRecDepth 100000',f'namespace {ns}','open Matrix','open scoped BigOperators',
           f'def C : Matrix (Fin {n}) (Fin {h}) ℤ := {_lean_matrix(packet["coefficients"])}',
           f'def V : Matrix (Fin {h}) (Fin {n}) ℤ := {_lean_matrix(packet["vectors"])}',
           f'def w : Fin {h} → ℕ := {_lean_vector(packet["weights"])}',
           f'def A : Matrix (Fin {n}) (Fin {n}) ℤ := {_lean_matrix(packet["matrix"])}',
           f'theorem assembly_checked : A = Matrix.of (fun i j => ∑ a, C i a * (({q} : ℤ)^w a * V a j)) := by decide +kernel',
           f'theorem determinant_checked : A.det = ({packet["determinant"]} : ℤ) := by decide +kernel']
    terms=[]
    for i,r in enumerate(packet['subsets']):
        indices='!['+','.join(str(j) for j in r['subset'])+']'
        lines += [f'def indices{i} : Fin {n} → Fin {h} := {indices}',
                  f'theorem minor{i}_checked : (C.submatrix id indices{i}).det * (V.submatrix indices{i} id).det =',
                  f'    ({r["alternating_coefficient"]} : ℤ) := by decide +kernel',f'#print axioms minor{i}_checked']
        terms.append(f'({q} : ℤ)^{r["weight"]}*((C.submatrix id indices{i}).det*(V.submatrix indices{i} id).det)')
    expr=' + '.join(terms) or '(0 : ℤ)'
    lines += [f'theorem unordered_checked : A.det = {expr} := by decide +kernel',
              f'theorem divisor_checked : ({packet["guaranteed_divisor"]} : ℤ) ∣ A.det := by decide +kernel',
              '#print axioms assembly_checked','#print axioms determinant_checked',
              '#print axioms unordered_checked','#print axioms divisor_checked']
    if packet['structural_zero'] or packet['zero_from_divisor_bound']:
        lines += ['theorem zero_checked : A.det=0 := by decide +kernel','#print axioms zero_checked']
    lines.append('end '+ns)
    return '\n'.join(lines)+'\n'


def chart_determinant(branch_packet,leaf_id,points,exponents):
    """Derive weighted local expansion from an actual source-chart point set."""
    from math import comb
    from .branching_residue_patch import verify_branching_patch
    from .residue_determinant import auxiliary_packet
    from .bounded_residue_patch import evaluate
    if not verify_branching_patch(branch_packet):raise ValueError('complete branching packet required')
    i=integer(leaf_id,32)
    if i not in branch_packet['leaf_ids']:raise ValueError('retained leaf id required')
    if not isinstance(points,list) or not 1<=len(points)<=6:
        raise ValueError('one through six distinct source points required')
    if any(not isinstance(z,list) or len(z)!=2 for z in points):raise ValueError('bivariate integer points required')
    points=[[integer(z,256) for z in row] for row in points]
    if len({tuple(z) for z in points})!=len(points):raise ValueError('distinct source points required')
    n=len(points)
    if not isinstance(exponents,list) or len(exponents)!=n or any(not isinstance(e,list) or len(e)!=2 or
        any(type(v) is not int or v<0 for v in e) or sum(e)>12 for e in exponents):
        raise ValueError('one bivariate monomial of total degree at most twelve per point required')
    node=branch_packet['nodes'][i];a,b=node['source_residue'];m=node['step']
    if any((x%m,y%m)!=(a,b) or not all(lo<=z<=hi for z,(lo,hi) in zip((x,y),branch_packet['bounds']))
           or evaluate(branch_packet['terms'],x,y)!=0 for x,y in points):
        raise ValueError('every point must be a source zero in the selected bounded chart')
    local_points=[[(x-a)//m,(y-b)//m] for x,y in points]
    expansions=[];support=set()
    for i,j in exponents:
        cs={(u,v):comb(i,u)*comb(j,v)*a**(i-u)*b**(j-v)
            for u in range(i+1) for v in range(j+1)}
        cs={e:c for e,c in cs.items() if c};support.update(cs);expansions.append(cs)
    labels=sorted(support)
    if len(labels)>8:raise ValueError('local monomial support eight budget exceeded')
    C=[[cs.get(e,0) for e in labels] for cs in expansions]
    V=[[u**i*v**j for u,v in local_points] for i,j in labels]
    certificate=weighted_determinant(C,V,[sum(e) for e in labels],m)
    expected=[[x**i*y**j for x,y in points] for i,j in exponents]
    if certificate['matrix']!=expected:raise ArithmeticError('source-coordinate polynomial expansion mismatch')
    return {'schema':'pp-chart-weighted-determinant/1','leaf_id':leaf_id,'source_points':points,
            'source_exponents':exponents,'local_points':local_points,'local_monomials':[list(e) for e in labels],
            'weighted_certificate':certificate,
            'auxiliary':auxiliary_packet(points,exponents) if certificate['determinant']==0 else None,
            'execution_verified':False}


def verify_chart_determinant(branch_packet,packet):
    try:
        return _canonical_equal(packet,chart_determinant(branch_packet,packet['leaf_id'],
                                     packet['source_points'],packet['source_exponents']))
    except (ValueError,TypeError,KeyError,IndexError,OverflowError):return False
