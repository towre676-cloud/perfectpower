"""Complete bivariate prime-power residues, including every singular branch.

Rectangle populations are modular candidates, not solutions. Counts and
class-major rank/select do not enumerate the rectangle. Exact source scanning
is performed only if the entire surviving population fits its budget.
"""
from math import isqrt
import hashlib
import json
from .bounded_residue_patch import terms_checked, evaluate, formula, _finset
from .residue_determinant import integer


def _parameter(value, name, cap):
    value = integer(value, 32)
    if not 1 <= value <= cap:
        raise ValueError(f'{name} must lie in [1,{cap}]')
    return value


def _derivative(terms, a, b, axis):
    return sum(c * (i if axis == 0 else j) * a**(i-(axis == 0)) * b**(j-(axis == 1))
               for c, i, j in terms if (i if axis == 0 else j))


def _node(terms, p, m, a, b):
    c = evaluate(terms, a, b)//m
    dx = _derivative(terms, a, b, 0)
    dy = _derivative(terms, a, b, 1)
    chart = 'vertical' if dy % p else 'horizontal' if dx % p else 'singular'
    return {'parent': [a, b], 'constant': c, 'dx': dx, 'dy': dy,
            'chart': chart, 'obstructed': chart == 'singular' and c % p != 0}


def atlas_packet(terms, prime, exponent, *, modulus_limit=256, work_limit=200000):
    terms = terms_checked(terms)
    if not terms:
        raise ValueError('nonzero source polynomial required')
    p = _parameter(prime, 'prime', 257)
    if p < 2 or any(p % d == 0 for d in range(2, isqrt(p)+1)):
        raise ValueError('prime required')
    k = _parameter(exponent, 'exponent', 8)
    cap = _parameter(modulus_limit, 'modulus_limit', 256)
    work_cap = _parameter(work_limit, 'work_limit', 2000000)
    if p**k > cap:
        raise ValueError('complete prime-power modulus exceeds budget')
    work = p*p
    if work > work_cap:
        raise ValueError('complete residue work exceeds budget')
    roots = [[a,b] for a in range(p) for b in range(p) if evaluate(terms,a,b) % p == 0]
    levels = [{'power':1, 'modulus':p, 'roots':roots, 'nodes':[]}]
    m = p
    for e in range(2,k+1):
        nodes = []; lifted = []
        for a,b in roots:
            node = _node(terms,p,m,a,b); c,dx,dy = node['constant'],node['dx'],node['dy']
            chart = node['chart']
            cost = p if chart != 'singular' else 0 if node['obstructed'] else p*p
            work += cost
            if work > work_cap:
                raise ValueError('complete residue work exceeds budget; no partial atlas')
            if chart == 'vertical':
                pairs = [(u,(-c-dx*u)*pow(dy,-1,p) % p) for u in range(p)]
            elif chart == 'horizontal':
                pairs = [((-c-dy*v)*pow(dx,-1,p) % p,v) for v in range(p)]
            else:
                pairs = [] if node['obstructed'] else [(u,v) for u in range(p) for v in range(p)]
            children = [[a+m*u,b+m*v] for u,v in pairs]
            if any(evaluate(terms,*z) % (m*p) for z in children):
                raise ArithmeticError('first-order lift identity failed')
            node['children'] = sorted(children)
            nodes.append(node); lifted.extend(children)
        roots = sorted(lifted);m *= p
        levels.append({'power':e,'modulus':m,'roots':roots,'nodes':nodes})
    return {'schema':'pp-residue-atlas/1','terms':terms,'prime':p,'exponent':k,
            'modulus':m,'roots':roots,'levels':levels,'work':work,
            'complete_modular_cover':True,'global_obstruction':not roots,
            'execution_verified':False,'global_height_bound':False}


def _canonical_equal(left, right):
    # JSON equality distinguishes true from 1 and rejects malformed nesting.
    return json.dumps(left,sort_keys=True,separators=(',',':')) == json.dumps(right,sort_keys=True,separators=(',',':'))


def verify_atlas(packet):
    """Independent full-square census at every level; no lift discovery call."""
    try:
        if packet['schema'] != 'pp-residue-atlas/1': return False
        terms = terms_checked(packet['terms']);p = _parameter(packet['prime'],'prime',257)
        k = _parameter(packet['exponent'],'exponent',8)
        if not terms or p < 2 or any(p % d == 0 for d in range(2,isqrt(p)+1)) or p**k>256:
            return False
        if not _canonical_equal(terms,packet['terms']) or len(packet['levels']) != k:
            return False
        previous = [];work = p*p
        for e,row in enumerate(packet['levels'],1):
            m = p**e
            roots = [[a,b] for a in range(m) for b in range(m) if evaluate(terms,a,b) % m == 0]
            nodes = []
            if e>1:
                old = m//p
                buckets = {tuple(z):[] for z in previous}
                for z in roots: buckets[z[0]%old,z[1]%old].append(z)
                for a,b in previous:
                    node = _node(terms,p,old,a,b);node['children'] = buckets[a,b]
                    work += p if node['chart'] != 'singular' else 0 if node['obstructed'] else p*p
                    nodes.append(node)
            expected = {'power':e,'modulus':m,'roots':roots,'nodes':nodes}
            if not _canonical_equal(expected,row): return False
            previous = roots
        return (_canonical_equal(packet['roots'],previous) and integer(packet['modulus']) == p**k
                and integer(packet['work']) == work and packet['complete_modular_cover'] is True
                and packet['global_obstruction'] is (not previous)
                and packet['execution_verified'] is False and packet['global_height_bound'] is False)
    except (ValueError,TypeError,KeyError,IndexError,OverflowError):
        return False


def _bounds(bounds):
    if not isinstance(bounds,list) or len(bounds)!=2 or any(not isinstance(v,list) or len(v)!=2 for v in bounds):
        raise ValueError('bounds are [[xmin,xmax],[ymin,ymax]]')
    result = [[integer(x,256) for x in row] for row in bounds]
    if any(lo>hi for lo,hi in result):raise ValueError('ordered closed axes required')
    return result


def _axis_count(lo,hi,m,r):
    return (hi-r)//m-(lo-1-r)//m


def _blocks(packet,bounds):
    m = packet['modulus']
    return [(a,b,_axis_count(*bounds[0],m,a),_axis_count(*bounds[1],m,b)) for a,b in packet['roots']]


def atlas_population(packet,bounds):
    if not verify_atlas(packet):raise ValueError('complete atlas required')
    bounds = _bounds(bounds)
    blocks = _blocks(packet,bounds)
    count = sum(nx*ny for _,_,nx,ny in blocks)
    return {'bounds':bounds,'modulus':packet['modulus'],'count':count,
            'class_count':len(blocks),'full_box_size':(bounds[0][1]-bounds[0][0]+1)*(bounds[1][1]-bounds[1][0]+1),
            'order':'residue-class lexicographic; within class x then y ascending',
            'scope':'all modular candidates; source equality still required','execution_verified':False}


def atlas_select(packet,bounds,index):
    if not verify_atlas(packet):raise ValueError('complete atlas required')
    bounds = _bounds(bounds);index = integer(index,1024)
    if index<0:raise IndexError('negative candidate rank')
    m = packet['modulus']
    for a,b,nx,ny in _blocks(packet,bounds):
        size = nx*ny
        if index<size:
            u,v = divmod(index,ny)
            return [bounds[0][0]+(a-bounds[0][0])%m+u*m,
                    bounds[1][0]+(b-bounds[1][0])%m+v*m]
        index -= size
    raise IndexError('candidate rank outside population')


def atlas_rank(packet,bounds,point):
    if not verify_atlas(packet):raise ValueError('complete atlas required')
    bounds = _bounds(bounds)
    if not isinstance(point,list) or len(point)!=2:raise ValueError('two integer coordinates required')
    x,y = [integer(v,256) for v in point];m = packet['modulus'];offset = 0
    if not bounds[0][0]<=x<=bounds[0][1] or not bounds[1][0]<=y<=bounds[1][1]:
        raise ValueError('point outside rectangle')
    for a,b,nx,ny in _blocks(packet,bounds):
        if x%m==a and y%m==b:
            xfirst = bounds[0][0]+(a-bounds[0][0])%m
            yfirst = bounds[1][0]+(b-bounds[1][0])%m
            return offset+((x-xfirst)//m)*ny+(y-yfirst)//m
        offset += nx*ny
    raise ValueError('point fails source modular condition')


def atlas_scan(packet,bounds,*,candidate_limit=4096):
    population = atlas_population(packet,bounds)
    budget = _parameter(candidate_limit,'candidate_limit',100000)
    if population['count']>budget:raise ValueError('complete candidate population exceeds scan budget; no partial solution list')
    bounds = population['bounds'];m = packet['modulus'];points = []
    for a,b,nx,ny in _blocks(packet,bounds):
        xfirst = bounds[0][0]+(a-bounds[0][0])%m;yfirst = bounds[1][0]+(b-bounds[1][0])%m
        for i in range(nx):
            for j in range(ny):
                z = [xfirst+i*m,yfirst+j*m]
                if evaluate(packet['terms'],*z)==0:points.append(z)
    return {'points':sorted(points),'bounds':bounds,'candidates_checked':population['count'],
            'complete_in_box':True,'global_height_bound':False,'execution_verified':False}


def _remainder(terms,a,b,m):
    from math import comb
    result = {}
    for c,i,j in terms:
        for u in range(i+1):
            for v in range(j+1):
                if u+v>=2:
                    result[u,v] = result.get((u,v),0)+c*comb(i,u)*comb(j,v)*a**(i-u)*b**(j-v)*m**(u+v-2)
    return [[c,u,v] for (u,v),c in sorted(result.items()) if c]


def _period_proof(terms):
    proofs = [f'((Int.ModEq.refl ({c})).mul (Int.ModEq.pow {i} hx)).mul (Int.ModEq.pow {j} hy)' for c,i,j in terms]
    result = '('+proofs[0]+')'
    for proof in proofs[1:]:result = f'({result}.add ({proof}))'
    return result


def native_atlas(packet,bounds):
    if not verify_atlas(packet):raise ValueError('complete atlas required')
    if packet['modulus']>32 or sum(len(row['nodes']) for row in packet['levels'])>64:
        raise ValueError('native atlas modulus/node budget exceeded')
    bounds = _bounds(bounds);tag = hashlib.sha256(json.dumps([packet,bounds],sort_keys=True).encode()).hexdigest()[:16]
    ns = 'Atlas_'+tag;p = packet['prime'];terms = packet['terms']
    lines = ['import PerfectPower.ResidueAtlas','import Mathlib.Tactic','import Mathlib.Data.Int.ModEq','set_option maxRecDepth 100000',
             'set_option maxHeartbeats 0',f'namespace {ns}','open PerfectPower.ResidueAtlas',
             f'def F (x y : ℤ) : ℤ := {formula(terms)}',f'theorem prime_checked : Nat.Prime {p} := by norm_num',
             '#print axioms prime_checked']
    for row in packet['levels']:
        e,m = row['power'],row['modulus']
        lines += [f'def roots{e} : Finset (ℤ × ℤ) := {_finset(row["roots"])}',
                  f'theorem periodic{e} (x y : ℤ) : F x y % {m} = F (x % {m}) (y % {m}) % {m} := by',
                  f'  change Int.ModEq {m} (F x y) (F (x % {m}) (y % {m}))',
                  f'  have hx : Int.ModEq {m} x (x % {m}) := (Int.mod_modEq x {m}).symm',
                  f'  have hy : Int.ModEq {m} y (y % {m}) := (Int.mod_modEq y {m}).symm',
                  '  unfold F',f'  exact {_period_proof(terms)}',
                  f'theorem checked{e} : rootTable F {m} = roots{e} := by decide +kernel',
                  f'def atlas{e} : AtlasPacket F {m} := ⟨by norm_num, roots{e}, checked{e}, periodic{e}⟩',
                  f'theorem complete{e} (x y : ℤ) : (x % {m},y % {m}) ∈ roots{e} ↔ F x y % {m} = 0 := atlas{e}.complete x y',
                  f'#print axioms periodic{e}',f'#print axioms checked{e}',f'#print axioms complete{e}']
        for i,node in enumerate(row['nodes']):
            old = m//p;a,b = node['parent'];c,dx,dy = node['constant'],node['dx'],node['dy'];name = f'lift{e}_{i}'
            rem = formula(_remainder(terms,a,b,old),'u','v')
            lines += [f'def {name}R (u v : ℤ) : ℤ := {rem}',
                      f'theorem {name}_identity (u v : ℤ) : F ({a}+{old}*u) ({b}+{old}*v) =',
                      f'    {old}*(({c})+({dx})*u+({dy})*v)+{old}^2*{name}R u v := by unfold F {name}R; ring',
                      f'def {name} : LiftPacket F {p} {old} {a} {b} := ⟨{c},{dx},{dy},{name}R,{name}_identity⟩',
                      f'theorem {name}_complete (u v : ℤ) : ({old}*{p} : ℤ) ∣ F ({a}+{old}*u) ({b}+{old}*v) ↔',
                      f'    ({p} : ℤ) ∣ ({c})+({dx})*u+({dy})*v := {name}.step (by norm_num) (by norm_num) u v',
                      f'theorem {name}_children : childTable F {p} {old} {a} {b} = {_finset(node["children"])} := by decide +kernel',
                      f'#print axioms {name}_identity',f'#print axioms {name}_complete',f'#print axioms {name}_children']
    e = packet['exponent'];m = packet['modulus'];(x0,x1),(y0,y1) = bounds
    count = atlas_population(packet,bounds)['count']
    lines += [f'def bounds : (ℤ × ℤ) × (ℤ × ℤ) := (({x0},{x1}),({y0},{y1}))',
              f'theorem count_checked : (candidates atlas{e} bounds).card = {count} := by',
              f'  rw [card_candidates]; decide +kernel',f'#print axioms count_checked',
              f'theorem source_survives (x y : ℤ) (hF : F x y = 0) : (x % {m},y % {m}) ∈ roots{e} := atlas{e}.source_survives x y hF',
              '#print axioms source_survives']
    if (x1-x0+1)*(y1-y0+1)<=1024 and count<=512:
        scan = atlas_scan(packet,bounds)
        lines += [f'def points : Finset (ℤ × ℤ) := {_finset(scan["points"])}',
                  f'theorem points_checked : solutions atlas{e} bounds = points := by decide +kernel',
                  f'theorem points_complete (x y : ℤ) : (x,y) ∈ points ↔',
                  f'    {x0} ≤ x ∧ x ≤ {x1} ∧ {y0} ≤ y ∧ y ≤ {y1} ∧ F x y = 0 := by',
                  f'  rw [← points_checked]; exact solutions_complete atlas{e} bounds x y',
                  '#print axioms points_checked','#print axioms points_complete']
    if not packet['roots']:
        lines += [f'theorem no_integer_solution (x y : ℤ) : F x y ≠ 0 := atlas{e}.empty_obstruction rfl x y',
                  '#print axioms no_integer_solution']
    lines += [f'end {ns}']
    return '\n'.join(lines)+'\n'
