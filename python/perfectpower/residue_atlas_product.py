"""Complete coprime products of bivariate atlases, with factored storage.

Every local combination is retained. Rectangle traversal prunes only cells
proved empty by exact axis counts and rejects exhausted work budgets.
"""
from math import prod
import hashlib,json,re
from .residue_atlas import (atlas_packet,verify_atlas,native_atlas,_bounds,_axis_count,
                            _parameter,_canonical_equal)
from .bounded_residue_patch import formula,evaluate
from .residue_determinant import integer


def _crt(a,b,m,n):
    return (a+m*((b-a)*pow(m,-1,n)%n))%(m*n)


def _all_roots(atlases):
    if any(not a["roots"] for a in atlases):return []
    states=[(0,0,1)]
    for atlas in atlases:
        n=atlas['modulus']
        states=[(_crt(a,x,m,n),_crt(b,y,m,n),m*n) for a,b,m in states for x,y in atlas['roots']]
    return sorted([[a,b] for a,b,_ in states])


def compose_atlases(atlases,*,explicit_limit=4096):
    limit=_parameter(explicit_limit,'explicit_limit',100000)
    if not isinstance(atlases,list) or not 1<=len(atlases)<=8:
        raise ValueError('one through eight complete atlases required')
    if any(not verify_atlas(a) for a in atlases):raise ValueError('invalid local atlas')
    primes=[a['prime'] for a in atlases]
    if len(set(primes))!=len(primes):raise ValueError('distinct prime factors required')
    terms=atlases[0]['terms']
    if any(not _canonical_equal(a['terms'],terms) for a in atlases):raise ValueError('all factors must have identical normalized source')
    ordered=sorted(atlases,key=lambda a:a['prime'])
    count=prod(len(a['roots']) for a in ordered);period=prod(a['modulus'] for a in ordered)
    # Copy the packet tree to prevent aliases mutating retained evidence.
    local=json.loads(json.dumps(ordered))
    roots=_all_roots(local) if count<=limit else None
    return {'schema':'pp-residue-atlas-product/1','terms':json.loads(json.dumps(terms)),'locals':local,
            'modulus':period,'combination_count':count,'roots':roots,
            'representation':'explicit' if roots is not None else 'factored',
            'explicit_limit':limit,'complete_modular_cover':True,
            'global_obstruction':count==0,'execution_verified':False,'global_height_bound':False}


def product_packet(terms,factors,*,explicit_limit=4096):
    if not isinstance(factors,list) or not 1<=len(factors)<=8 or any(not isinstance(f,list) or len(f)!=2 for f in factors):
        raise ValueError('factors are one through eight [prime,exponent] pairs')
    return compose_atlases([atlas_packet(terms,p,k) for p,k in factors],explicit_limit=explicit_limit)


def verify_product(packet):
    try:
        if packet['schema']!='pp-residue-atlas-product/1':return False
        atlases=packet['locals'];limit=_parameter(packet['explicit_limit'],'explicit_limit',100000)
        if not isinstance(atlases,list) or not 1<=len(atlases)<=8 or any(not verify_atlas(a) for a in atlases):return False
        primes=[a['prime'] for a in atlases]
        if primes!=sorted(set(primes)):return False
        if any(not _canonical_equal(a['terms'],packet['terms']) for a in atlases):return False
        count=prod(len(a['roots']) for a in atlases);m=prod(a['modulus'] for a in atlases)
        expected=_all_roots(atlases) if count<=limit else None
        if expected is not None:
            allowed=[(a['modulus'],{tuple(z) for z in a['roots']}) for a in atlases]
            if len(expected)!=count or len({tuple(z) for z in expected})!=count:return False
            if any(not (0<=x<m and 0<=y<m) or any((x%n,y%n) not in roots for n,roots in allowed) for x,y in expected):return False
        return (_canonical_equal(packet['roots'],expected) and packet['representation']==('explicit' if expected is not None else 'factored')
                and integer(packet['modulus'])==m and integer(packet['combination_count'])==count
                and packet['complete_modular_cover'] is True and packet['global_obstruction'] is (count==0)
                and packet['execution_verified'] is False and packet['global_height_bound'] is False)
    except (KeyError,ValueError,TypeError,IndexError,OverflowError):return False


def product_contains(packet,point):
    if not verify_product(packet):raise ValueError('complete coprime product required')
    if not isinstance(point,list) or len(point)!=2:raise ValueError('two integer coordinates required')
    x,y=[integer(v,256) for v in point]
    return all([x%a['modulus'],y%a['modulus']] in a['roots'] for a in packet['locals'])


def _blocks(packet,bounds,work_limit):
    used=0
    def visit(depth,a,b,m):
        nonlocal used
        used+=1
        if used>work_limit:raise ValueError('complete CRT traversal exceeds work budget; no partial result')
        nx=_axis_count(*bounds[0],m,a);ny=_axis_count(*bounds[1],m,b)
        if not nx or not ny:return
        if depth==len(packet['locals']):
            yield a,b,nx,ny
            return
        atlas=packet['locals'][depth];n=atlas['modulus']
        for x,y in atlas['roots']:
            yield from visit(depth+1,_crt(a,x,m,n),_crt(b,y,m,n),m*n)
    if not packet["global_obstruction"]:
        yield from visit(0,0,0,1)


def _prepare(packet,bounds,work_limit):
    if not verify_product(packet):raise ValueError('complete coprime product required')
    return _bounds(bounds),_parameter(work_limit,'work_limit',2000000)


def product_population(packet,bounds,*,work_limit=200000):
    bounds,budget=_prepare(packet,bounds,work_limit)
    count=sum(nx*ny for _,_,nx,ny in _blocks(packet,bounds,budget))
    return {'bounds':bounds,'modulus':packet['modulus'],'count':count,
            'combination_count':packet['combination_count'],'representation':packet['representation'],
            'full_box_size':(bounds[0][1]-bounds[0][0]+1)*(bounds[1][1]-bounds[1][0]+1),
            'order':'sorted local-factor root tuples; within each CRT cell x then y ascending',
            'scope':'complete simultaneous modular candidates; source equality still required','execution_verified':False}


def product_select(packet,bounds,index,*,work_limit=200000):
    bounds,budget=_prepare(packet,bounds,work_limit);index=integer(index,1024)
    if index<0:raise IndexError('negative candidate rank')
    m=packet['modulus']
    for a,b,nx,ny in _blocks(packet,bounds,budget):
        size=nx*ny
        if index<size:
            u,v=divmod(index,ny)
            return [bounds[0][0]+(a-bounds[0][0])%m+u*m,bounds[1][0]+(b-bounds[1][0])%m+v*m]
        index-=size
    raise IndexError('candidate rank outside population')


def product_rank(packet,bounds,point,*,work_limit=200000):
    bounds,budget=_prepare(packet,bounds,work_limit)
    if not isinstance(point,list) or len(point)!=2:raise ValueError('two integer coordinates required')
    x,y=[integer(v,256) for v in point];m=packet['modulus'];offset=0
    if not bounds[0][0]<=x<=bounds[0][1] or not bounds[1][0]<=y<=bounds[1][1]:raise ValueError('point outside rectangle')
    for a,b,nx,ny in _blocks(packet,bounds,budget):
        if x%m==a and y%m==b:
            xf=bounds[0][0]+(a-bounds[0][0])%m;yf=bounds[1][0]+(b-bounds[1][0])%m
            return offset+((x-xf)//m)*ny+(y-yf)//m
        offset+=nx*ny
    raise ValueError('point fails simultaneous modular conditions')


def product_scan(packet,bounds,*,candidate_limit=4096,work_limit=200000):
    bounds,budget=_prepare(packet,bounds,work_limit);limit=_parameter(candidate_limit,'candidate_limit',100000)
    # Finish the entire traversal and check exact cardinality before evaluating any source point.
    count=sum(nx*ny for _,_,nx,ny in _blocks(packet,bounds,budget))
    if count>limit:raise ValueError('complete candidate population exceeds scan budget; no partial solution list')
    m=packet['modulus'];points=[]
    for a,b,nx,ny in _blocks(packet,bounds,budget):
        xf=bounds[0][0]+(a-bounds[0][0])%m;yf=bounds[1][0]+(b-bounds[1][0])%m
        for i in range(nx):
            for j in range(ny):
                z=[xf+i*m,yf+j*m]
                if evaluate(packet['terms'],*z)==0:points.append(z)
    return {'points':sorted(points),'bounds':bounds,'candidates_checked':count,
            'complete_in_box':True,'global_height_bound':False,'execution_verified':False}


def native_product(packet,bounds):
    if not verify_product(packet):raise ValueError('complete coprime product required')
    if max(prod(len(a['roots']) for a in packet['locals'][:i]) for i in range(1,len(packet['locals'])+1))>2048:
        raise ValueError('native CRT combination budget exceeded')
    bounds=_bounds(bounds);sources=[];names=[];imports={'import PerfectPower.ResidueAtlasCRT'}
    for atlas in packet['locals']:
        source=native_atlas(atlas,bounds);ns=re.search(r'^namespace (Atlas_\w+)$',source,re.M).group(1)
        names.append(ns)
        imports.update(line for line in source.splitlines() if line.startswith('import '))
        sources.append('\n'.join(line for line in source.splitlines() if not line.startswith('import ')))
    tag=hashlib.sha256(json.dumps([packet,bounds],sort_keys=True).encode()).hexdigest()[:16]
    lines=sorted(imports)+sources+[f'namespace Product_{tag}','open PerfectPower.ResidueAtlas PerfectPower.ResidueAtlasCRT',
                                 f'def F (x y : ℤ) : ℤ := {formula(packet["terms"])}']
    first=packet['locals'][0];m=first['modulus']
    lines += [f'def stage0 : AtlasPacket F {m} := {names[0]}.atlas{first["exponent"]}',
              f'theorem roots_count0 : stage0.roots.card = {len(first["roots"])} := by decide +kernel',
              '#print axioms roots_count0']
    for j,(atlas,ns) in enumerate(zip(packet['locals'][1:],names[1:]),1):
        n=atlas['modulus'];u=pow(m,-1,n);v=(1-u*m)//n
        count=prod(len(a['roots']) for a in packet['locals'][:j+1])
        lines += [f'def local{j} : AtlasPacket F {n} := {ns}.atlas{atlas["exponent"]}',
                  f'theorem coprime{j} : ({m} : ℤ).natAbs.Coprime ({n} : ℤ).natAbs := by decide +kernel',
                  f'theorem bezout{j} : ({u} : ℤ)*{m}+({v})*{n}=1 := by decide +kernel',
                  f'def stage{j} : AtlasPacket F {m*n} := merge stage{j-1} local{j} {u} ({v}) coprime{j} bezout{j}',
                  f'theorem roots_count{j} : stage{j}.roots.card = {count} := by',
                  f'  change (roots stage{j-1} local{j} {u} ({v})).card = {count}',
                  f'  rw [roots_card _ _ _ _ bezout{j}, roots_count{j-1}]; decide +kernel',
                  f'#print axioms coprime{j}',f'#print axioms bezout{j}',f'#print axioms roots_count{j}']
        m*=n
    j=len(packet['locals'])-1;(x0,x1),(y0,y1)=bounds
    count=product_population(packet,bounds)['count']
    lines += [f'def bounds : Bounds := (({x0},{x1}),({y0},{y1}))',
              f'theorem complete (x y : ℤ) : (x % {m},y % {m}) ∈ stage{j}.roots ↔ F x y % {m}=0 := stage{j}.complete x y',
              f'theorem count_checked : (candidates stage{j} bounds).card = {count} := by',
              ('  rw [card_candidates]; decide +kernel' if j==0 else f'  change (candidates (merge stage{j-1} local{j} {u} ({v}) coprime{j} bezout{j}) bounds).card = {count}\n  rw [merged_count]; decide +kernel'),
              f'theorem source_survives (x y : ℤ) (hF : F x y=0) : (x % {m},y % {m}) ∈ stage{j}.roots := stage{j}.source_survives x y hF',
              '#print axioms complete','#print axioms count_checked','#print axioms source_survives']
    if packet['global_obstruction']:
        lines += [f'theorem no_integer_solution (x y : ℤ) : F x y ≠ 0 := stage{j}.empty_obstruction (by decide +kernel) x y',
                  '#print axioms no_integer_solution']
    if (x1-x0+1)*(y1-y0+1)<=1024 and count<=512:
        points=product_scan(packet,bounds)['points'];from .bounded_residue_patch import _finset
        lines += [f'def points : Finset (ℤ × ℤ) := {_finset(points)}',
                  f'theorem points_checked : solutions stage{j} bounds=points := by decide +kernel',
                  f'theorem points_complete (x y : ℤ) : (x,y) ∈ points ↔ {x0}≤x ∧ x≤{x1} ∧ {y0}≤y ∧ y≤{y1} ∧ F x y=0 := by',
                  f'  rw [← points_checked]; exact solutions_complete stage{j} bounds x y',
                  '#print axioms points_checked','#print axioms points_complete']
    lines += [f'end Product_{tag}'];return '\n'.join(lines)+'\n'
