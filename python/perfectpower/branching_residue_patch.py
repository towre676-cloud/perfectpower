"""Content-normalized residue blowups with complete bounded source coverage.

Singular parents can become horizontal or vertical after exact prime-content
removal. All residue branches survive until excluded by a normalized modular
obstruction or by the declared box. Candidate cells are disjoint.
"""
from math import comb
import hashlib
import json
from .bounded_residue_patch import terms_checked,evaluate
from .residue_atlas import _bounds,_parameter,_axis_count,_canonical_equal
from .residue_determinant import integer


def _pullback(terms,p,a,b):
    cs={}
    for c,i,j in terms:
        for u in range(i+1):
            for v in range(j+1):
                cs[u,v]=integer(cs.get((u,v),0)+c*comb(i,u)*comb(j,v)*a**(i-u)*b**(j-v)*p**(u+v),256)
    cs={ij:c for ij,c in cs.items() if c}
    # The zero source is rejected; a nondegenerate affine substitution is injective.
    valuation=min(_valuation(c,p) for c in cs.values())
    content=p**valuation
    return [[c//content,u,v] for (u,v),c in sorted(cs.items())],content,valuation


def _valuation(c,p):
    v=0
    while c%p==0:c//=p;v+=1
    return v


def _chart(terms,p,a,b):
    dx=sum(c*i*a**(i-1)*b**j for c,i,j in terms if i)%p
    dy=sum(c*j*a**i*b**(j-1) for c,i,j in terms if j)%p
    return 'vertical' if dy else 'horizontal' if dx else 'singular'


def branching_patch(terms,bounds,prime,exponent,*,work_limit=200000):
    terms=terms_checked(terms);bounds=_bounds(bounds)
    if not terms:raise ValueError('nonzero source polynomial required')
    p=_parameter(prime,'prime',7)
    if p<2 or any(p%d==0 for d in range(2,p)):raise ValueError('prime 2, 3, 5 or 7 required')
    depth=_parameter(exponent,'exponent',4);budget=_parameter(work_limit,'work_limit',2000000)
    nodes=[];leaves=[];used=0;switches=0
    counts={'vertical':0,'horizontal':0,'singular':0,'dead_normalized_nodes':0,'box_pruned':0}
    def visit(H,a,b,m,C,level,previous):
        nonlocal used,switches
        used+=1
        if used>budget:raise ValueError('complete branching work exceeds budget; no partial result')
        node_id=len(nodes)
        node={'id':node_id,'depth':level,'source_residue':[a,b],'step':m,
              'content':C,'terms':H,'previous_chart':previous,'roots':None,'branches':[]}
        nodes.append(node)
        if level==depth:
            leaves.append(node_id);return node_id
        roots=[]
        for r in range(p):
            for s in range(p):
                used+=1
                if used>budget:raise ValueError('complete branching work exceeds budget; no partial result')
                if evaluate(H,r,s)%p==0:roots.append([r,s])
        node['roots']=roots
        if not roots:counts['dead_normalized_nodes']+=1
        for r,s in roots:
            kind=_chart(H,p,r,s);counts[kind]+=1
            switched=previous is not None and previous!=kind
            switches+=int(switched)
            G,c,v=_pullback(H,p,r,s)
            if v<1:raise ArithmeticError('root pullback is not divisible by the prime')
            aa,bb,mm=a+m*r,b+m*s,m*p
            active=bool(_axis_count(*bounds[0],mm,aa) and _axis_count(*bounds[1],mm,bb))
            child=visit(G,aa,bb,mm,C*c,level+1,kind) if active else None
            if not active:counts['box_pruned']+=1
            node['branches'].append({'residue':[r,s],'chart':kind,'switched':switched,
                                      'removed_prime_exponent':v,'child':child,'active':active})
        return node_id
    visit(terms,0,0,1,1,0,None)
    candidate_count=sum(_axis_count(*bounds[0],nodes[i]['step'],nodes[i]['source_residue'][0])*
                        _axis_count(*bounds[1],nodes[i]['step'],nodes[i]['source_residue'][1]) for i in leaves)
    return {'schema':'pp-branching-residue-patch/2','terms':terms,'bounds':bounds,'prime':p,
            'exponent':depth,'work_limit':budget,'work':used,'nodes':nodes,'leaf_ids':leaves,
            'node_counts':counts,'chart_switch_count':switches,'candidate_count':candidate_count,
            'complete_source_cover':True,'complete_in_box':True,
            'global_height_bound':False,'execution_verified':False}


def verify_branching_patch(packet):
    try:
        return _canonical_equal(packet,branching_patch(packet['terms'],packet['bounds'],packet['prime'],
                                 packet['exponent'],work_limit=packet['work_limit']))
    except (ValueError,TypeError,KeyError,IndexError,OverflowError):return False


def _check(packet):
    if not verify_branching_patch(packet):raise ValueError('complete branching residue patch required')


def _cells(packet):
    for i in packet['leaf_ids']:
        n=packet['nodes'][i];a,b=n['source_residue'];m=n['step']
        yield n,a,b,m,_axis_count(*packet['bounds'][0],m,a),_axis_count(*packet['bounds'][1],m,b)


def patch_select(packet,index):
    _check(packet);index=integer(index,1024)
    if index<0:raise IndexError('negative candidate rank')
    for _,a,b,m,nx,ny in _cells(packet):
        if index<nx*ny:
            u,v=divmod(index,ny);xl=packet['bounds'][0][0];yl=packet['bounds'][1][0]
            return [xl+(a-xl)%m+u*m,yl+(b-yl)%m+v*m]
        index-=nx*ny
    raise IndexError('candidate rank outside population')


def patch_rank(packet,point):
    _check(packet)
    if not isinstance(point,list) or len(point)!=2:raise ValueError('two integer coordinates required')
    x,y=[integer(v,256) for v in point]
    if not all(lo<=z<=hi for z,(lo,hi) in zip((x,y),packet['bounds'])):raise ValueError('point outside bounds')
    total=0
    for _,a,b,m,nx,ny in _cells(packet):
        if (x%m,y%m)==(a,b):
            xl=packet['bounds'][0][0];yl=packet['bounds'][1][0]
            return total+(x-(xl+(a-xl)%m))//m*ny+(y-(yl+(b-yl)%m))//m
        total+=nx*ny
    raise ValueError('point outside normalized residue cover')


def patch_scan(packet,*,candidate_limit=100000):
    _check(packet);cap=_parameter(candidate_limit,'candidate_limit',1000000)
    if packet['candidate_count']>cap:raise ValueError('complete candidate scan exceeds budget; no partial result')
    points=[];xl=packet['bounds'][0][0];yl=packet['bounds'][1][0]
    for node,a,b,m,nx,ny in _cells(packet):
        x0=xl+(a-xl)%m;y0=yl+(b-yl)%m
        for u in range(nx):
            for v in range(ny):
                x,y=x0+m*u,y0+m*v
                if evaluate(node['terms'],(x-a)//m,(y-b)//m)==0:points.append([x,y])
    return {'points':sorted(points),'candidate_count':packet['candidate_count'],
            'complete_in_box':True,'global_height_bound':False,'execution_verified':False}


def native_branching_patch(packet):
    _check(packet)
    if len(packet['nodes'])>64:raise ValueError('native chart-node budget sixty-four exceeded')
    from .bounded_residue_patch import formula
    from .residue_atlas import _finset
    ns='Branching_'+hashlib.sha256(json.dumps(packet,sort_keys=True).encode()).hexdigest()[:16]
    lines=['import PerfectPower.BranchingResidueCharts','set_option maxHeartbeats 0',
           'set_option maxRecDepth 100000',f'namespace {ns}',
           'open PerfectPower.BranchingResidueCharts',f'def F (x y : ℤ) : ℤ := {formula(packet["terms"])}']
    for node in packet['nodes']:
        i=node['id'];a,b=node['source_residue'];m=node['step'];c=node['content']
        lines += [f'def G{i} (u v : ℤ) : ℤ := {formula(node["terms"],"u","v")}',
                  f'theorem identity{i} (u v : ℤ) : F ({a}+{m}*u) ({b}+{m}*v) = ({c})*G{i} u v := by unfold F G{i}; ring',
                  f'def chart{i} : Chart F := ⟨{a},{b},{m},{c},G{i},by norm_num,by norm_num,identity{i}⟩',
                  f'theorem zeros{i} (u v : ℤ) : F ({a}+{m}*u) ({b}+{m}*v)=0 ↔ G{i} u v=0 := chart{i}.zero_iff u v',
                  f'#print axioms identity{i}',f'#print axioms zeros{i}']
    (x0,x1),(y0,y1)=packet['bounds']
    if (x1-x0+1)*(y1-y0+1)<=1024 and packet['candidate_count']<=512:
        points=patch_scan(packet)['points']
        lines += [f'def bounds : PerfectPower.ResidueAtlas.Bounds := (({x0},{x1}),({y0},{y1}))',
                  f'def points : Finset (ℤ×ℤ) := {_finset(points)}',
                  'theorem points_checked : boxZeros F bounds = points := by decide +kernel',
                  f'theorem points_complete (x y : ℤ) : (x,y) ∈ points ↔',
                  f'    {x0}≤x ∧ x≤{x1} ∧ {y0}≤y ∧ y≤{y1} ∧ F x y=0 := by',
                  '  rw [← points_checked];exact boxZeros_complete F bounds x y',
                  '#print axioms points_checked','#print axioms points_complete']
    lines.append('end '+ns)
    return '\n'.join(lines)+'\n'
