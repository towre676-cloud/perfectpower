"""Exact real-plane identities by finite sign splits and Farkas contradictions.

Fourier-Motzkin only proposes rational linear witnesses. Lean independently
checks the tree and interprets its conclusion at every real point.
"""
from fractions import Fraction as Q
from hashlib import sha256
import json,re
from .divisor_square import Budget,WorkLimit
from .euclid_geometry import point


def neg(a):return tuple(-x for x in a)
def lt(a):return ('lt',a)
def eq(a):return ('eq',a)
def not_(f):return ('neg',f)
def and_(f,g):return ('conj',f,g)
def or_(f,g):return not_(and_(not_(f),not_(g)))
def ge(a):return not_(lt(a))
def all_(fs):
    out=('truth',True)
    for f in reversed(fs):out=and_(f,out)
    return out

def any_(fs):
    out=('truth',False)
    for f in reversed(fs):out=or_(f,out)
    return out

def same(f,g):return not_(or_(and_(f,not_(g)),and_(not_(f),g)))
def side(a,b):
    dx=b[0]-a[0];dy=b[1]-a[1]
    return (-dy,dx,dy*a[0]-dx*a[1])
def xline(x):return (Q(1),Q(0),-x)
def yline(y):return (Q(0),Q(1),-y)

def boundary(a,b):return all_([eq(side(a,b)),ge(xline(min(a[0],b[0]))),
    ge(neg(xline(max(a[0],b[0])))),ge(yline(min(a[1],b[1]))),ge(neg(yline(max(a[1],b[1]))))])
def polygon_parts(vertices):
    edges=list(zip(vertices,vertices[1:]+vertices[:1]));rays=[]
    for a,b in edges:
        if a[1]<b[1]:rays.append((1,yline(a[1]),yline(b[1]),neg(side(a,b))))
        elif b[1]<a[1]:rays.append((-1,yline(b[1]),yline(a[1]),side(a,b)))
        else:rays.append((0,(Q(0),)*3,(Q(0),)*3,(Q(0),)*3))
    return any_([boundary(a,b) for a,b in edges]),('winding',rays)
def filled(vertices):
    b,w=polygon_parts(vertices);return or_(b,w)
def interior(vertices):
    b,w=polygon_parts(vertices);return and_(not_(b),w)
def triangle(t):return all_([ge(side(t[0],t[1])),ge(side(t[1],t[2])),ge(side(t[2],t[0]))])

def leaves(f):
    if f[0] in ('lt','eq'):return [f[1]]
    if f[0]=='truth':return []
    if f[0]=='winding':return [p for r in f[1] for p in r[1:]]
    if f[0]=='neg':return leaves(f[1])
    return leaves(f[1])+leaves(f[2])
def evaluate(f,assignment):
    k=f[0]
    if k=='lt':return assignment[f[1]]==-1
    if k=='eq':return assignment[f[1]]==0
    if k=='truth':return f[1]
    if k=='winding':return sum(r[0] for r in f[1] if assignment[r[1]]!=-1 and assignment[r[2]]==-1 and assignment[r[3]]==-1)!=0
    if k=='neg':return not evaluate(f[1],assignment)
    return evaluate(f[1],assignment) and evaluate(f[2],assignment)

def constraints(assignment):
    out=[]
    for a,s in assignment:
        if s==-1:out.append((neg(a),True))
        elif s==0:out.extend(((a,False),(neg(a),False)))
        else:out.append((a,True))
    return out


def contradiction(cs,budget):
    n=len(cs)
    rows=[(a,strict,tuple(Q(i==j) for j in range(n))) for i,(a,strict) in enumerate(cs)]
    def dedup(rows):
        seen={}
        for a,strict,w in rows:
            if a[0]==a[1]==0:
                if a[2]<0 or a[2]==0 and strict:return w,None
                continue
            scale=next(abs(x) for x in a if x)
            a=tuple(x/scale for x in a);w=tuple(x/scale for x in w)
            if a not in seen or strict and not seen[a][1]:seen[a]=(a,strict,w)
        return None,list(seen.values())
    witness,rows=dedup(rows)
    if witness is not None:return witness
    for axis in (0,1):
        positive=[r for r in rows if r[0][axis]>0];negative=[r for r in rows if r[0][axis]<0]
        new=[r for r in rows if r[0][axis]==0]
        for a,sa,wa in positive:
            for b,sb,wb in negative:
                budget.spend();pa=a[axis];pb=-b[axis]
                c=tuple(x/pa+y/pb for x,y in zip(a,b))
                w=tuple(x/pa+y/pb for x,y in zip(wa,wb))
                if c[0]==c[1]==0 and (c[2]<0 or c[2]==0 and (sa or sb)):return w
                new.append((c,sa or sb,w))
        witness,rows=dedup(new)
        if witness is not None:return witness
    return None


def prove(f,*,work_limit=1000000,atom_limit=64):
    atoms=list(dict.fromkeys(leaves(f)))
    if len(atoms)>atom_limit:raise WorkLimit('real-plane atom budget exceeded')
    budget=Budget(work_limit);stats={'nodes':0,'leaves':0,'contradictions':0,'atoms':len(atoms)}
    def recurse(depth,assignment):
        budget.spend();stats['nodes']+=1
        witness=contradiction(constraints(assignment),budget)
        if witness is not None:
            stats['contradictions']+=1;return ('impossible',[(c,w) for c,w in zip(constraints(assignment),witness) if w])
        if depth==len(atoms):
            if not evaluate(f,dict(assignment)):raise ValueError('real-plane identity has a feasible counterexample sign region')
            stats['leaves']+=1;return ('leaf',)
        a=atoms[depth]
        return ('split',a,*(recurse(depth+1,[(a,s),*assignment]) for s in (-1,0,1)))
    tree=recurse(0,[]);stats['work']=budget.used
    return tree,stats


def _q(x):
    x=Q(x);return f'(({x.numerator} : ℚ)/({x.denominator} : ℚ))'
def _plane(a):return '('+','.join(map(_q,a))+')'
def _point(p):return '('+','.join(map(_q,p))+')'
def _list(xs):return '['+','.join(xs)+']'
def _formula(f):
    k=f[0]
    if k in ('lt','eq'):return '(.'+k+' '+_plane(f[1])+')'
    if k=='truth':return '(.truth '+str(f[1]).lower()+')'
    if k=='winding':return '(.winding '+_list('('+str(r[0])+','+','.join(map(_plane,r[1:]))+')' for r in f[1])+')'
    if k=='neg':return '(.neg '+_formula(f[1])+')'
    return '(.conj '+_formula(f[1])+' '+_formula(f[2])+')'
def _tree(t):
    if t[0]=='leaf':return '.leaf'
    if t[0]=='impossible':return '(.impossible '+_list('(('+_plane(c[0])+','+str(c[1]).lower()+'),'+_q(w)+')' for c,w in t[1])+')'
    return '(.split '+_plane(t[1])+' '+ ' '.join(map(_tree,t[2:]))+')'


def tree_definitions(tree,formula='formula',prefix='cert'):
    lines=[f'def {prefix}_context_0 : Assignment := []'];counter=0
    def walk(t,ctx):
        nonlocal counter
        counter+=1;i=counter;name=f'{prefix}_tree_{i}';proof=f'{prefix}_checked_{i}'
        if t[0]=='split':
            children=[]
            for sign,subtree in zip((-1,0,1),t[2:]):
                c=f'{prefix}_context_{counter+1}'
                lines.append(f'def {c} : Assignment := ({_plane(t[1])},{sign})::{ctx}')
                children.append(walk(subtree,c))
            lines.append(f'def {name} : Tree := .split {_plane(t[1])} '+ ' '.join(n for n,p in children))
            lines.append(f'theorem {proof} : checked {formula} {ctx} {name} := '+
                f'checked_split {formula} {ctx} {_plane(t[1])} '+ ' '.join(n for n,p in children)+' '+ ' '.join(p for n,p in children))
        else:
            lines.append(f'def {name} : Tree := {_tree(t)}')
            lines.append(f'theorem {proof} : checked {formula} {ctx} {name} := by decide +kernel')
        return name,proof
    root,proof=walk(tree,prefix+'_context_0')
    return lines,root,proof

def compile_mesh_coverage(vertices,triangles,*,namespace='MeshCoverage',work_limit=1000000,atom_limit=64):
    if not re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',namespace):raise ValueError('simple namespace required')
    from .geometry_certificates import certify_mesh
    packet=certify_mesh(vertices,triangles,work_limit=work_limit)
    vertices=list(map(point,packet['vertices']));triangles=[list(map(point,t)) for t in packet['triangles']]
    f=same(filled(vertices),any_([triangle(t) for t in triangles]));tree,stats=prove(f,work_limit=work_limit,atom_limit=atom_limit)
    tree_lines,root,proof=tree_definitions(tree)
    source='\n'.join(['import PerfectPower.PlanarGeometry','set_option maxRecDepth 100000',
      'set_option maxHeartbeats 16000000','open PerfectPower.PlanarCertificates PerfectPower.PlanarGeometry',
      f'namespace {namespace}',f'def vertices : List QPoint := {_list(map(_point,vertices))}',
      f'def triangles : List (QPoint × QPoint × QPoint) := {_list("("+",".join(map(_point,t))+")" for t in triangles)}',
      'def formula := coverageFormula vertices triangles',*tree_lines,f'def proofTree : Tree := {root}',
      f'theorem source_checked : checked formula [] proofTree := {proof}',
      'theorem source_coverage : ∀ p : Point, Filled vertices p ↔ MeshCovered triangles p :=',
      '  coverage_from_tree vertices triangles proofTree source_checked',
      '#print axioms source_coverage',f'end {namespace}'])+'\n'
    result={'schema':'pp-real-mesh-coverage/1','mesh':packet,'tree_statistics':stats,
            'scope':'all real points: closed nonzero-winding source region equals union of supplied closed oriented triangles; no Jordan interior identification, clearance or physics claim',
            'proof':{'source_sha256':sha256(source.encode()).hexdigest(),'kernel_checked':False}}
    return result,source


def map_planes(f,fn):
    if f[0] in ('lt','eq'):return (f[0],fn(f[1]))
    if f[0]=='truth':return f
    if f[0]=='winding':return ('winding',[(r[0],*(fn(p) for p in r[1:])) for r in f[1]])
    if f[0]=='neg':return not_(map_planes(f[1],fn))
    return and_(map_planes(f[1],fn),map_planes(f[2],fn))

def segment_formula(polygons,a,b):
    def along(p):return (p[0]*(b[0]-a[0])+p[1]*(b[1]-a[1]),Q(0),p[0]*a[0]+p[1]*a[1]+p[2])
    forbidden=any_([interior(p) for p in polygons])
    return or_(lt((Q(1),Q(0),Q(0))),or_(lt((Q(-1),Q(0),Q(1))),not_(map_planes(forbidden,along))))


def segment_proof(polygons,a,b,*,formula_expr,predicate_expr,prefix='real',work_limit=1000000,atom_limit=64):
    from .geometry_admission import segment_evidence
    evidence=segment_evidence(polygons,a,b,work_limit=work_limit)
    lines=[]
    if evidence['status']=='FREE':
        tree,stats=prove(segment_formula(polygons,a,b),work_limit=work_limit,atom_limit=atom_limit)
        lines += [f'def {prefix}_formula : PerfectPower.PlanarCertificates.Formula := {formula_expr}']
        defs,root,proof=tree_definitions(tree,formula=prefix+'_formula',prefix=prefix)
        lines+=defs
        lines += [f'theorem {prefix}_free : {predicate_expr} :=',
                  f'  PerfectPower.RealVisibility.segment_from_tree _ _ _ {root} {proof}']
        evidence['tree_statistics']=stats
    else:
        t=_q(evidence['parameter'])
        # predicate_expr is FreeSegment polygons a b. The caller supplies args separately.
        args=formula_expr.replace('PerfectPower.RealVisibility.segmentFormula ','',1)
        lines += [f'theorem {prefix}_hit : PerfectPower.RealVisibility.blockedFormula {args} {t} = true := by decide +kernel',
                  f'theorem {prefix}_blocked : ¬{predicate_expr} :=',
                  f'  PerfectPower.RealVisibility.blocked_segment _ _ _ {t} (by norm_num) (by norm_num) {prefix}_hit']
    return lines,evidence


def compile_real_segment(polygons,start,finish,*,namespace='RealSegment',work_limit=1000000,atom_limit=64):
    if not re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',namespace):raise ValueError('simple namespace required')
    polygons=[list(map(point,p)) for p in polygons];a,b=point(start),point(finish)
    # Source chains have explicit winding semantics; callers may additionally require simple polygons.
    lines=['import PerfectPower.RealVisibility','set_option maxRecDepth 100000','set_option maxHeartbeats 16000000',
      'open PerfectPower.PlanarCertificates',f'namespace {namespace}',
      f'def polygons : List (List (ℚ × ℚ)) := {_list(_list(map(_point,p)) for p in polygons)}',
      f'def start : ℚ × ℚ := {_point(a)}',f'def finish : ℚ × ℚ := {_point(b)}']
    args='polygons start finish'
    proof,evidence=segment_proof(polygons,a,b,formula_expr='PerfectPower.RealVisibility.segmentFormula '+args,
      predicate_expr='PerfectPower.RealVisibility.FreeSegment '+args,work_limit=work_limit,atom_limit=atom_limit)
    lines+=proof
    conclusion='real_free' if evidence['status']=='FREE' else 'real_blocked'
    lines += ['#print axioms '+conclusion,f'end {namespace}'];source='\n'.join(lines)+'\n'
    return {'schema':'pp-real-segment/1','evidence':evidence,
      'scope':'all real parameters of the actual source segment avoid explicit real winding interiors, or a rational blocked parameter proves failure',
      'proof':{'source_sha256':sha256(source.encode()).hexdigest(),'kernel_checked':False}},source


def compile_real_route(packet,certificate,*,work_limit=1000000,atom_limit=64):
    from .geometry_admission import compile_geometric_route_certificate
    old=compile_geometric_route_certificate(packet,certificate,work_limit=work_limit)
    source=old['source'].replace('import PerfectPower.GeometrySourceTransport','import PerfectPower.RealVisibility',1)
    source=source.replace('set_option maxRecDepth 10000','set_option maxRecDepth 100000').replace('set_option maxHeartbeats 4000000','set_option maxHeartbeats 16000000')
    polys=[list(map(point,p)) for p in packet['obstacles']];nodes=list(map(point,packet['vertices']));n=len(nodes)
    denominator=old['denominator']
    # Recover the retained ordered pairs from the existing source, not edge tuple assumptions.
    match=re.search(r'def admitted : List \(Nat × Nat\) := \[(.*?)\]',source)
    admitted={tuple(map(int,p)) for p in re.findall(r'\((\d+),(\d+)\)',match.group(1))}
    lines=['open PerfectPower.PlanarCertificates'];evidence={};budget=Budget(work_limit)
    s=packet['vertices'].index(packet['start'])
    args=f'originalObstacles (rationalVertex originalNodes {s}) (rationalVertex originalNodes {s})'
    safe,esafe=segment_proof(polys,nodes[s],nodes[s],formula_expr='PerfectPower.RealVisibility.segmentFormula '+args,
      predicate_expr='PerfectPower.RealVisibility.FreeSegment '+args,prefix='real_source',work_limit=budget.limit,atom_limit=atom_limit)
    if esafe['status']!='FREE':raise ValueError('route source lies in a forbidden winding interior')
    lines+=safe;evidence['source_stationary']=esafe
    budget.used+=esafe.get('tree_statistics',{}).get('work',esafe['work_used'])
    for u in range(n):
        for v in range(n):
            if u==v:continue
            prefix=f'real_{u}_{v}'
            args=f'originalObstacles (rationalVertex originalNodes {u}) (rationalVertex originalNodes {v})'
            proof,e=segment_proof(polys,nodes[u],nodes[v],formula_expr='PerfectPower.RealVisibility.segmentFormula '+args,
              predicate_expr='PerfectPower.RealVisibility.FreeSegment '+args,prefix=prefix,
              work_limit=budget.limit-budget.used,atom_limit=atom_limit)
            budget.used+=e.get('tree_statistics',{}).get('work',e['work_used'])
            evidence[f'{u},{v}']=e;lines+=proof
            if e['status']=='FREE':
                if (u,v) not in admitted:raise ValueError('missing real visibility edge')
                lines += [f'theorem {prefix}_pair : (({u},{v}) ∈ admitted) ↔ PerfectPower.RealVisibility.FreeSegment {args} :=',
                          f'  iff_of_true (by decide) {prefix}_free']
            else:
                if (u,v) in admitted:raise ValueError('invented real visibility edge')
                lines += [f'theorem {prefix}_pair : (({u},{v}) ∈ admitted) ↔ PerfectPower.RealVisibility.FreeSegment {args} :=',
                          f'  iff_of_false (by decide) {prefix}_blocked']
    lines += ['theorem real_complete : ∀ u v, u < originalNodes.length → v < originalNodes.length → u ≠ v →',
      '  ((u,v) ∈ admitted ↔ PerfectPower.RealVisibility.FreeSegment originalObstacles (rationalVertex originalNodes u) (rationalVertex originalNodes v)) := by',
      '  intro u v hu hv hne','  simp only [originalNodes,List.length_cons,List.length_nil] at hu hv',
      '  interval_cases u <;> interval_cases v']
    for u in range(n):
        for v in range(n):lines.append('  · omega' if u==v else f'  · exact real_{u}_{v}_pair')
    if packet['status']=='ROUTE':
        s=packet['vertices'].index(packet['start']);t=packet['vertices'].index(packet['end'])
        path=packet['path_indices']
        expression='(0 : ℚ)';walk=f'PerfectPower.RealVisibility.SourceWalk.nil {t}'
        for u,v in reversed(list(zip(path,path[1:]))):
            expression=f'(qweight (rationalVertex originalNodes {u}) (rationalVertex originalNodes {v})+{expression})'
            walk=f'PerfectPower.RealVisibility.SourceWalk.cons (u := {u}) (v := {v}) (by decide) (by decide) real_{u}_{v}_free ({walk})'
        lines += [f'def realWalkCost : ℚ := {expression}',
          f'theorem source_real_walk_cost : realWalkCost = {_q(packet["cost"])} := by decide +kernel',
          f'theorem retained_real_walk : PerfectPower.RealVisibility.SourceWalk originalObstacles originalNodes {s} {t} {_q(packet["cost"])} := by',
          '  rw [← source_real_walk_cost]',f'  exact {walk}',
          '#print axioms retained_real_walk']
        lines += [f'def realPotential (u : Nat) : ℚ := (potential u : ℚ)/{_q(denominator)}',
          f'theorem real_bounds_finite : ∀ u v : Fin {n}, (u.val,v.val) ∈ admitted →',
          '  realPotential v ≤ realPotential u+qweight (rationalVertex originalNodes u) (rationalVertex originalNodes v) := by decide +kernel',
          'theorem real_bounds : ∀ u v, u < originalNodes.length → v < originalNodes.length → u ≠ v →',
          '  PerfectPower.RealVisibility.FreeSegment originalObstacles (rationalVertex originalNodes u) (rationalVertex originalNodes v) →',
          '  realPotential v ≤ realPotential u+qweight (rationalVertex originalNodes u) (rationalVertex originalNodes v) := by',
          '  intro u v hu hv hne hf',f'  have hu\' : u < {n} := by simpa [originalNodes] using hu',
          f'  have hv\' : v < {n} := by simpa [originalNodes] using hv',
          '  exact real_bounds_finite ⟨u,hu\'⟩ ⟨v,hv\'⟩ ((real_complete u v hu hv hne).mpr hf)',
          f'theorem source_real_dual : {_q(packet["cost"])} = realPotential {t}-realPotential {s} := by decide +kernel',
          'theorem no_cheaper_real_walk {other : ℚ}',
          f'  (walk : PerfectPower.RealVisibility.SourceWalk originalObstacles originalNodes {s} {t} other) : {_q(packet["cost"])} ≤ other :=',
          '  PerfectPower.RealVisibility.source_optimal_walk originalObstacles originalNodes realPotential real_bounds source_real_dual walk',
          '#print axioms no_cheaper_real_walk']
    else:
        s=packet['vertices'].index(packet['start']);t=packet['vertices'].index(packet['end'])
        lines += [f'theorem real_closed_finite : ∀ u v : Fin {n}, (u.val,v.val) ∈ admitted → reachable u → reachable v := by decide',
          'theorem real_closed : ∀ u v, u < originalNodes.length → v < originalNodes.length → u ≠ v →',
          '  PerfectPower.RealVisibility.FreeSegment originalObstacles (rationalVertex originalNodes u) (rationalVertex originalNodes v) → reachable u → reachable v := by',
          '  intro u v hu hv hne hf hr',f'  have hu\' : u < {n} := by simpa [originalNodes] using hu',
          f'  have hv\' : v < {n} := by simpa [originalNodes] using hv',
          '  exact real_closed_finite ⟨u,hu\'⟩ ⟨v,hv\'⟩ ((real_complete u v hu hv hne).mpr hf) hr',
          f'theorem no_real_route : ∀ c, ¬PerfectPower.RealVisibility.SourceWalk originalObstacles originalNodes {s} {t} c :=',
          '  PerfectPower.RealVisibility.source_no_walk_outside originalObstacles originalNodes reachable real_closed source_inside target_outside',
          '#print axioms no_real_route']
    lines += ['#print axioms real_complete']
    tail=source.rindex('\nend ');source=source[:tail]+'\n'+'\n'.join(lines)+'\n'+source[tail:]
    return {'schema':'pp-real-source-graph/1','denominator':denominator,'pair_evidence':evidence,
      'scope':'source-derived finite graph is complete for whole real-parameter winding visibility; original-unit rational Manhattan optimality for every finite source walk including stationary steps; continuous arbitrary-bend global optimality not asserted',
      'proof':{'source_sha256':sha256(source.encode()).hexdigest(),'kernel_checked':False}},source


def compile_real_contact(a,b,c,d,*,namespace='RealContact',work_limit=1000000,atom_limit=64):
    """Certify existence or nonexistence of a real common point of closed segments.

    The producer's proper/touch/overlap classification is informative metadata;
    the Lean conclusion proves contact existence or universal disjointness only.
    """
    from .euclid_geometry import segment_intersection
    if not re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',namespace):raise ValueError('simple namespace required')
    a,b,c,d=map(point,(a,b,c,d));hit=segment_intersection(a,b,c,d)
    lines=['import PerfectPower.RealContact','set_option maxRecDepth 100000','set_option maxHeartbeats 16000000',
      'open PerfectPower.PlanarCertificates',f'namespace {namespace}']
    for name,pt in zip(('a','b','c','d'),(a,b,c,d)):lines.append(f'def {name} : ℚ × ℚ := {_point(pt)}')
    if hit['points']:
        witness=point(hit['points'][0]);stats=None
        lines += [f'def witness : ℚ × ℚ := {_point(witness)}',
          'theorem source_hit : (PerfectPower.RealContact.contactFormula a b c d).eval (fun f => PerfectPower.RealContact.rationalSign f witness) = true := by decide +kernel',
          'theorem source_contact : PerfectPower.RealContact.Contact a b c d :=',
          '  PerfectPower.RealContact.contact_from_hit a b c d witness source_hit','#print axioms source_contact']
    else:
        f=not_(and_(boundary(a,b),boundary(c,d)));tree,stats=prove(f,work_limit=work_limit,atom_limit=atom_limit)
        lines.append('def formula := PerfectPower.RealContact.disjointFormula a b c d')
        defs,root,proof=tree_definitions(tree);lines+=defs
        lines += ['theorem source_disjoint : ¬PerfectPower.RealContact.Contact a b c d :=',
          f'  PerfectPower.RealContact.disjoint_from_tree a b c d {root} {proof}','#print axioms source_disjoint']
    lines.append(f'end {namespace}');source='\n'.join(lines)+'\n'
    return {'schema':'pp-real-segment-contact/1','producer_intersection':hit,'tree_statistics':stats,
      'scope':'existence or nonexistence of a real common point of the actual closed segments; proper/touch/overlap classification is producer metadata',
      'proof':{'source_sha256':sha256(source.encode()).hexdigest(),'kernel_checked':False}},source
