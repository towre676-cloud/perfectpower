"""Exact cap incidence and canonical five-letter transport; no CKM inputs."""
from pathlib import Path
from collections import Counter, deque
import random
import json
import numpy as np
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'receipts/m22_interactions'
ID = bytes(range(22))
TAIL = bytes(range(22, 256))


def mul(p, q):
    return q.translate(p + TAIL)


def inv(p):
    a = bytearray(22)
    for i, j in enumerate(p):
        a[j] = i
    return bytes(a)


def power(p, n):
    a = ID
    while n:
        if n & 1:
            a = mul(a, p)
        p = mul(p, p)
        n //= 2
    return a


def order(p):
    n, a = 1, p
    while a != ID:
        a = mul(a, p)
        n += 1
    return n


def perm(cycles):
    p = bytearray(ID)
    for c in cycles:
        for i, j in zip(c, c[1:] + c[:1]):
            p[i-1] = j-1
    return bytes(p)


A = perm([[1,13],[2,8],[3,16],[4,12],[6,22],[7,17],[9,10],[11,14]])
B = perm([[1,22,3,21],[2,18,4,13],[5,12],[6,11,7,15],[8,14,20,10],[17,19]])


def closure(gens, identity=ID, product=mul):
    seen = {identity}
    queue = [identity]
    for x in queue:
        for g in gens:
            y = product(g, x)
            if y not in seen:
                seen.add(y)
                queue.append(y)
    return sorted(seen)


def conjugate(g, p):
    return mul(mul(g, p), inv(g))


def cosets(h):
    reps, lookup = [ID], {x: 0 for x in h}
    for g in reps:
        for s in (A, B):
            sg = mul(s, g)
            if sg not in lookup:
                i = len(reps)
                reps.append(sg)
                lookup.update((mul(sg, x), i) for x in h)
    assert len(lookup) == 443520
    return reps, lookup


def orbit_profile(reps, lookup, gens):
    unseen = set(range(len(reps)))
    sizes = []
    while unseen:
        start = min(unseen)
        queue = [start]
        unseen.remove(start)
        for i in queue:
            for h in gens:
                j = lookup[mul(h, reps[i])]
                if j in unseen:
                    unseen.remove(j)
                    queue.append(j)
        sizes.append(len(queue))
    return Counter(sizes)


def choose_cap():
    rng = random.Random(220526)
    target = Counter({60:100,30:42,20:4,15:2,10:1,6:1,5:1,1:1})
    for attempt in range(1000):
        g = ID
        for _ in range(22):
            g = mul(rng.choice([A,B,inv(B)]), g)
        o = order(g)
        if o % 3:
            continue
        v = power(g, o//3)
        if order(mul(A,v)) != 5:
            continue
        h = closure([A,v])
        assert len(h) == 60
        reps, lookup = cosets(h)
        profile = orbit_profile(reps, lookup, [A,v])
        print('cap candidate', attempt, 'profile', dict(sorted(profile.items())), flush=True)
        if profile == target:
            return h, reps, lookup, v
    raise RuntimeError('No matching cap class found')


def natural_letters(h):
    twos = [x for x in h if order(x) == 2]
    kleins = set()
    for x in twos:
        for y in twos:
            if x != y and mul(x,y) == mul(y,x):
                kleins.add(tuple(sorted([ID,x,y,mul(x,y)])))
    assert len(kleins) == 5
    a4s = []
    for k in sorted(kleins):
        a4 = frozenset(g for g in h if {conjugate(g,x) for x in k} == set(k))
        assert len(a4) == 12
        a4s.append(a4)
    return a4s


def small_mul(p,q):
    return tuple(p[j] for j in q)


def small_inv(p):
    return tuple(p.index(i) for i in range(len(p)))


def parity(p):
    return (-1)**sum(p[i]>p[j] for i in range(len(p)) for j in range(i+1,len(p)))


def connection(h, reps, lookup):
    r = next(x for x in h if order(x) == 5)
    rr = power(r,2)
    t = next(x for x in sorted(lookup) if mul(x,r) == mul(rr,x))
    assert order(t) == 4 and t not in h
    base_neighbors = sorted({lookup[mul(x,t)] for x in h})
    assert len(base_neighbors) == 6
    letters = natural_letters(h)
    hset = set(h)
    label = {a:i for i,a in enumerate(letters)}
    rho = {g:tuple(label[frozenset(conjugate(g,x) for x in a)] for a in letters) for g in h}
    assert all(parity(x) == 1 for x in rho.values())
    base_transport = {}
    for j in base_neighbors:
        g = reps[j]
        local = [frozenset(conjugate(g,x) for x in a) for a in letters]
        d5 = hset & {conjugate(g,x) for x in h}
        assert len(d5) == 10
        source = [next(iter((set(a)&d5)-{ID})) for a in letters]
        dest = [next(iter((set(a)&d5)-{ID})) for a in local]
        assert all(len(set(a)&d5) == 2 for a in letters+local)
        assert len(set(source)) == len(set(dest)) == 5
        base_transport[j] = tuple(dest.index(x) for x in source)
    seen, queue, edges = {0}, [0], {}
    for i in queue:
        for j in base_neighbors:
            gj = mul(reps[i], reps[j])
            w = lookup[gj]
            cocycle = mul(inv(reps[w]), gj)
            assert cocycle in hset
            transport = small_mul(rho[cocycle], base_transport[j])
            edges[i,w] = transport
            if w not in seen:
                seen.add(w)
                queue.append(w)
    assert len(queue) == 42 and len(edges) == 252
    for (v,w), p in edges.items():
        assert edges[w,v] == small_inv(p)
    parallel = {0:tuple(range(5))}
    parents = {0:None}
    bfs = [0]
    holonomies = []
    for v in bfs:
        for w in sorted(x for a,x in edges if a == v):
            p = edges[v,w]
            if w not in parallel:
                parallel[w] = small_mul(p,parallel[v])
                parents[w] = v
                bfs.append(w)
            else:
                holonomies.append(small_mul(small_inv(parallel[w]),small_mul(p,parallel[v])))
    holonomy = closure(holonomies,tuple(range(5)),small_mul)
    print('transport component',len(queue),'holonomy',len(holonomy), 'edge parity',Counter(map(parity,edges.values())),flush=True)
    return queue, edges, holonomy, base_neighbors, t, letters, rho


def wedge(m):
    pairs = [(i,j) for i in range(4) for j in range(i+1,4)]
    return sp.Matrix([[m[i,k]*m[j,l]-m[i,l]*m[j,k] for k,l in pairs] for i,j in pairs])


def fiber_certificate(holonomy):
    g = sp.eye(4)+sp.ones(4)
    g2 = wedge(g)
    pairs = [(i,j) for i in range(4) for j in range(i+1,4)]
    e = sp.zeros(6)
    for a,(i,j) in enumerate(pairs):
        for b,(k,l) in enumerate(pairs):
            if len({i,j,k,l}) == 4:
                e[a,b] = parity((i,j,k,l))
    s = e*g2/sp.sqrt(5)
    assert s*s == sp.eye(6) and s.T*g2 == g2*s
    matrices = []
    for p in holonomy:
        m = sp.Matrix([[int(p[j]==i)-int(p[4]==i) for j in range(4)] for i in range(4)])
        m2 = wedge(m)
        assert m.T*g*m == g
        assert s*m2 == parity(p)*m2*s
        matrices.append(m2)
    def centralizer_dim(ms):
        # Column-vectorized commutator; full exact rank over Q.
        stacked = sp.Matrix.vstack(*[sp.kronecker_product(sp.eye(6),m)-sp.kronecker_product(m.T,sp.eye(6)) for m in ms])
        return 36-stacked.rank()
    # All elements can be restricted to a small generating set without changing invariants.
    odd = next(p for p in holonomy if parity(p)==-1)
    even = next(p for p in holonomy if parity(p)==1 and order5(p)==5)
    three = next(p for p in holonomy if parity(p)==1 and order5(p)==3 and len(closure([even,p],tuple(range(5)),small_mul))==60)
    index = {p:i for i,p in enumerate(holonomy)}
    assert len(closure([odd,even,three],tuple(range(5)),small_mul))==len(holonomy)
    full = centralizer_dim([matrices[index[x]] for x in (odd,even,three)])
    orient = centralizer_dim([matrices[index[x]] for x in (even,three)])
    assert full == 1 and orient == 2
    return {'hyperplane_metric':list(map(list,g.tolist())), 'hodge_star_times_sqrt5':(e*g2).tolist(),
            'hodge_star_square_identity':True, 'projector_ranks':[3,3],
            'full_holonomy_commutant_dimension':full,'even_holonomy_commutant_dimension':orient,
            'edge_odd_transport_exchanges_triplets':True}


def d5_intertwiners(h,reps,neighbors,rho,fiber):
    g=reps[neighbors[0]]
    d5=set(h)&{conjugate(g,x) for x in h}
    omega=sp.Matrix(fiber['hodge_star_times_sqrt5'])/sp.sqrt(5)
    def character(p,sign):
        m=sp.Matrix([[int(p[j]==i)-int(p[4]==i) for j in range(4)] for i in range(4)])
        m2=wedge(m)
        return sp.simplify((m2.trace()+sign*(omega*m2).trace())/2)
    rows=[]
    same=0;cross=0
    for d in sorted(d5):
        dest=conjugate(inv(g),d)
        cv=character(rho[d],1)
        cw=character(rho[dest],1)
        co=character(rho[dest],-1)
        same+=cv*cw;cross+=cv*co
        rows.append({'order':order(d),'source_plus':str(cv),'target_plus':str(cw),'target_minus':str(co)})
    same=sp.simplify(same/10);cross=sp.simplify(cross/10)
    assert (same,cross)==(1,2)
    return {'edge_stabilizer_order':10,'edge_stabilizer':'D5',
        'same_branch_intertwiner_dimension':int(same),'opposite_branch_intertwiner_dimension':int(cross),
        'same_branch_maximum_rank':1,'opposite_branch_independent_channels':['one-dimensional axis','two-dimensional plane'],
        'characters':rows,'scope':'Symmetry allows independent axis and plane couplings; incidence matching picks one particular isometry.'}


def order5(p):
    i = tuple(range(5)); a=p; n=1
    while a!=i:
        a=small_mul(a,p);n+=1
    return n


def orientation_cover(queue,edges):
    root=(0,0)
    parallel={root:tuple(range(5))};bfs=[root];holonomies=[]
    for v,sheet in bfs:
        for w in sorted(b for a,b in edges if a==v):
            dest=(w,1-sheet);p=edges[v,w]
            if dest not in parallel:
                parallel[dest]=small_mul(p,parallel[v,sheet]);bfs.append(dest)
            else:
                holonomies.append(small_mul(small_inv(parallel[dest]),small_mul(p,parallel[v,sheet])))
    holonomy=closure(holonomies,tuple(range(5)),small_mul)
    assert len(bfs)==84 and len(holonomy)==60 and all(parity(p)==1 for p in holonomy)
    # A shortest odd closed walk gives an explicit obstruction on the base.
    parents={root:None};search=[root];goal=(0,1)
    for v,sheet in search:
        if (v,sheet)==goal:
            break
        for w in sorted(b for a,b in edges if a==v):
            dest=(w,1-sheet)
            if dest not in parents:
                parents[dest]=(v,sheet);search.append(dest)
    path=[];cur=goal
    while cur is not None:
        path.append(cur[0]);cur=parents[cur]
    path.reverse();p=tuple(range(5))
    for a,b in zip(path,path[1:]):
        p=small_mul(edges[a,b],p)
    assert len(path)==6 and parity(p)==-1
    return {'vertex_count':84,'connected':True,'holonomy_group':'A5','holonomy_order':60,
        'parallel_chirality_operator':'J_(v,sheet) = (-1)^sheet Omega_v',
        'deck_transformation':'sheet -> 1-sheet exchanges the two rank-three sectors',
        'base_odd_cycle_vertices':path,'base_odd_cycle_holonomy':list(p),
        'base_odd_cycle_holonomy_parity':parity(p)}


def component_stabilizers(queue,edges,h,reps,lookup):
    unseen=set(queue);blocks=[]
    while unseen:
        root=min(unseen);dist={root:0};bfs=[root]
        for v in bfs:
            for w in (b for a,b in edges if a==v):
                if w not in dist:
                    dist[w]=dist[v]+1;bfs.append(w)
        block=frozenset([root]+[v for v,d in dist.items() if d==3])
        assert len(block)==6 and block<=unseen
        blocks.append(block);unseen-=block
    assert len(blocks)==7
    blockindex={v:i for i,b in enumerate(blocks) for v in b}
    subgroup={mul(reps[v],x) for v in queue for x in h}
    assert len(subgroup)==2520
    images=set()
    for g in subgroup:
        action=tuple(blockindex[lookup[mul(g,reps[min(b)])]] for b in blocks)
        assert len(set(action))==7 and parity(action)==1
        for b in blocks:
            assert {blockindex[lookup[mul(g,reps[v])]] for v in b}=={action[blockindex[min(b)]]}
        images.add(action)
    assert len(images)==2520
    baseblock=next(b for b in blocks if 0 in b)
    a6={mul(reps[v],x) for v in baseblock for x in h}
    assert len(a6)==360
    six=sorted(baseblock);sixindex={v:i for i,v in enumerate(six)};siximages=set()
    for g in a6:
        action=tuple(sixindex[lookup[mul(g,reps[v])]] for v in six)
        assert len(set(action))==6 and parity(action)==1
        siximages.add(action)
    assert len(siximages)==360
    return {'component_stabilizer':'A7','component_stabilizer_order':2520,
        'faithful_even_seven_letter_action_size':len(images),'antipodal_blocks':[sorted(b) for b in blocks],
        'antipodal_block_stabilizer':'A6','antipodal_block_stabilizer_order':360,
        'faithful_even_six_letter_action_size':len(siximages),'A5_cap_index_in_A6':6,
        'scope':'Ordinary A6 is established inside this cap geometry; the specific restriction of a central M22 cover is not assumed.'}


def main():
    OUT.mkdir(parents=True,exist_ok=True)
    assert (order(A),order(B),order(mul(A,B))) == (2,4,11)
    h,reps,lookup,v = choose_cap()
    queue,edges,holonomy,neighbors,t,letters,rho = connection(h,reps,lookup)
    fiber = fiber_certificate(holonomy)
    cover = orientation_cover(queue,edges)
    intertwiners=d5_intertwiners(h,reps,neighbors,rho,fiber)
    stabilizers=component_stabilizers(queue,edges,h,reps,lookup)
    distance = {0:0}; bfs=[0]
    for a in bfs:
        for b in sorted(w for x,w in edges if x==a):
            if b not in distance:
                distance[b]=distance[a]+1;bfs.append(b)
    intersection = {d:set() for d in set(distance.values())}
    for a in bfs:
        counts=Counter(distance[b]-distance[a] for x,b in edges if x==a)
        intersection[distance[a]].add(tuple(counts[k] for k in (-1,0,1)))
    assert all(len(x)==1 for x in intersection.values())
    assert [sum(d==i for d in distance.values()) for i in range(4)] == [1,6,30,5]
    data = {'sources':{'atlas_generators':'https://brauer.maths.qmul.ac.uk/Atlas/spor/M22/','permutation_convention':'p composed with q; zero based'},
        'group_order':len(lookup),'cap_order':len(h),'cap_count':len(reps),'cap_generators':[list(A),list(v)],
        'cap_subdegrees':dict(sorted(orbit_profile(reps,lookup,[A,v]).items())),
        'normalizer_c5_nonresidue_element':list(t),'component_vertices':sorted(queue),
        'component_count':len(reps)//len(queue),'distance_layers':[1,6,30,5],
        'intersection_counts_previous_same_next':{d:list(next(iter(x))) for d,x in intersection.items()},
        'transport_edges':[{'source':a,'target':b,'permutation':list(p),'parity':parity(p)} for (a,b),p in sorted(edges.items())],
        'holonomy_order':len(holonomy),'holonomy_group':'S5' if len(holonomy)==120 else 'unclassified',
        'holonomy_parities':dict(sorted(Counter(map(parity,holonomy)).items())), 'fiber':fiber,'orientation_cover':cover,'edge_intertwiners':intertwiners,'stabilizers':stabilizers,
        'physics_scope':'Canonical incidence transport forces both local golden triplets; no CKM angle or coefficient is used or derived.'}
    (OUT/'cap_transport.json').write_text(json.dumps(data,indent=2,sort_keys=True,default=int)+'\n')
    # Exact permutations provide independently usable coset representatives.
    np.savez_compressed(OUT/'cap_permutations.npz',representatives=np.array([list(x) for x in reps],dtype=np.uint8),cap=np.array([list(x) for x in h],dtype=np.uint8))
    print(json.dumps({'holonomy':len(holonomy),'fiber':fiber},default=str),flush=True)


if __name__=='__main__':
    main()
