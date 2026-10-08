"""Recompute the complete sextic stabilizer from its exact line covariant.

No published sextic automorphism bound is used. The complete graph search
uses nauty; all projective realizability tests use the exact coefficient
field. Singular verifies the original-generator identities and the full
45-line factorization of an intrinsically constructed covariant.
"""
from pathlib import Path
from collections import Counter
from functools import lru_cache
from itertools import combinations
import argparse
import hashlib
import json
import math
import shutil
import subprocess
import sympy as s
from sympy.polys.matrices import DomainMatrix
from develop_valentiner_frames import group_closure, generators, mul, dagger, IDENTITY
from develop_valentiner_diagonal_vacua import tensor_data, X
from develop_valentiner_exact_vacuum_curve import singular_expression

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'receipts/m22_interactions'
STEM='valentiner_direct_stabilizer'


def normalize(v):
    pivot=next(c for c in v if c)
    return tuple(c/pivot for c in v)


def determinant(a,b,c):
    return (a[0]*(b[1]*c[2]-b[2]*c[1])-a[1]*(b[0]*c[2]-b[2]*c[0])
            +a[2]*(b[0]*c[1]-b[1]*c[0]))


@lru_cache(None)
def exact_geometry():
    F,tensor,_=tensor_data()
    omega=(-1+s.I*s.sqrt(3))/2
    G=group_closure(generators())[0]
    assert len(G)==1080
    @lru_cache(None)
    def coefficient(t,den):
        a,b,c,d=t
        return F.from_sympy((a+b*s.sqrt(5)+(c+d*s.sqrt(5))*omega)/den)
    def matrix(g):
        den,entries=g
        return [[coefficient(entries[3*i+j],den) for j in range(3)] for i in range(3)]
    source_matrices=[]
    for g in generators():
        assert mul(g,dagger(g))==IDENTITY
        M=matrix(g)
        assert determinant(*M)==F.one
        source_matrices.append(M)
    involutions=[g for g in G if g!=IDENTITY and mul(g,g)==IDENTITY]
    assert len(involutions)==45
    lines=[]
    for g in involutions:
        M=matrix(g)
        rows=[[M[i][j]+F.convert(int(i==j)) for j in range(3)] for i in range(3)]
        row=normalize(next(v for v in rows if any(v)))
        assert all(not any(v) or normalize(v)==row for v in rows)
        lines.append(row)
    assert len(set(lines))==45
    points={}
    for i,v in enumerate(lines):
        for j,u in enumerate(lines[:i]):
            point=normalize((v[1]*u[2]-v[2]*u[1],v[2]*u[0]-v[0]*u[2],v[0]*u[1]-v[1]*u[0]))
            points.setdefault(point,set()).update((i,j))
    assert Counter(map(len,points.values()))=={3:120,4:45,5:36}
    # Also check every claimed/nonclaimed incidence against the coordinates.
    for point,ids in points.items():
        assert {i for i,v in enumerate(lines) if sum((a*b for a,b in zip(point,v)),F.zero)==F.zero}==ids
    polynomial=s.Poly.from_dict({m:c*F.convert(math.factorial(6)//math.prod(math.factorial(n) for n in m))
                                 for m,c in tensor.items()},X,domain=F)
    return F,polynomial,lines,points,source_matrices


def permutation_closure(gens,n):
    group=[tuple(range(n))];seen=set(group)
    for g in group:
        for h in gens:
            k=tuple(h[g[i]] for i in range(n))
            if k not in seen:seen.add(k);group.append(k)
    return group


def incidence_automorphisms(lines,points):
    import pynauty
    adj={i:set() for i in range(len(lines)+len(points))}
    for n,ids in enumerate(points.values(),len(lines)):
        for i in ids:adj[i].add(n);adj[n].add(i)
    colors=[set(range(len(lines)))]+[{n for n in range(len(lines),len(adj)) if len(adj[n])==k} for k in (3,4,5)]
    graph=pynauty.Graph(len(adj),adjacency_dict=adj,vertex_coloring=colors)
    result=pynauty.autgrp(graph)
    full_gens=result[0]
    for g in full_gens:
        assert set(g)==set(adj)
        assert all({g[j] for j in adj[i]}==adj[g[i]] for i in adj)
        assert all({g[j] for j in color}==color for color in colors)
    group=permutation_closure([tuple(g[:45]) for g in full_gens],45)
    assert result[1]*(10**result[2])==len(group)==1440
    return group,full_gens,pynauty.__version__


def filter_projectivities(F,lines,group):
    def frame(ids):
        a,b,c,d=[lines[i] for i in ids]
        delta=determinant(a,b,c)
        if not delta:return None
        t=(determinant(d,b,c)/delta,determinant(a,d,c)/delta,determinant(a,b,d)/delta)
        if not all(t):return None
        return [[a[i]*t[0],b[i]*t[1],c[i]*t[2]] for i in range(3)]
    ids=next(ids for ids in combinations(range(45),4) if frame(ids))
    inverse=DomainMatrix(frame(ids),(3,3),F).inv().to_list()
    coordinates=[tuple(sum((inverse[i][j]*v[j] for j in range(3)),F.zero) for i in range(3)) for v in lines]
    accepted=[];witnesses=[]
    for perm in group:
        target=frame(tuple(perm[i] for i in ids))
        assert target
        failed=-1
        for i,v in enumerate(coordinates):
            image=tuple(sum((target[j][k]*v[k] for k in range(3)),F.zero) for j in range(3))
            if normalize(image)!=lines[perm[i]]:
                failed=i;break
        witnesses.append(failed)
        if failed==-1:accepted.append(perm)
    assert len(accepted)==360
    # Independently close the known matrix subgroup on the same dual lines.
    lookup={v:i for i,v in enumerate(lines)}
    known_gens=[]
    for M in exact_geometry()[4]:
        inverse=DomainMatrix(M,(3,3),F).inv().to_list()
        perm=tuple(lookup[normalize(tuple(sum((v[j]*inverse[j][k] for j in range(3)),F.zero)
                                         for k in range(3)))] for v in lines)
        known_gens.append(perm)
    known=permutation_closure(known_gens,45)
    assert set(known)==set(accepted) and len(known)==360
    return list(ids),witnesses,known_gens


def covariant_script():
    F,polynomial,lines,_,matrices=exact_geometry()
    script='ring r=(0,a),(x,y,z),dp;\nminpoly=a^4-4*a^2+64;\npoly f='+singular_expression(polynomial)+';\n'
    for n,M in enumerate(matrices):
        images=[]
        for row in M:
            poly=s.Poly.from_dict({tuple(int(i==j) for j in range(3)):c for i,c in enumerate(row) if c},X,domain=F)
            images.append(singular_expression(poly))
        script+='map g'+str(n)+'=r,'+','.join(images)+';\npoly fg'+str(n)+'=g'+str(n)+'(f);\nprint("GENERATOR_'+str(n)+'="+string(fg'+str(n)+'==f));\n'
    script+=r'''
matrix H[3][3];int i;int j;
for(i=1;i<=3;i++){for(j=1;j<=3;j++){H[i,j]=diff(diff(f,var(i)),var(j));}}
poly h=det(H);
matrix B[4][4];
for(i=1;i<=3;i++){
  B[1,i+1]=diff(h,var(i));B[i+1,1]=diff(h,var(i));
  for(j=1;j<=3;j++){B[i+1,j+1]=H[i,j];}
}
poly b=det(B);
matrix J[3][3];
for(i=1;i<=3;i++){J[1,i]=diff(f,var(i));J[2,i]=diff(h,var(i));J[3,i]=diff(b,var(i));}
poly c=det(J);
print("COVARIANT_DEG="+string(deg(c)));
print("COVARIANT_TERMS="+string(size(c)));
poly L=1;
'''
    for line in lines:
        poly=s.Poly.from_dict({tuple(int(i==j) for j in range(3)):v for i,v in enumerate(line) if v},X,domain=F)
        script+='L=L*('+singular_expression(poly)+');\n'
    return script+r'''
number scalar=leadcoef(c)/leadcoef(L);
print("PRODUCT_DEG="+string(deg(L)));
print("FACTOR_IDENTITY="+string(c==scalar*L));
print("NONZERO_SCALAR="+string(scalar!=0));
print("COVARIANT_COMPLETE");quit;
'''


def prove(binary='Singular'):
    F,_,lines,points,_=exact_geometry()
    group,gens,version=incidence_automorphisms(lines,points)
    frame,witnesses,known_gens=filter_projectivities(F,lines,group)
    script=covariant_script();OUT.mkdir(parents=True,exist_ok=True)
    path=OUT/(STEM+'.sing');path.write_text(script)
    result=subprocess.run([binary,'-q',str(path)],capture_output=True,text=True,timeout=60,check=True)
    log=result.stdout.replace('\r\n','\n')
    assert '?' not in log and 'COVARIANT_COMPLETE' in log,log
    for marker in ('COVARIANT_DEG=45','PRODUCT_DEG=45','FACTOR_IDENTITY=1','NONZERO_SCALAR=1',
                   'GENERATOR_0=1','GENERATOR_1=1','GENERATOR_2=1','GENERATOR_3=1'):
        assert marker in log,marker
    (OUT/(STEM+'.log')).write_text(log)
    data={
        'coefficient_field':'Q(sqrt(5),sqrt(-3))','characteristic':0,
        'known_matrix_group_order':1080,'involutions':45,
        'lines':[[str(F.to_sympy(c)) for c in v] for v in lines],
        'point_incidence_sets':[sorted(ids) for ids in points.values()],
        'intersection_multiplicities':{'3':120,'4':45,'5':36},
        'colored_incidence_graph_vertices':246,
        'complete_incidence_group_order':1440,'graph_generators':gens,
        'graph_engine':'pynauty '+version,'projective_frame_indices':frame,
        'projectivity_failure_line_by_permutation_index':witnesses,
        'projectivity_count':360,'rejected_incidence_permutations':1080,
        'known_projective_generators':known_gens,'accepted_set_equals_known_projective_group':True,
        'original_sextic_generator_checks':4,'intrinsic_covariant_degree':45,
        'full_45_line_factorization_verified':True,
        'full_projective_sextic_stabilizer_order':360,
        'determinant_one_scalar_kernel_order':3,
        'full_SU3_tensor_stabilizer_order':1080,'selected_global_minima':1080,
        'classification_theorem_used':False,
        'scope':'Complete stabilizer of the original sextic and its conjugate; selected Gram-completed frames. No quark or CP selection is implied.',
        'script_sha256':hashlib.sha256(script.encode()).hexdigest(),
        'log_sha256':hashlib.sha256(log.encode()).hexdigest(),
    }
    (OUT/(STEM+'.json')).write_text(json.dumps(data,indent=2)+'\n')
    return data


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--singular',default=shutil.which('Singular') or 'Singular')
    args=parser.parse_args();data=prove(args.singular)
    print(json.dumps({k:data[k] for k in ('complete_incidence_group_order','projectivity_count',
          'full_SU3_tensor_stabilizer_order','full_45_line_factorization_verified','classification_theorem_used')},indent=2))
