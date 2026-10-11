"""Source-bound exact Euclidean transformation and polygon area proof emitters."""
from fractions import Fraction as Q
from hashlib import sha256
from math import lcm
import json
from .euclid_geometry import rational,point
from .belyaev_geometry import apply_isometry,check_triangulation,orientation,signed_area2


def _digest(packet):return sha256(json.dumps(packet,sort_keys=True,separators=(',',':')).encode()).hexdigest()


def compile_isometry(transform):
    apply_isometry(transform,[0,0])
    matrix=[[rational(v) for v in row] for row in transform['matrix']];shift=point(transform['translation'])
    denominator=lcm(*(v.denominator for row in matrix for v in row),*(v.denominator for v in shift))
    a,b,c,e=[int(v*denominator) for row in matrix for v in row];tx,ty=[int(v*denominator) for v in shift]
    sign=1 if a*e-b*c>0 else -1;digest=_digest(transform)
    source=f'''import PerfectPower.GeometryFoundations
namespace PerfectPower.CheckedGeometry.P{digest}
open PerfectPower.GeometryFoundations
theorem matrix_conditions :
    ({a} : Int)*({a})+({c})*({c})=({denominator})*({denominator}) ∧
    ({a})*({b})+({c})*({e})=0 ∧
    ({b})*({b})+({e})*({e})=({denominator})*({denominator}) := by decide
theorem determinant_condition : ({a} : Int)*({e})-({b})*({c})=({sign})*({denominator})*({denominator}) := by decide
def imageX (x y : Int) : Int := ({a})*x+({b})*y+({tx})
def imageY (x y : Int) : Int := ({c})*x+({e})*y+({ty})
theorem distance_all_inputs (x y u v : Int) :
    norm2 (imageX x y-imageX u v) (imageY x y-imageY u v)=
    ({denominator})*({denominator})*norm2 (x-u) (y-v) := by
  have hx : imageX x y-imageX u v=({a})*(x-u)+({b})*(y-v) := by
    simp [imageX,Int.mul_sub]; omega
  have hy : imageY x y-imageY u v=({c})*(x-u)+({e})*(y-v) := by
    simp [imageY,Int.mul_sub]; omega
  rw [hx,hy]
  exact orthogonal_scaled_norm ({a}) ({b}) ({c}) ({e}) ({denominator}) matrix_conditions.1 matrix_conditions.2.1 matrix_conditions.2.2 (x-u) (y-v)
theorem orientation_all_vectors (x y u v : Int) :
    (({a})*x+({b})*y)*(({c})*u+({e})*v)-(({c})*x+({e})*y)*(({a})*u+({b})*v)=
    (({sign})*({denominator})*({denominator}))*(x*v-y*u) := by
  rw [matrix_determinant,determinant_condition]
#print axioms distance_all_inputs
#print axioms orientation_all_vectors
end PerfectPower.CheckedGeometry.P{digest}
'''
    return {'schema':'pp-source-bound-rational-isometry/1','transform':transform,'denominator':denominator,
            'integer_matrix':[[a,b],[c,e]],'integer_translation':[tx,ty],'source':source,
            'source_sha256':sha256(source.encode()).hexdigest(),'specification_sha256':digest,
            'kernel_checked':False,'scope':'squared-distance and determinant scaling for every integer coordinate pair/vector, with source rational denominators cleared'}


def compile_triangulation_area(packet):
    check_triangulation(packet);vertices=[point(v) for v in packet['vertices']]
    triangles=[[point(v) for v in t] for t in packet['triangles']]
    denominator=lcm(*(v.denominator for p in vertices for v in p))
    scaled=lambda p:tuple(int(v*denominator) for v in p)
    area2=abs(signed_area2([scaled(p) for p in vertices]))
    determinants=[int(orientation(*[scaled(p) for p in t])) for t in triangles]
    digest=_digest(packet);terms='+'.join(f'({d} : Int)' for d in determinants)
    claims=[]
    for i,(triangle,d) in enumerate(zip(triangles,determinants)):
        (ax,ay),(bx,by),(cx,cy)=[scaled(p) for p in triangle]
        expression=f'(({bx} : Int)-({ax}))*(({cy})-({ay}))-(({by})-({ay}))*(({cx})-({ax}))'
        claims.append(f'theorem triangle_{i}_determinant : {expression}=({d}) := by decide')
        claims.append(f'theorem triangle_{i}_positive : (0 : Int)<({expression}) := by decide')
    claims='\n'.join(claims)
    original=[scaled(p) for p in vertices]
    original_terms='+'.join(f'(({a[0]} : Int)*({b[1]})-({a[1]})*({b[0]}))' for a,b in zip(original,original[1:]+original[:1]))
    source=f'''import PerfectPower.GeometryFoundations
namespace PerfectPower.CheckedGeometry.Area{digest}
{claims}
theorem source_polygon_area : Int.natAbs ({original_terms})=({area2}) := by decide
theorem area_conservation : {terms}=({area2}) := by decide
#print axioms area_conservation
end PerfectPower.CheckedGeometry.Area{digest}
'''
    return {'schema':'pp-source-bound-triangle-area/1','denominator':denominator,
            'scaled_vertices':[list(scaled(p)) for p in vertices],
            'scaled_triangles':[[list(scaled(p)) for p in t] for t in triangles],
            'source':source,'source_sha256':sha256(source.encode()).hexdigest(),
            'specification_sha256':digest,'kernel_checked':False,
            'scope':'retained positive triangle areas and exact total area; polygon coverage and nonoverlap remain tested Python'}
