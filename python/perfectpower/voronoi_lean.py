"""Export complete explicit witness data into the native Lean packet checker.

Derived barycentric vertices/areas are reconstructed natively from addresses.
The source packet is validated before export; Lean rechecks the exported data.
"""
from fractions import Fraction as Q
from .voronoi_certificate import verify
from .box_lean import rational


def array(xs,render=str):return '['+', '.join(render(x) for x in xs)+']'
def triple(xs):return '('+', '.join(str(x) for x in xs)+')'
def qlist(xs):return array(xs,lambda q:rational(q,'ℚ'))


def emit(name,mesh,packet):
    if not verify(mesh,packet):raise ValueError('valid witness packet required')
    signs=mesh.get('face_orientation_signs',[1]*len(mesh['triangles']))
    edges=array(mesh['edge_lengths'],lambda e:f'({e[0]}, {e[1]}, {rational(Q(str(e[2])),"ℚ")})')
    fields=array(packet['fields'],qlist)
    paths=array(packet['paths'],lambda rows:array(rows,lambda p:array(p)))
    leaves=[]
    for leaf in packet['pieces']:
        winner='none' if leaf['site'] is None else 'some '+str(leaf['site'])
        leaves.append('{face := '+str(leaf['face'])+', address := '+array(leaf['address'])+
                      ', winner := '+winner+', radius := '+rational(leaf['radius_upper'],'ℚ')+
                      ', upper := '+qlist(leaf['center_upper'])+', lower := '+qlist(leaf['center_lower'])+'}')
    return f'''def {name}_mesh : Mesh := {{vertices := {mesh['vertices']}, faces := {array(mesh['triangles'],triple)}, signs := {array(signs)}, edges := {edges}}}
def {name}_packet : Packet := {{sites := {array(packet['sites'])}, fields := {fields}, paths := {paths}, depth := {packet['depth']}, leaves := [{', '.join(leaves)}]}}
theorem {name}_accepted : accepts {name}_mesh {name}_packet=true := by decide +kernel
#print axioms {name}_accepted
'''
