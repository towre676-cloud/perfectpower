"""Exact all-orders block vacuum curve, in characteristic zero.

SymPy reconstructs the restriction from the original nine-variable tensor.
Singular computes a global standard basis, verifies its lift, and checks
I:q=I.  The latter excludes a fat isolated point at the nominated vacuum.
No finite Taylor truncation or modular reconstruction enters the proof.
"""
from pathlib import Path
import argparse
import hashlib
import json
import shutil
import subprocess
import sympy as s
from develop_valentiner_frame_selection import full_sextic_polynomial

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'receipts/m22_interactions'
STEM = 'valentiner_exact_vacuum_curve'


def block_polynomials():
    P = full_sextic_polynomial()
    D = s.Poly(s.Matrix(3, 3, P.gens).det(), P.gens, domain=P.domain)
    W = P - 5*D
    keep, omitted = [0, 4, 8, 1, 3], [2, 5, 6, 7]
    variables = s.symbols('x y z p q')
    def restrict(poly):
        terms = {tuple(m[i] for i in keep): c
                 for m, c in poly.rep.to_dict().items()
                 if not any(m[i] for i in omitted)}
        return s.Poly.from_dict(terms, variables, domain=P.domain)
    assert all(restrict(W.diff(P.gens[i])).is_zero for i in omitted)
    return restrict(W), restrict(D)


def singular_expression(poly):
    """Serialize ANP coefficients in a=sqrt(5)+sqrt(-3), safely."""
    terms = []
    for m, c in poly.rep.to_dict().items():
        coefficients = c.to_list()
        coefficient = '+'.join('('+str(r)+')'+
            ('*a^'+str(len(coefficients)-i-1) if len(coefficients)-i-1 else '')
            for i, r in enumerate(coefficients) if r)
        monomial = '*'.join(str(poly.gens[i])+'^'+str(n)
                            for i, n in enumerate(m) if n)
        terms.append('('+coefficient+')'+('*'+monomial if monomial else ''))
    return '+'.join(terms)


def certificate_script():
    W, D = block_polynomials()
    return ('ring r=(0,a),(x,y,z,p,q),dp;\n'
            'minpoly=a^4-4*a^2+64;\n'
            'poly W='+singular_expression(W)+';\n'
            'poly D='+singular_expression(D)+';\n'+r'''
ideal I=diff(W,x),diff(W,y),diff(W,z),diff(W,p),diff(W,q),D-1;
short=0;
matrix T; ideal G=liftstd(I,T);
print("DIM="+string(dim(G)));
print("BASIS_SIZE="+string(size(G)));
print("LIFT_IDENTITY="+string(matrix(I)*T==matrix(G)));
ideal R=reduce(I,G);int good=1;int j;
for(j=1;j<=size(R);j++){if(R[j]!=0){good=0;}}
print("ORIGINAL_REMAINDERS_ZERO="+string(good));
ideal Q=quotient(G,ideal(q));R=reduce(Q,G);good=1;
for(j=1;j<=size(R);j++){if(R[j]!=0){good=0;}}
print("COLON_REMAINDERS_ZERO="+string(good));
number w=-1/2+(1/32)*a^3+(1/8)*a;
map atP=r,1,w,w^2,0,0;
R=atP(I);good=1;
for(j=1;j<=size(R);j++){if(R[j]!=0){good=0;}}
print("POINT_ON_IDEAL="+string(good));
matrix H[4][4];int k;
for(j=1;j<=4;j++){for(k=1;k<=4;k++){H[j,k]=diff(I[j],var(k));}}
poly detH=det(H);poly hd=atP(detH);
print("MASSIVE_HESSIAN_DETERMINANT="+string(hd));
print("MASSIVE_HESSIAN_INVERTIBLE="+string(hd!=0));
poly constantW=reduce(W+5/2,G);
print("CONSTANT_W="+string(constantW==0));
print("BASIS_BEGIN");G;print("BASIS_END");
print("CERTIFICATE_COMPLETE");quit;
''')


def prove(binary='Singular'):
    script = certificate_script()
    OUT.mkdir(parents=True, exist_ok=True)
    script_path = OUT / (STEM+'.sing')
    script_path.write_text(script)
    result = subprocess.run([binary, '-q', str(script_path)],
                            capture_output=True, text=True, timeout=60, check=True)
    log = result.stdout.replace('\r\n', '\n')
    assert '?' not in log and 'CERTIFICATE_COMPLETE' in log, log[:2000]
    markers = dict(line.split('=', 1) for line in log.splitlines()
                   if '=' in line and not line.startswith('_'))
    assert markers['DIM']=='1' and markers['BASIS_SIZE']=='38'
    for label in ('LIFT_IDENTITY', 'ORIGINAL_REMAINDERS_ZERO',
                  'COLON_REMAINDERS_ZERO', 'POINT_ON_IDEAL',
                  'MASSIVE_HESSIAN_INVERTIBLE', 'CONSTANT_W'):
        assert markers[label]=='1', (label, markers[label])
    (OUT / (STEM+'.log')).write_text(log)
    data = {
        'coefficient_field': 'Q(a), a=sqrt(5)+sqrt(-3), a^4-4*a^2+64=0',
        'characteristic': 0,
        'block': 'K=[[x,p,0],[q,y,0],[0,0,z]]',
        'base': '[1,omega,omega^2,0,0], omega=(-1+sqrt(-3))/2',
        'block_W_terms': len(block_polynomials()[0].terms()),
        'omitted_original_F_polynomials_identically_zero': 4,
        'ideal': '<W_x,W_y,W_z,W_p,W_q,z*(x*y-p*q)-1>',
        'standard_basis_size': 38, 'global_dimension': 1,
        'standard_basis_lift_identity_verified': True,
        'original_generators_reduce_to_zero': True,
        'colon_identity': 'I:q=I', 'colon_identity_verified': True,
        'base_on_ideal_verified': True,
        'massive_Hessian_coordinates': ['x','y','z','p'],
        'massive_Hessian_determinant_in_a': markers['MASSIVE_HESSIAN_DETERMINANT'],
        'massive_Hessian_invertible': True,
        'local_dimension_at_base': 1, 'local_curve_smooth': True,
        'local_parameter': 'q', 'all_nine_original_F_terms_zero_to_all_orders': True,
        'determinant_on_curve': 1, 'W_on_curve': '-5/2',
        'vacuum_census_conclusion': 'Infinitely many unperturbed complex F-flat vacua; a finite census cannot be complete.',
        'scope': 'One exact block curve. The full three-null-coordinate germ is not classified. Added Gram/soft/gauge terms are not included.',
        'script_sha256': hashlib.sha256(script.encode()).hexdigest(),
        'log_sha256': hashlib.sha256(log.encode()).hexdigest(),
    }
    (OUT / (STEM+'.json')).write_text(json.dumps(data, indent=2)+'\n')
    return data


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--singular', default=shutil.which('Singular') or 'Singular')
    args=parser.parse_args()
    print(json.dumps(prove(args.singular), indent=2))
