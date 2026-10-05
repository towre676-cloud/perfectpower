"""Reconstruct the unique C5 orbital and certify its polynomial algebra exactly."""
from pathlib import Path
import json
import numpy as np
import sympy as sp
from flint import fmpq_mat, fmpz_mat

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'receipts/m22_interactions'


def main():
    operators=json.loads((ROOT/'receipts/m22_frame/recovered_operators.json').read_text())
    w=np.load(ROOT/'galois_merge/vendor/forge/DATA/RELATION/TASK_SELECTED_WORD_PROGRAMS_V23/exact_prefix_1023.npz',allow_pickle=True)['hecke']
    selected=operators['basis_word_indices']
    rx=np.array(operators['right_x'],dtype=object)
    ry=np.array(operators['right_y'],dtype=object)
    star=operators['transpose']
    inverse=fmpq_mat(w[selected].tolist()).inv()
    def orbital(index):
        rows=[np.eye(152,dtype=object)[index]]
        for i in range(255):
            rows.extend([rows[i]@rx,rows[i]@ry])
        solved=inverse*fmpq_mat(np.array(rows,dtype=object)[selected].tolist())
        assert all(x.denominator==1 for x in solved.entries())
        left=np.array([[int(solved[i,j]) for j in range(152)] for i in range(152)],dtype=object)
        right=left[np.ix_(star,star)]
        assert np.array_equal(np.array(rows,dtype=object),w[:511]@left)
        return left,right
    lb,b=orbital(134);ld,d=orbital(139)
    identity=np.eye(152,dtype=object)
    assert np.array_equal(b@b,rx+6*identity)
    assert np.array_equal(b@b@b,4*rx+11*b+6*d)
    assert np.array_equal(b@b@b@b,4*(b@b@b)+17*(b@b)-24*b-36*identity)
    t=sp.Symbol('t')
    cp=fmpz_mat(b.tolist()).charpoly()
    charpoly=sp.Poly.from_list([int(cp[i]) for i in reversed(range(len(cp)))],gens=t)
    assert sp.factor(charpoly.as_expr())==(t-6)**9*(t-2)**65*(t+1)**27*(t+3)**51
    powers=identity.copy();walks=[]
    for i in range(31):
        powers=powers@b;walks.append(int(powers[151,151]))
    result={'characteristic_polynomial':str(sp.factor(charpoly.as_expr())),
        'minimal_polynomial':str((t-6)*(t-2)*(t+1)*(t+3)),
        'closed_walk_counts':walks,'orbital_C5':134,'orbital_distance_three':139,
        'exact_identities':['B^2 = X + 6 I','B^3 = 4 X + 11 B + 6 D',
            'B^4 - 4 B^3 - 17 B^2 + 24 B + 36 I = 0'],
        'all_available_word_extensions_checked':511,
        'characteristic_coefficient_convention':'python-flint coefficients are ascending; reversed for SymPy',
        'scope':'Integral identities in the full 152-dimensional Wilson commutant regular representation.'}
    (OUT/'c5_spectrum.json').write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    (OUT/'c5_operators.json').write_text(json.dumps({'orbital_index':134,'left':lb.tolist(),'right':b.tolist()},sort_keys=True,separators=(',',':'))+'\n')
    print(json.dumps(result,indent=2),flush=True)


if __name__=='__main__':
    main()
