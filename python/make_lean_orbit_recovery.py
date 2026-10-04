"""Emit finite matrix witnesses; Lean independently checks every identity."""
from fractions import Fraction as Q
from pathlib import Path
from perfectpower.recurrence import Recurrence,scan_seq_directory
from perfectpower.recurrence_identity import companion,compare_recurrences


def rec(entry):
    return Recurrence(tuple(map(Q,entry['coefficients'])),tuple(map(Q,entry['initial'])))


def scalar(x):
    x=Q(x)
    return f'({x.numerator} / {x.denominator} : ℚ)'


def vector(xs):return '!['+', '.join(map(scalar,xs))+']'
def matrix(rows):return '!!['+'; '.join(', '.join(map(scalar,row)) for row in rows)+']'


def generate(directory):
    out=['import PerfectPower.OrbitRecovery','namespace PerfectPower.Generated.OrbitRecovery',
         'open Matrix PerfectPower.OrbitRecovery','set_option maxRecDepth 100000']
    count=0
    for e in scan_seq_directory(directory)['candidates']:
        bridge=e.get('supplied_GF_bridge')
        if not bridge or not bridge['prefix_matches']:continue
        left=rec(e);base=rec(bridge)
        right=Recurrence(base.coefficients,tuple(base.nth(e['offset']+i) for i in range(len(base.coefficients))))
        result=compare_recurrences(left,right)
        if result['status']!='ZERO_FOR_ALL_NONNEGATIVE_INDICES':raise ValueError('nonidentity')
        a,b=companion(left),companion(right);r,s=len(a),len(b);n=r+s
        A=tuple(tuple(a[i][j] if i<r and j<r else b[i-r][j-r] if i>=r and j>=r else Q(0)
                      for j in range(n)) for i in range(n))
        basis=result['orbit_basis'];k=len(basis)
        if not k:raise ValueError('zero-dimensional certificate requires separate emitter')
        C=tuple(tuple(basis[j][i] for j in range(k)) for i in range(n))
        closure=result['closure_coefficients']
        B=tuple(tuple(Q(i==j+1) if j<k-1 else closure[i] for j in range(k)) for i in range(k))
        H=(tuple(Q(1 if j==0 else -1 if j==r else 0) for j in range(n)),)
        name=e['id'];seed=left.initial+right.initial;z=tuple(Q(i==0) for i in range(k))
        out += [f'-- Offset {e["offset"]}; source SHA256 {e["sha256"]}. Supplied definitions only.',
                f'def {name}_A : Matrix (Fin {n}) (Fin {n}) ℚ := {matrix(A)}',
                f'def {name}_B : Matrix (Fin {k}) (Fin {k}) ℚ := {matrix(B)}',
                f'def {name}_C : Matrix (Fin {n}) (Fin {k}) ℚ := {matrix(C)}',
                f'def {name}_H : Matrix (Fin 1) (Fin {n}) ℚ := {matrix(H)}',
                f'theorem {name}_all (t : ℕ) : {name}_H *ᵥ orbit (fun v => {name}_A *ᵥ v) {vector(seed)} t=0 := by',
                f'  have hs : {vector(seed)} = {name}_C *ᵥ {vector(z)} := by decide +kernel',
                '  rw [hs]',
                f'  exact matrix_zero {name}_A {name}_B {name}_C {name}_H {vector(z)} (by decide +kernel) (by decide +kernel) t']
        count+=1
    out+=['end PerfectPower.Generated.OrbitRecovery']
    return '\n'.join(out)+'\n',count


if __name__=='__main__':
    source,count=generate('data/oeis/seq')
    Path('PerfectPower/Generated/OrbitRecovery.lean').write_text(source)
    print('Emitted',count,'all-future matrix certificates')
