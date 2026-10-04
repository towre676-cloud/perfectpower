"""Complete square-plus-constant solving after an exact integer coordinate shift.

Coordinate magnitude is not a search radius. Failed work budgets still fail.
"""
from fractions import Fraction
from math import comb
from .divisor_square import _integers,solve,evaluate,WorkLimit


def shift_polynomial(coefficients,shift,*,degree_limit=64):
    """Coefficients of P(t+shift), by exact binomial expansion."""
    coefficients=_integers(coefficients)
    if type(shift) is not int:raise ValueError('integer coordinate shift required')
    if type(degree_limit) is not int or degree_limit<1:raise ValueError('positive degree budget required')
    if len(coefficients)-1>degree_limit:raise WorkLimit('coordinate-shift degree budget exceeded')
    return tuple(sum(coefficients[j]*comb(j,i)*shift**(j-i) for j in range(i,len(coefficients)))
                 for i in range(len(coefficients)))


def solve_centered(coefficients,k,*,shift=None,work_limit=1_000_000,degree_limit=64):
    """Center at the nearest integer mean root; solve all integer x,y exactly.

    The centering heuristic affects cost, never correctness. Some translated
    polynomials remain costly; no unproved completeness is returned on failure.
    """
    coefficients=_integers(coefficients);d=len(coefficients)-1
    if d<1:raise ValueError('nonconstant polynomial required')
    automatic=shift is None
    if automatic:
        mean=Fraction(-coefficients[-2],d*coefficients[-1]);lo=mean.numerator//mean.denominator
        shift=lo if mean-lo<=Fraction(1,2) else lo+1
    centered=shift_polynomial(coefficients,shift,degree_limit=degree_limit)
    if automatic and abs(centered[0])>abs(coefficients[0]):
        shift=0;centered=coefficients
    if shift_polynomial(centered,-shift,degree_limit=degree_limit)!=coefficients:
        raise AssertionError('coordinate identity failed')
    result=solve(centered,k,work_limit=work_limit)
    points=sorted((t+shift,y) for t,y in result['points'])
    if any(y*y!=evaluate(coefficients,x)**2+k for x,y in points):
        raise AssertionError('translated point failed its original equation')
    return {**result,'points':points,'coefficients':list(coefficients),
            'centered_coefficients':list(centered),'coordinate_shift':shift,
            'centered_points':result['points'],'coordinate_identity_checked':True,
            'scope':'all integer coordinates; a bijective integer translation of complete divisor fibres'}


def emit_lean_instance(result,name='hidden_needle'):
    """Emit an independent native centered solve and integer-translation theorem.

    Emission is not acceptance. Compile this file before calling it a proof.
    """
    import re
    if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*',name):raise ValueError('simple identifier required')
    c=result['centered_coefficients'];original=result['coefficients'];s=result['coordinate_shift'];k=result['k']
    return f'''import PerfectPower.Tactic.NativePolynomialPower

namespace PerfectPower.Showcase.{name}
open NativePolynomialSquare
native_polynomial_square canonical for {c}, {k}

def translated : Finset (ℤ × ℤ) := canonical.image fun p => (p.1 + ({s}), p.2)

theorem coordinate_identity (x : ℤ) :
    eval {original} x = eval {c} (x - ({s})) := by
  simp only [eval]
  ring

theorem original_complete (x y : ℤ) :
    y^2 = (eval {original} x)^2 + ({k}) ↔ (x,y) ∈ translated := by
  rw [coordinate_identity, canonical_complete]
  simp only [translated, Finset.mem_image]
  constructor
  · intro h
    refine ⟨(x - ({s}), y), h, ?_⟩
    ext <;> simp
  · rintro ⟨⟨t,w⟩, h, heq⟩
    have hx : t + ({s}) = x := congrArg Prod.fst heq
    have hy : w = y := congrArg Prod.snd heq
    have ht : x - ({s}) = t := by omega
    simpa [ht, hy] using h

#print axioms original_complete
end PerfectPower.Showcase.{name}
'''
