"""Emit a Lean equivalence for a deliberately narrow, whole SMT query.

Supports exactly two integer constants, one directly asserted x*x=y*y*y,
and arithmetic/Boolean residual assertions. Unsupported script constructs
raise ValueError. The generated theorem must be compiled before use.
No solver result or SMT proof certificate is claimed by this emitter.
"""
from __future__ import annotations
import hashlib
import re
from .smt_cert import split_commands, _sexpr


def emit_square_cube(script: str) -> str:
    nodes = [_sexpr(c) for c in split_commands(script)]
    names, assertions, checks = [], [], 0
    for n in nodes:
        op = n[0]
        if checks:
            raise ValueError('commands after the query are unsupported')
        if op in ('set-info',):
            continue
        if op == 'set-logic' and n == ['set-logic', 'QF_NIA']:
            continue
        if op == 'declare-fun' and len(n) == 4 and n[2:] == [[], 'Int']:
            names.append(n[1])
        elif op == 'declare-const' and len(n) == 3 and n[2] == 'Int':
            names.append(n[1])
        elif op == 'assert' and len(n) == 2 and checks == 0:
            assertions.append(n[1])
        elif n == ['check-sat']:
            checks += 1
        else:
            raise ValueError(f'unsupported command: {op}')
    if len(names) != 2 or len(set(names)) != 2 or checks != 1:
        raise ValueError('requires two distinct Int constants and one query')
    if any(not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*', n) for n in names):
        raise ValueError('requires plain identifiers')
    match = None
    for a in assertions:
        for x, y in (names, names[::-1]):
            lhs, rhs = ['*', x, x], ['*', y, y, y]
            if a == ['=', lhs, rhs] or a == ['=', rhs, lhs]:
                match = (x, y, a)
                break
        if match:
            break
    if match is None:
        raise ValueError('no directly asserted square/cube relation')
    x, y, atom = match
    symbols = {x: 'x', y: 'y'}

    def term(e):
        if isinstance(e, str):
            if e in symbols:
                return symbols[e]
            if e.isascii() and e.isdecimal():
                return f'({e} : ℤ)'
            raise ValueError('unsupported arithmetic atom')
        if not e or e[0] not in ('+', '-', '*'):
            raise ValueError('unsupported arithmetic operator')
        op, args = e[0], e[1:]
        if op == '-' and len(args) == 1:
            return f'(-{term(args[0])})'
        if len(args) < 2:
            raise ValueError('arithmetic arity')
        return '(' + f' {op} '.join(term(a) for a in args) + ')'

    def prop(e):
        if e == 'true': return 'True'
        if e == 'false': return 'False'
        if not isinstance(e, list) or not e:
            raise ValueError('unsupported Boolean atom')
        op, args = e[0], e[1:]
        if op in ('=', '<', '<=', '>', '>=') and len(args) == 2:
            ops = {'=': '=', '<': '<', '<=': '≤', '>': '>', '>=': '≥'}
            return f'({term(args[0])} {ops[op]} {term(args[1])})'
        if op in ('and', 'or') and len(args) >= 2:
            return '(' + (' ∧ ' if op == 'and' else ' ∨ ').join(prop(a) for a in args) + ')'
        if op == 'not' and len(args) == 1:
            return f'(¬ {prop(args[0])})'
        raise ValueError('unsupported Boolean operator or arity')

    residual = list(assertions)
    residual.remove(atom)
    body = ' ∧ '.join(prop(a) for a in residual) or 'True'
    digest = hashlib.sha256(script.encode()).hexdigest()
    return f'''import PerfectPower.FormulaTransport
-- Source SHA256: {digest}
-- Symbols: square coordinate {x!r}; cube coordinate {y!r}
namespace PerfectPower.GeneratedFormula
private def residual (x y : ℤ) : Prop := {body}
-- All residual assertions retain their exact integer and Boolean meaning.
theorem original_iff_parameter :
    (∃ x y : ℤ, x * x = y * y * y ∧ residual x y) ↔
      ∃ t : ℤ, residual (t ^ 3) (t ^ 2) := by
  simpa only [pow_succ, pow_zero, mul_one, one_mul] using
    FormulaTransport.square_cube_exists residual
#print axioms original_iff_parameter
end PerfectPower.GeneratedFormula
'''
