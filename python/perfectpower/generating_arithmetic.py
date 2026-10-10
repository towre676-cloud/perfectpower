"""Generating functions of declared recurrences and exact modular power sieves.

Cycle acceptance is a necessary congruence condition, not global powerhood.
Pell OGFs are indexed by unit exponent, not the integer-coordinate hit index.
"""
from fractions import Fraction as Q
from .recurrence import Recurrence, filter_count
from .generating import RationalGF, from_recurrence, periodic_gf, replay_generating
from .arith import pell_fundamental


def pell_generating(D, unit=None):
    if type(D) is not int or D <= 0:
        raise ValueError('Positive integer D required')
    x,y = pell_fundamental(D) if unit is None else tuple(unit)
    if type(x) is not int or type(y) is not int or x <= 1 or y <= 0 or x*x-D*y*y != 1:
        raise ValueError('Positive norm-one Pell unit required')
    gx,gy = from_recurrence([-1,2*x],[1,x]),from_recurrence([-1,2*x],[0,y])
    return {'schema':'perfectpower.pell-gf/1','D':D,'unit':[x,y],
            'x':gx.packet(),'y':gy.packet(),
            'scope':'coordinates x_n+y_n sqrt(D)=(x+y sqrt(D))^n, n>=0; one unit orbit; no coordinate-index hit OGF claim',
            'verification':'exact rational identities; no new Lean theorem'}


def modular_power_gf(coefficients, initial, degree, modulus, state_limit=10000):
    if type(degree) is not int or not 2 <= degree <= 4096:
        raise ValueError('Degree in 2..4096 required')
    if type(modulus) is not int or not 2 <= modulus <= 10000:
        raise ValueError('Modulus in 2..10000 required')
    if type(state_limit) is not int or not 1 <= state_limit <= 100000:
        raise ValueError('State limit in 1..100000 required')
    coefficients,initial=tuple(coefficients),tuple(initial)
    if any(isinstance(x,float) for x in coefficients+initial):
        raise TypeError('Use exact recurrence coefficients and initial values')
    recurrence = Recurrence(tuple(Q(x) for x in coefficients),tuple(Q(x) for x in initial))
    residues = set(pow(x,degree,modulus) for x in range(modulus))
    table = recurrence.residue_filter(modulus,lambda state:state[0] in residues,state_limit=state_limit)
    import json
    table = json.loads(json.dumps(table))
    mu,period = table['preperiod'],table['period']
    if mu+period > 512:
        raise ValueError('Completed cycle exceeds the 512-coefficient OGF normalization budget')
    prefix = [int(i in table['prefix_hits']) for i in range(mu)]
    cycle = [int(i in table['cycle_hits']) for i in range(period)]
    # The cycle can be large: the compact OGF itself remains available even
    # when an expensive full Hankel minimality witness would exceed 128 states.
    gf = periodic_gf(prefix,cycle)
    ogf = {'numerator':list(map(str,gf.numerator)), 'denominator':list(map(str,gf.denominator))}
    return {'schema':'perfectpower.modular-power-gf/1',
            'coefficients':list(map(str,recurrence.coefficients)), 'initial':list(map(str,recurrence.initial)),
            'degree':degree,'modulus':modulus,'state_limit':state_limit,'cycle_table':table,
            'accepted_index_gf':ogf, 'power_residues':sorted(residues),
            'scope':'exact nonnegative recurrence indices passing this modular power condition; necessary filter, not a complete integer-power solution set',
            'verification':'reconstruct completed finite-state cycle; no new Lean theorem'}


def modular_count(packet, stop):
    replay_arithmetic_gf(packet)
    if packet.get('schema') != 'perfectpower.modular-power-gf/1':
        raise ValueError('Modular power OGF required')
    return filter_count(packet['cycle_table'],stop)


def replay_arithmetic_gf(packet):
    if packet.get('schema') == 'perfectpower.pell-gf/1':
        expected = pell_generating(packet['D'],packet['unit'])
    elif packet.get('schema') == 'perfectpower.modular-power-gf/1':
        expected = modular_power_gf(packet['coefficients'],packet['initial'],packet['degree'],
                                    packet['modulus'],packet['state_limit'])
    else:
        raise ValueError('Unknown arithmetic generating-function schema')
    if packet != expected:
        raise ValueError('Arithmetic generating-function certificate does not reconstruct')
    return True


def compile_spec(spec):
    from .generating import from_state,binomial_tail
    from .binary64 import power_certificate
    kind = spec['kind']
    if kind == 'binary64_polynomial':
        from .binary_polynomial import polynomial_power_certificate
        return polynomial_power_certificate(spec['word'],spec['coefficients'],spec['degree'])
    if kind == 'rational_gf':
        return RationalGF(spec['numerator'],spec['denominator']).packet()
    if kind == 'recurrence_gf':
        return from_recurrence(spec['coefficients'],spec['initial']).packet()
    if kind == 'state_gf':
        return from_state(spec['A'],spec['initial'],spec['C']).packet()
    if kind == 'rational_gf_tail':
        return RationalGF(spec['numerator'],spec['denominator']).tail(spec['argument'],spec['radius'],spec['count'])
    if kind == 'binomial_tail':
        return binomial_tail(spec['alpha'],spec['argument'],spec['count'])
    if kind == 'binary64_power':
        return power_certificate(spec['word'],spec['degree'])
    if kind == 'pell_gf':
        return pell_generating(spec['D'],spec.get('unit'))
    if kind == 'modular_power_gf':
        return modular_power_gf(spec['coefficients'],spec['initial'],spec['degree'],spec['modulus'],spec.get('state_limit',10000))
    raise ValueError('Unknown arithmetic series kind')


def replay(packet):
    from .binary64 import replay_power
    if packet.get('schema') == 'perfectpower.binary64-polynomial/1':
        from .binary_polynomial import replay_binary_polynomial
        return replay_binary_polynomial(packet)
    if packet.get('schema') == 'exact.binary64-power/1':
        return replay_power(packet)
    if packet.get('schema','').startswith('perfectpower.'):
        return replay_arithmetic_gf(packet)
    return replay_generating(packet)


def add_commands(sub):
    from pathlib import Path
    p = sub.add_parser('arithmetic-series',help='compile or replay exact generating functions and binary64 power certificates')
    p.add_argument('operation',choices=['compile','replay'])
    p.add_argument('input',type=Path)
    p.add_argument('--output',type=Path)


def cli(args):
    if args.command != 'arithmetic-series':
        return False
    import json
    spec = json.loads(args.input.read_text())
    result = compile_spec(spec) if args.operation == 'compile' else {'accepted':replay(spec)}
    text = json.dumps(result,indent=2)+'\n'
    if args.output:
        args.output.write_text(text)
    else:
        print(text,end='')
    return True
