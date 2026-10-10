"""Perfect-power queries on exact stored binary64 polynomial arguments.

This is rational evaluation, not a claim about decimal intent or a rounded
polynomial evaluation. Its receipts are reconstructed in Python, not Lean.
"""
from fractions import Fraction as Q
from .binary64 import exact, classify
from .core import integer_power_root


def polynomial_power_certificate(word, coefficients, degree):
    if type(degree) is not int or not 2 <= degree <= 4096:
        raise ValueError('Power degree in 2..4096 required')
    coefficients = tuple(coefficients)
    if not coefficients or len(coefficients) > 65 or any(isinstance(x,float) for x in coefficients):
        raise ValueError('One to 65 exact rational coefficients required')
    coefficients = tuple(Q(x) for x in coefficients)
    if any(max(abs(v.numerator).bit_length(),v.denominator.bit_length()) > 4096 for v in coefficients):
        raise ValueError('Coefficient exceeds 4096-bit arithmetic budget')
    x = exact(word)
    value = Q(0)
    for c in reversed(coefficients):
        value = value*x+c
        if max(abs(value.numerator).bit_length(),value.denominator.bit_length()) > 32768:
            raise ValueError('Polynomial value exceeds 32768-bit arithmetic budget')
    numerator = integer_power_root(value.numerator,degree)
    denominator = integer_power_root(value.denominator,degree)
    root = Q(numerator,denominator) if numerator is not None and denominator is not None else None
    return {'schema':'perfectpower.binary64-polynomial/1','word':word,'hex':f'{word:016x}',
            'classification':classify(word),'argument':str(x),'coefficients':list(map(str,coefficients)),
            'degree':degree,'value':str(value),'is_power':root is not None,
            'root':None if root is None else str(root),
            'scope':'exact rational polynomial evaluated at the exact stored finite binary64 argument; rounded polynomial arithmetic excluded',
            'verification':'exact arithmetic reconstruction; no new Lean theorem'}


def replay_binary_polynomial(packet):
    if packet.get('schema') != 'perfectpower.binary64-polynomial/1' or packet != polynomial_power_certificate(
            packet['word'],packet['coefficients'],packet['degree']):
        raise ValueError('Binary polynomial certificate does not reconstruct')
    return True
