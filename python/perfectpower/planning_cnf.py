"""Functional binary-adder encoding for independent #SAT comparisons.

Every original assignment has exactly one extension to gate variables. Counts
are unprojected: auxiliary gates create no extra project populations.
"""
from itertools import product
from .model_counting import CNF
from .planning import CompletionPlanner

class Circuit:
    def __init__(self, n):
        self.n = n
        self.clauses = []
        self.gates = []

    def gate(self, inputs, fn):
        variables = sorted({abs(x) for x in inputs if type(x) is int})
        rows = []
        for bits in product((0, 1), repeat=len(variables)):
            assignment = dict(zip(variables, bits))
            values = [x if type(x) is bool else bool(assignment[abs(x)]) == (x > 0) for x in inputs]
            rows.append((bits, bool(fn(*values))))
        if all(value == rows[0][1] for _, value in rows):
            return rows[0][1]
        # Reuse a literal when the entire truth table is that literal.
        for v in variables:
            for sign in (1, -1):
                if all(value == (bool(bits[variables.index(v)]) == (sign > 0)) for bits, value in rows):
                    return sign*v
        self.n += 1
        out = self.n
        for bits, value in rows:
            self.clauses.append(tuple([-v if bit else v for v, bit in zip(variables, bits)]+[out if value else -out]))
        self.gates.append((out, tuple(inputs), tuple(rows), tuple(variables)))
        return out

    def assert_true(self, signal):
        if type(signal) is bool:
            if not signal:
                self.clauses.append(())
        else:
            self.clauses.append((signal,))

    def le(self, bits, bound):
        if bound < 0:
            return False
        if bound >= (1 << len(bits))-1:
            return True
        le = True
        for j, bit in enumerate(bits):
            if (bound >> j) & 1:
                le = self.gate((bit, le), lambda x, rest: not x or rest)
            else:
                le = self.gate((bit, le), lambda x, rest: not x and rest)
        return le

    def extend(self, original):
        values = {i+1: bool(x) for i, x in enumerate(original)}
        for out, inputs, rows, variables in self.gates:
            bits = tuple(int(values[v]) for v in variables)
            values[out] = dict(rows)[bits]
        return [int(values[i]) for i in range(1, self.n+1)]


def encode_allocation(spec):
    p = CompletionPlanner(spec, _compile=False)
    if p.kind != 'allocation' or p.machine_model is not None or any(v[2:5] != (0, 1, 2) for v in p.variables):
        raise ValueError('CNF encoding requires independent original binary projects')
    c = Circuit(len(p.variables))
    for k, (lo, hi) in enumerate(zip(p.lower, p.upper)):
        total = sum(v[0][k] for v in p.variables)
        width = max(1, total.bit_length())
        bits = [False]*width
        for j, v in enumerate(p.variables):
            cost, carry, next_bits = v[0][k], False, []
            for h in range(width):
                x = j+1 if (cost >> h) & 1 else False
                next_bits.append(c.gate((bits[h], x, carry), lambda a, b, d: a ^ b ^ d))
                carry = c.gate((bits[h], x, carry), lambda a, b, d: (a and b) or (a and d) or (b and d))
            bits = next_bits
        c.assert_true(c.le(bits, hi))
        if lo:
            less = c.le(bits, lo-1)
            c.assert_true(not less if type(less) is bool else -less)
    return CNF(c.n, tuple(c.clauses)), c
