"""Finite exact contracts for residue and period normalization.

Inputs describe already-chosen meromorphic candidates and holomorphic bases.
This module solves their finite ambiguity; it does not compute analytic periods.
"""
from fractions import Fraction as Q
from .connection_polytope import exact
from .exact_linear import inverse, apply


def normalize_periods(period_matrix, candidate_periods, target_periods=None):
    rows = tuple(tuple(map(exact, row)) for row in period_matrix)
    periods = tuple(map(exact, candidate_periods))
    target = tuple(Q(0) for _ in periods) if target_periods is None else tuple(map(exact, target_periods))
    n = len(periods)
    if len(rows) != n or len(target) != n or any(len(row) != n for row in rows):
        raise ValueError('square period matrix matching the period vectors required')
    if not n:
        return {'correction': [], 'corrected_periods': [], 'unique_in_supplied_basis': True,
                'formalized': False, 'scope': 'zero-dimensional supplied ambiguity'}
    correction = apply(inverse(rows), tuple(t-p for t, p in zip(target, periods)))
    corrected = tuple(p+c for p, c in zip(periods, apply(rows, correction)))
    if corrected != target:
        raise AssertionError('period correction identity failed')
    return {'correction': list(map(str, correction)), 'corrected_periods': list(map(str, corrected)),
            'unique_in_supplied_basis': True, 'formalized': False,
            'scope': 'exact finite period data; actual complex periods are not generated'}


def residue_contract(residues, genus):
    residues = tuple(map(exact, residues))
    if type(genus) is not int or genus < 0:
        raise ValueError('nonnegative integer genus required')
    total = sum(residues, Q(0))
    return {'residues': list(map(str, residues)), 'sum': str(total),
            'existence_condition_met': total == 0,
            'holomorphic_ambiguity_dimension': genus if total == 0 else None,
            'period_conditions_required': genus if total == 0 else None,
            'formalized': False,
            'scope': 'classical simple-pole contract on a compact connected curve'}
