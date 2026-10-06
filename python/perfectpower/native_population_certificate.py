"""Emit kernel-checkable certificates for bounded polynomial image populations.

The bounded original predicate is retained verbatim as Lean arithmetic syntax.
No unbounded-domain compiler result or external proof is trusted by the theorem.
"""
import hashlib
import json
from .semilinear_domains import _normalize
from .residue_cover import integer_polynomial, evaluate
from .polynomial_domains import _boolean, _holds
from .divisor_square import WorkLimit


def _int(value, name, bits=256):
    if type(value) is not int:
        raise ValueError(f'{name} must be an integer')
    if abs(value).bit_length() > bits:
        raise WorkLimit(f'{name} exceeds integer bit budget')
    return value


def _polynomial(coefficients):
    result = '0'
    for c in reversed(coefficients):
        result = f'(({c}) + x * ({result}))'
    return result


def _predicate(tree, atoms):
    if type(tree) is bool:
        return 'True' if tree else 'False'
    if 'atom' in tree:
        atom = atoms[tree['atom']]
        lhs = _polynomial(atom['poly'])
        if 'modulus' in atom:
            lhs = f'(({lhs}) % ({atom["modulus"]}))'
        rhs = atom.get('value', 0)
        relation = {'!=': '≠', '<=': '≤', '>=': '≥'}.get(atom['relation'], atom['relation'])
        return f'({lhs} {relation} ({rhs}))'
    args = [_predicate(a, atoms) for a in tree['args']]
    if tree['op'] == 'not':
        return f'(¬ {args[0]})'
    identity, connective = ('True', ' ∧ ') if tree['op'] == 'and' else ('False', ' ∨ ')
    return '(' + connective.join(args) + ')' if args else identity


def population_certificate(lower, upper, predicate, polynomial, *, ranks=None,
                           work_limit=4096):
    """Return a Lean source and exact receipts for distinct numeric image ranks.

    Count and membership/rank claims are proved by Lean kernel reduction when
    the returned source is compiled. Merely emitting this packet is not a proof.
    Bounds are part of the source semantics, even if predicate implies them.
    """
    lo, hi = _int(lower, 'lower'), _int(upper, 'upper')
    if type(work_limit) is not int or not 1 <= work_limit <= 16384:
        raise ValueError('work_limit must lie between 1 and 16384')
    if max(0, hi-lo+1) > work_limit:
        raise WorkLimit('bounded source exceeds enumeration certificate budget')
    coefficients = list(integer_polynomial(polynomial))
    if len(coefficients) > 33:
        raise WorkLimit('polynomial degree exceeds 32')
    for c in coefficients:
        _int(c, 'coefficient')
    tree, atoms = _normalize(predicate)
    for atom in atoms:
        if len(atom['poly']) > 33:
            raise WorkLimit('predicate polynomial degree exceeds 32')
        for c in atom['poly']:
            _int(c, 'predicate coefficient')
        for key in ('modulus', 'value'):
            if key in atom:
                _int(atom[key], key)
    values = set()
    for x in range(lo, hi+1):
        truth = [_holds((evaluate(a['poly'], x) % a['modulus'] - a['value'])
                        if 'modulus' in a else evaluate(a['poly'], x), a['relation'])
                 for a in atoms]
        if _boolean(tree, truth):
            values.add(_int(evaluate(coefficients, x), 'image value', bits=4096))
    values = sorted(values)
    if ranks is None:
        ranks = []
    if not isinstance(ranks, list) or len(ranks) > 64:
        raise ValueError('at most 64 ranks required')
    for i in ranks:
        if type(i) is not int or not 0 <= i < len(values):
            raise ValueError('rank outside distinct image population')
    p, f = _predicate(tree, atoms), _polynomial(coefficients)
    source = f'''import PerfectPower.FiniteDomainCertificate
namespace PerfectPower.GeneratedPopulation
open PerfectPower.FiniteDomainCertificate
private def accepts (x : ℤ) : Prop := {p}
private instance : DecidablePred accepts := fun x => by unfold accepts; infer_instance
private def imageMap (x : ℤ) : ℤ := {f}
private def transcript : Domain := boundedImage ({lo}) ({hi}) accepts imageMap

theorem source_complete (z : ℤ) :
    z ∈ evaluate transcript ↔ ∃ x : ℤ, ({lo}) ≤ x ∧ x ≤ ({hi}) ∧ accepts x ∧ imageMap x = z :=
  bounded_image_complete ({lo}) ({hi}) accepts imageMap z

theorem count_checked : (evaluate transcript).card = {len(values)} := by decide +kernel
'''
    for j, i in enumerate(ranks):
        value = values[i]
        source += f'''
theorem selection_{j} :
    (∃ x : ℤ, ({lo}) ≤ x ∧ x ≤ ({hi}) ∧ accepts x ∧ imageMap x = ({value})) ∧
    ∀ z, (∃ x : ℤ, ({lo}) ≤ x ∧ x ≤ ({hi}) ∧ accepts x ∧ imageMap x = z) →
      rank (evaluate transcript) z = {i} → z = ({value}) := by
  exact bounded_image_select ({lo}) ({hi}) accepts imageMap {i} ({value})
    (by decide +kernel) (by decide +kernel)
'''
    source += '\nend PerfectPower.GeneratedPopulation\n'
    spec = dict(lower=lo, upper=hi, predicate=predicate, polynomial=coefficients, ranks=ranks)
    return dict(schema='pp-native-population-certificate/1', specification=spec,
                cardinality=len(values), selections=[dict(rank=i, value=values[i]) for i in ranks],
                lean=source, source_sha256=hashlib.sha256(source.encode()).hexdigest(),
                specification_sha256=hashlib.sha256(json.dumps(spec, sort_keys=True,
                    separators=(',', ':')).encode()).hexdigest(),
                execution_verified=False, ordering='increasing distinct numeric image value',
                scope='bounded source; compile emitted Lean to check count and selection proofs')
