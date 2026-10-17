"""Rebuild compact, source-bound deep integral receipts from current code.

PYTHONPATH=python python3 python/develop_period_bridge_deep.py

Uses only the Python standard library. It reruns the complete E8 bracket
sweeps, all 130 generating constructions, all 120 previous decompositions,
independent rational value enclosures, full small character tables, phase
reconstruction and the all-type Coxeter classification. Historical retained
summary files are evidence only and never contribute fresh execution counts.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json
import subprocess

from perfectpower import raghava_generating as rg
from perfectpower import e8_lift, phase_descent, period_observability, coxeter_mellin
from perfectpower.dirichlet_periods import DirichletCharacter, PeriodicDirichlet, all_characters
from perfectpower.raghava_periods import two_order_cancellation

ROOT = Path(__file__).resolve().parents[1]
DESTINATION = ROOT/'receipts/period_bridge_deep'
SOURCE_PATHS = (
    'python/develop_period_bridge_deep.py', 'python/export_integral_browser.py',
    'python/perfectpower/raghava_generating.py', 'python/perfectpower/raghava_periods.py',
    'python/perfectpower/cyclotomic_real.py', 'python/perfectpower/e8_lift.py',
    'python/perfectpower/e8_periods.py', 'python/perfectpower/phase_descent.py',
    'python/perfectpower/period_transport.py', 'python/perfectpower/dirichlet_periods.py',
    'python/perfectpower/period_observability.py', 'python/perfectpower/coxeter_mellin.py',
    'web/integral-families/engine.js',
)


def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True)+'\n').encode('utf-8')


def digest(value):
    return hashlib.sha256(encoded(value)).hexdigest()


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def bounds(value):
    return Q(value['lower']), Q(value['upper'])


def overlap(a, b):
    return max(a[0], b[0]) <= min(a[1], b[1])


def compact_interval(value):
    # The complete rational partial is reproducible through the API; retain
    # interval endpoints and a hash rather than huge repeated pi-polynomials.
    return {key: item for key, item in value.items() if key not in ('pi_coefficients',)}


def generating_results():
    families = [rg.generating_family(m, kind) for kind in ('second', 'supplementary') for m in range(65)]
    require(all(rg.verify_family(row) for row in families), 'generating family replay failed')
    decompositions = []
    for s in range(2, 17):
        for r in range(1, s):
            actual, old = rg.two_order_decomposition(r, s), two_order_cancellation(r, s)
            for key in ('A', 'D', 'harmonic_coefficients', 'zeta_coefficients'):
                require(actual[key] == old[key], 'old two-order decomposition mismatch')
            decompositions.append(dict(r=r, s=s, exact_match=True, coefficients_sha256=digest(actual)))
    basis = [rg.canonical_second_basis(m, rg.generating_family(m, 'supplementary')) for m in range(33)]
    values = []
    for m in range(13):
        for kind in ('second', 'supplementary'):
            original = rg.family_partial(m, kind, terms=48, bits=96)
            reduced = rg.family_interval(m, kind, bits=96)
            require(overlap(bounds(original), bounds(reduced)), 'original series and zeta enclosures disjoint')
            if kind == 'second':
                lo, hi = bounds(reduced)
                require((lo if m % 2 == 0 else -hi) > 0, 'second-family strict sign not isolated')
            values.append(dict(m=m, family=kind, original=compact_interval(original),
                               zeta_formula=reduced, overlap_checked=True))
    masters = [rg.master_interval(x, terms=48, bits=96, oscillatory=oscillatory)
               for oscillatory in (False, True) for x in ('0', '1/20', '1/4', '-1/3', '2/5')]
    require(all(row['intervals_overlap'] for row in masters), 'master comparison failed')
    global_checks = []
    for t in ('0', '1/16', '1/4', '1', '2', '4', '9', '16'):
        for order in (0, 3):
            polynomial = rg.global_taylor_bounds(t, order=order, bits=96)
            direct = rg.global_generator_interval(t, terms=192, bits=96)
            require(overlap(bounds(polynomial), bounds(direct)), 'global Taylor inequality comparison failed')
            global_checks.append(dict(t=t, order=order, polynomial=polynomial,
                                      direct=direct, overlap_checked=True))
    return dict(families=families, family_count=len(families), maximum_order=64,
                maximum_weight=131, second_count=65, supplementary_count=65,
                prior_pair_decompositions=decompositions,
                supplementary_basis_reductions=basis, rational_value_comparisons=values,
                master_comparisons=masters, global_taylor_comparisons=global_checks,
                scope='Classical generating families implemented at all requested coefficients; finite order guards are computational budgets, not terminal mathematical weights.',
                source='https://arxiv.org/html/2607.09904v2')


def dirichlet_results():
    characters, transforms, periods, gauss = [], [], 0, []
    for modulus in range(1, 17):
        for character in all_characters(modulus):
            values = character.dft()
            # Exact inverse Fourier reconstruction is independent of the
            # primitive Bernoulli/Gauss formula used for scalar special values.
            for a in range(1, modulus+1):
                from perfectpower.dirichlet_periods import CyclotomicNumber as C
                actual = sum((coefficient*C.root(modulus, h*a)
                              for h, coefficient in enumerate(values)), C(1, 0))
                require(actual == character.value(a), 'character inverse Fourier reconstruction failed')
                transforms.append([modulus, character.order, list(character.exponents), a, actual.packet()])
            scalar = []
            for weight in range(1, 5):
                if character.parity != (-1)**weight:
                    continue
                value = character.special_value(weight)
                require(value['primitive_euler_crosscheck'], 'Gauss/Bernoulli vs Fourier period mismatch')
                scalar.append(value)
                periods += 1
            for a in range(modulus):
                relation = character.gauss_relation(a)
                if relation['applicable']:
                    require(relation['exact_equality'], 'applicable Gauss relation failed')
                gauss.append([modulus, character.order, a, relation['applicable'], relation['exact_equality']])
            characters.append(dict(character=character.packet(), special_values=scalar))
    pairs = []
    for period in range(2, 17):
        for residue in range(1, period+1):
            for parity in (-1, 1):
                obj = PeriodicDirichlet.residue_pair(period, residue, parity)
                reconstructed = obj.inverse_dft()
                require(all(value == coefficient for value, coefficient in zip(reconstructed, obj.coefficients)),
                        'periodic residue inverse Fourier reconstruction failed')
                weight = 3 if parity == -1 else 2
                scalar = obj.special_value(weight)
                require(scalar['status'] == 'exact_algebraic_pi_power', 'matched residue parity did not reduce')
                pairs.append(dict(period=period, residue=residue, parity=parity,
                                  kernel=obj.kernel_receipt(), special_value=scalar))
    beta = DirichletCharacter.beta()
    require(beta.special_value(2)['status'] == 'formal', 'Catalan beta(2) was incorrectly reduced')
    return dict(schema='pp-dirichlet-integral-coverage/1',
                character_moduli='all characters modulo 1 through 16', characters=characters,
                character_count=len(characters), exact_dft_coefficient_reconstructions=len(transforms),
                dft_reconstructions_sha256=digest(transforms),
                gauss_multiplier_checks=len(gauss), gauss_rows_sha256=digest(gauss),
                matched_parity_period_comparisons=periods, residue_pair_count=len(pairs), residue_pairs=pairs,
                beta_values=[beta.special_value(k) for k in (1, 2, 3, 5)],
                modulo_eight_odd_cubic=PeriodicDirichlet.residue_pair(8, 1).special_value(3),
                scope='exact finite cyclotomic Fourier calculations and cited analytic special-value identities; opposite parity remains a formal period',
                formal_kernel_verified=False)


def build():
    parent = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    source_hashes = {path: hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in SOURCE_PATHS}
    generating = generating_results()
    adjoint = e8_lift.receipt(exhaustive=True)
    descent = phase_descent.descent_receipt()
    observable = period_observability.receipt()
    coxeter = coxeter_mellin.receipt()
    dirichlet = dirichlet_results()
    children = {'e8_lift.json': adjoint, 'observability.json': observable,
                'coxeter.json': coxeter, 'dirichlet.json': dirichlet}
    child_hashes = {name: digest(value) for name, value in children.items()}
    results = dict(schema='pp-period-bridge-deep-results/1', source_parent_commit=parent,
                   source_sha256=source_hashes, child_receipts=child_hashes,
                   reproducibility=dict(command='PYTHONPATH=python python3 python/develop_period_bridge_deep.py',
                                        dependencies='Python standard library only',
                                        deterministic_for_same_parent_and_source=True,
                                        timestamps_and_runtime_counters_omitted=True),
                   generating=generating, phase_descent=descent,
                   e8_adjoint=dict(receipt='e8_lift.json', sha256=child_hashes['e8_lift.json'],
                                   dimension=adjoint['dimension'], actual_adjoint_identification_checked=adjoint['actual_adjoint_identification_checked']),
                   observability=dict(receipt='observability.json', sha256=child_hashes['observability.json']),
                   coxeter=dict(receipt='coxeter.json', sha256=child_hashes['coxeter.json']),
                   dirichlet=dict(receipt='dirichlet.json', sha256=child_hashes['dirichlet.json']),
                   proof_scope='Exact rational/integer Python computations, exhaustive finite checks and source-supported analytic theorems; not Lean-kernel formalization of these analytic identities.')
    counts = dict(generating_coefficient_families=len(generating['families']),
                  second_family_coefficients=65, supplementary_family_coefficients=65,
                  maximum_generating_weight=131, prior_pair_decompositions=len(generating['prior_pair_decompositions']),
                  supplementary_basis_reductions=len(generating['supplementary_basis_reductions']),
                  rigorous_generating_value_enclosures=len(generating['rational_value_comparisons']),
                  rigorous_master_comparisons=len(generating['master_comparisons']),
                  global_taylor_checks=len(generating['global_taylor_comparisons']),
                  jacobi_basis_triples=adjoint['jacobi_distinct_basis_triples'],
                  simple_lift_bracket_checks=adjoint['lift_bracket_preservation_pairs'],
                  dirichlet_characters=dirichlet['character_count'],
                  exact_character_dft_checks=dirichlet['exact_dft_coefficient_reconstructions'],
                  exact_character_period_comparisons=dirichlet['matched_parity_period_comparisons'],
                  residue_pair_periods=dirichlet['residue_pair_count'],
                  coxeter_geometry_cases=coxeter['exact_geometry_cases'],
                  coxeter_geometry_roots=sum(row['roots'] for row in coxeter['geometry']),
                  observable_reflection_dimension=observable['reflection']['minimal_dimension'],
                  observable_adjoint_dimension=observable['adjoint']['minimal_dimension'])
    limits = [
        'No identification of 240 cyclotomic field conjugates with 240 E8 roots follows from cardinalities.',
        'The explicit finite phase category and conductor colimit do not establish unspecified higher-category resonance proposals.',
        'Parity-mismatched values such as Catalan beta(2) remain formal periods.',
        'Canonical zeta-coordinate changes are exact formal algebra, not numerical algebraic independence.',
        'Coxeter classification concerns real zeros for s>1; it does not classify complex zeros.',
    ]
    summary = dict(schema='pp-period-bridge-deep/1',
                   title='Complete generating integrals, actual E8 adjoint lift and Coxeter continuation',
                   source_parent_commit=parent, source_sha256=source_hashes, counts=counts,
                   results_sha256=digest(results), result_path='receipts/period_bridge_deep/results.json',
                   child_receipts=child_hashes,
                   application='/integrals/', monograph='docs/PERIOD_BRIDGE_DEEP_MONOGRAPH.md',
                   formal_kernel_verified=False, live_data_is_executable_upgrade=False,
                   scope=results['proof_scope'], limits=limits,
                   highlights=[
                       dict(label='Raghava generating engine', value='130 identities through weight 131',
                            detail='Two complete scalar families, rigorous rational enclosures, a formal basis and exact recovery of every previous pair formula.'),
                       dict(label='Actual E8 adjoint', value='248 dimensions; exhaustive brackets',
                            detail='The root-space signs, Jacobi identity, eight Tits lifts and complete adjoint spectrum are recomputed.'),
                       dict(label='Coxeter continuation', value='all irreducible crystallographic types',
                            detail='Real Mellin zeros classified; B7 and C7 vanish at weight four, with log companion -pi^4*log(2)/5145.'),
                       dict(label='Exact observation', value='248 dimensions reduce to 30',
                            detail='A minimal observable machine preserves the complete E8 adjoint trace sequence; this is not a 30-dimensional faithful adjoint representation.'),
                       dict(label='Dirichlet coverage', value='80 complete character tables',
                            detail='Exact Fourier reconstruction, independent Gauss/Bernoulli comparisons and 270 residue-pair periods.'),
                   ])
    return summary, results, children


def main():
    summary, results, children = build()
    DESTINATION.mkdir(parents=True, exist_ok=True)
    for name, value in {**children, 'results.json': results, 'summary.json': summary}.items():
        (DESTINATION/name).write_bytes(encoded(value))
    print(json.dumps(dict(schema=summary['schema'], **summary['counts'], results_sha256=summary['results_sha256']), sort_keys=True))


if __name__ == '__main__':
    main()
