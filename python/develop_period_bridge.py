"""Regenerate exact integral-family receipts and independent numeric comparisons.

Run from the repository root: PYTHONPATH=python python python/develop_period_bridge.py
No third-party packages, downloaded data, nondeterministic timings, or scratch
files are required. The analytic identities retain their published provenance;
the finite receipts are exact Python computations, not Lean proof objects.
"""
from decimal import Decimal, localcontext
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import subprocess

from perfectpower.raghava_periods import (
    ARCSINE_SOURCE, SINE_SOURCE, arcsine_angle, arcsine_kernel, arcsine_moment,
    cancellation_partial, sine_pole, two_order_cancellation, verify_receipt,
)
from perfectpower.cyclotomic_periods import (
    full_fiber_reduction, primitive_conjugate_reduction,
)
from perfectpower.e8_periods import receipt as e8_receipt
from perfectpower.period_transport import (
    PhaseObject, TransportArrow, even_period_coefficient, primitive_phases,
    root_fiber, transport_closure, verify_transport,
)


ROOT = Path(__file__).resolve().parents[1]
DESTINATION = ROOT / 'receipts' / 'period_bridge'
PI_DIGITS = ('3.141592653589793238462643383279502884197169399375105820974944592307816406286'
             '2089986280348253421170679')


def _bytes(value):
    return (json.dumps(value, indent=2, sort_keys=True)+'\n').encode('utf-8')


def _digest(value):
    return hashlib.sha256(_bytes(value)).hexdigest()


def _require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def _numerical_comparison(identities):
    """Independent eta finite differences, explicitly not rigorous numerics.

    The exact tail bound is rigorous; these independently rounded values are
    diagnostic comparisons, not an interval-arithmetic validation of zeta.
    """
    with localcontext() as context:
        context.prec = 200
        dpi = Decimal(PI_DIGITS)
        def decimal(value):
            value = Q(value)
            return Decimal(value.numerator)/value.denominator
        def zeta(order):
            differences = [Decimal(1)/Decimal(k+1)**order for k in range(320)]
            eta = Decimal(0)
            denominator = Decimal(2)
            while differences:
                eta += differences[0]/denominator
                differences = [a-b for a,b in zip(differences, differences[1:])]
                denominator *= 2
            return eta/(1-Decimal(2)**(1-order))
        zetas = {order:zeta(order) for order in range(3,34,2)}
        rows = []
        for identity in identities:
            partial = cancellation_partial(identity, 80)
            left = sum(decimal(row['coefficient'])*dpi**row['pi_power']
                       for row in partial['pi_coefficients'])
            right = sum(decimal(row['coefficient'])*dpi**row['pi_power']*zetas[row['zeta_order']]
                        for row in identity['zeta_coefficients'])
            difference = abs(left-right)
            bound = decimal(partial['tail_absolute'])
            _require(difference < bound, 'independent numerical comparison exceeds exact tail')
            rows.append(dict(r=identity['r'],s=identity['s'],weight=identity['weight'],
                             series_terms=80,numeric_value=str(right),difference=str(difference),
                             tail_absolute=partial['tail_absolute'],
                             difference_to_bound_ratio=str(difference/bound),within_bound=True))
        return dict(arithmetic='Decimal precision 200; Euler-transformed eta with 320 terms; finite pi literal',
                    rigorous_numeric_enclosure=False,
                    exact_tail_bound=True,
                    provenance='recomputed here independently of harmonic recurrence and Fourier-zeta coefficient construction; no scratch input',
                    limitation='rounded zeta and pi values are comparisons only; analytic validity comes from the cited theorem and exact algebraic cancellation',
                    comparisons=len(rows),all_within_bounds=True,
                    maximum_difference_to_bound_ratio=str(max(Decimal(row['difference_to_bound_ratio']) for row in rows)),
                    rows=rows)


def _small_filters(maximum=48):
    rows = []
    checks = 0
    for N in range(1,maximum+1):
        for n in range(1,N+1):
            if N % n:
                continue
            for a in range(n):
                reduction = primitive_conjugate_reduction(n,N,a)
                _require(len(reduction.source_phases()) == reduction.phase_count,
                         'small primitive phase multiplicity mismatch')
                coefficients = []
                for weight in (2,4,6):
                    _require(reduction.verify_even_weight(weight), 'small Bernoulli reduction mismatch')
                    coefficients.append(str(reduction.real_even_pi_coefficient(weight)))
                    checks += 1
                rows.append([n,N,a,reduction.phase_count,coefficients])
    return dict(domain='every 1<=N<=48, positive n dividing N, and a=0,...,n-1; primitive fibers',
                weights=[2,4,6],cases=len(rows),exact_even_weight_comparisons=checks,
                all_passed=True,
                method='enumerate every source phase; compare full Bernoulli sum with independent reduced expression',
                case_rows_sha256=_digest(rows))


def _phase_results():
    primitive = primitive_conjugate_reduction(1680,443520)
    full = full_fiber_reduction(1680,443520)
    _require(primitive.phase_count == 240 and len(primitive.terms) == 2,
             'artifact conjugate fiber mismatch')
    _require(full.phase_count == 264 and len(full.terms) == 1,
             'artifact complete fiber mismatch')
    weights = []
    for weight in range(2,14,2):
        _require(primitive.verify_even_weight(weight) and full.verify_even_weight(weight),
                 'artifact full-source Bernoulli comparison failed')
        obj = root_fiber(1680,264,primitive=True)
        coefficient = primitive.real_even_pi_coefficient(weight)
        _require(even_period_coefficient(obj,weight) == coefficient,
                 'independent phase object and distribution coefficients differ')
        weights.append(dict(weight=weight,primitive_pi_coefficient=str(coefficient),
                            full_pi_coefficient=str(full.real_even_pi_coefficient(weight)),
                            full_source_exact_comparison=True,
                            independent_phase_object_comparison=True))
    _require(Q(weights[0]['primitive_pi_coefficient']) == Q(22537,6773760),
             'reference dilogarithm coefficient mismatch')
    lo,hi = primitive.specialize(2).real_interval(80)
    return dict(primitive=primitive.as_dict(2),full=full.as_dict(2),
                symbolic_identity='sum_primitive I_s(Q^u)=264^(1-s) I_s(q)-24^(1-s) I_s(q^611)',
                parameters=dict(q='exp(i*pi/840)',Q='exp(i*pi/221760)',
                                q_order=1680,Q_order=443520,power_map_degree=264,
                                base_field_degree=384,extension_field_degree=240),
                even_weight_checks=weights,
                real_weight_two_interval=dict(lower=str(lo),upper=str(hi),bits=80,
                                              arithmetic='rational Machin-formula pi enclosure'),
                bounded_exhaustive=_small_filters(),
                scope='integer weights in receipts; symbolic distribution valid for Re(s)>1; 264 branches differ from 240 primitive field conjugates')


def _transport_results():
    base = PhaseObject(1680,{1:1})
    direct = TransportArrow.rule(base,'lift',conductor=443520)
    first = TransportArrow.rule(base,'lift',conductor=6720)
    composed = first.then(TransportArrow.rule(first.target,'lift',conductor=443520))
    _require(direct.target == composed.target,'two lift paths do not commute')
    primitive = primitive_phases(1680)
    restriction = TransportArrow.rule(primitive,'restrict',conductor=30)
    relift = restriction.then(TransportArrow.rule(restriction.target,'lift',conductor=1680))
    power = TransportArrow.rule(primitive,'power',exponent=56)
    _require(relift.target == power.target,'restriction/power path mismatch')
    fiber = root_fiber(1680,264,primitive=True)
    collapse = TransportArrow.rule(fiber,'power',exponent=264)
    _require(collapse.target == base.lift(443520).scale(240),'primitive phase collapse mismatch')
    receipts = [path.receipt() for path in (direct,composed,restriction,relift,power,collapse)]
    _require(all(verify_transport(row) for row in receipts),'transport receipt replay failed')
    closures = []
    for n in range(2,33):
        objects = transport_closure([PhaseObject(n,{1:1})],
                                    [('power',{'exponent':2}),('dual',{})],max_objects=100)
        closures.append(dict(conductor=n,object_count=len(objects),
                             exponent_support=sorted(obj.terms[0][0] for obj in objects)))
    return dict(paths=receipts,checked_paths=len(receipts),
                commuting_paths=[dict(left=0,right=1,same_target=True),
                                 dict(left=3,right=4,same_target=True)],
                restriction_to_order_30=restriction.target.packet(),
                multiplicity_per_coxeter_eigenphase=48,
                primitive_fiber_collapse=dict(source_dimension='240',target_dimension=str(collapse.target.dimension),
                                              target_phase_count=len(collapse.target.terms)),
                finite_power_dual_closures=closures,
                closure_rule_domain='single character at every conductor 2,...,32; power 2 and dual; complete finite requested rule closure',
                scope='exact character objects and replayable rewrite paths; no higher-category colimit or tensor-to-product integral functor is asserted')


def build():
    parent = subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
    source_paths = ['python/develop_period_bridge.py',
                    'python/perfectpower/raghava_periods.py',
                    'python/perfectpower/cyclotomic_periods.py',
                    'python/perfectpower/e8_periods.py',
                    'python/perfectpower/period_transport.py']
    source_hashes = {path:hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in source_paths}
    identities = [two_order_cancellation(r,s) for s in range(2,17) for r in range(1,s)]
    sine = [sine_pole(k) for k in range(1,65)]
    sine += [sine_pole(k,a,b) for a,b in [('1/2','2'),('3/2','2/5'),('2','3')]
             for k in (1,2,3,7,16,32)]
    moments = [arcsine_moment(j,t,terms) for j in (1,2,3,5,8)
               for t in ('0','1/2','1','3/2','19/10') for terms in (16,48)]
    kernels = [arcsine_kernel(u,t,terms) for u in ('0','1/2','2/3','2','7/2')
               for t in ('0','1/2','1','3/2','19/10') for terms in (16,48)]
    angles = [arcsine_angle(j,angle) for angle in ('1/840','1/221760','1/6')
              for j in range(1,9)]
    partials = [cancellation_partial(two_order_cancellation(r,s),80)
                for r,s in ((1,2),(2,3),(1,4),(3,5),(15,16))]
    replay = sine+identities+moments+kernels+angles+partials
    _require(all(verify_receipt(row) for row in replay),'Raghava receipt failed exact replay')
    e8 = e8_receipt()
    _require(e8['combined_model']['pi_coefficients']['2'] == '0','E8 combined weight-two zero failed')
    results = dict(schema='pp-period-bridge-results/1',source_parent_commit=parent,
                   source_sha256=source_hashes,
                   reproducibility=dict(command='PYTHONPATH=python python python/develop_period_bridge.py',
                                        dependencies='Python standard library only',
                                        deterministic_for_same_parent_and_source=True,
                                        generated_at_timestamp_omitted=True),
                   source_provenance=dict(raghava_current_paper=ARCSINE_SOURCE,
                                          sine_pole_archive=SINE_SOURCE,
                                          artifact_parameter_sources=[
                                              'https://claude.ai/public/artifacts/1db99748-b7fd-477b-8a9c-1bb54fb33a19',
                                              'https://claude.ai/public/artifacts/4fd0f32a-22b6-4fae-b2d2-1f3732d324af'],
                                          attribution='Raghava source families and classical antecedents retained; all-k sine generalization credited to Abdulhafeez Abdulsalam'),
                   raghava=dict(two_order_identities=identities,sine_pole=sine,
                                arcsine_moment_bounds=moments,arcsine_kernel_bounds=kernels,
                                exact_angle_specializations=angles,selected_series_partials=partials,
                                exact_receipts_replayed=len(replay),all_exact_replays_passed=True,
                                two_order_domain='all 120 pairs 1<=r<s<=16; weights 5 through 33; not an independence count'),
                   cyclotomic=_phase_results(),e8=e8,transport=_transport_results(),
                   independent_numeric_diagnostics=_numerical_comparison(identities),
                   proof_scope='exact finite integer/rational calculations and cited analytic theorems; not Lean-kernel proofs of the new analytic identities',
                   limitations=[
                       'This does not prove the supplied artifacts categorical colimit or arbitrary E8 unification claims.',
                       'The 240 Galois conjugates are not identified with the 240 E8 roots by matching cardinalities.',
                       'The E8 root-permutation-plus-Cartan model is a verified cyclic direct sum; no adjoint lift with root-space signs is asserted.',
                       'The two-order family is complete only within the cited polynomial ansatz; identities need not be numerically linearly independent.',
                       'Numerical Decimal comparisons are diagnostics and have no rigorous zeta enclosure.'])
    raw = _bytes(results)
    summary = dict(schema='pp-period-bridge/1',title='Integral families: Raghava, phase geometry and E8',
                   description='Exact reusable integral families join harmonic/binomial recurrences to cyclotomic phase filters and an explicit E8 Coxeter model.',
                   source_parent_commit=parent,
                   result_path='receipts/period_bridge/results.json',results_sha256=hashlib.sha256(raw).hexdigest(),
                   counts=dict(raghava_two_order_identities=len(identities),sine_pole_receipts=len(sine),
                               moment_bound_receipts=len(moments),kernel_bound_receipts=len(kernels),
                               exact_angle_specializations=len(angles),selected_series_partials=len(partials),
                               exact_raghava_receipts_replayed=len(replay),
                               small_filter_cases=results['cyclotomic']['bounded_exhaustive']['cases'],
                               small_filter_even_weight_comparisons=results['cyclotomic']['bounded_exhaustive']['exact_even_weight_comparisons'],
                               checked_transport_paths=results['transport']['checked_paths'],
                               independent_numeric_comparisons=len(identities)),
                   highlights=[
                       dict(label='Raghava construction',value='120 exact identities',
                            detail='Every selected-order pair through weight 33, with exact harmonic/zeta coefficients and rational tails; no independence claim.'),
                       dict(label='Phase reduction',value='240 integrals become two',
                            detail='The complete 264-branch fiber becomes one; its 240 primitive field conjugates become two with exact inclusion-exclusion.'),
                       dict(label='E8 integral cancellation',value='zero at weight two',
                            detail='The explicit 248-dimensional cyclic root-permutation-plus-Cartan model has a unique real Mellin zero for s>1 at s=2.'),
                       dict(label='Exact example',value='22537*pi^2/6773760',
                            detail='The real weight-two sum over the 240 primitive phases, checked against complete-source Bernoulli evaluation.'),
                       dict(label='Artifact-angle bridge',value='pi^2/352800',
                            detail='Raghava arcsine moment at t=2sin(pi/840); the refined angle divides this value by 264^2.'),
                       dict(label='Actual E8 geometry',value='240 roots; eight Coxeter orbits',
                            detail='Integer reflection construction, Coxeter order 30 and characteristic polynomial Phi30 are checked.'),
                       dict(label='Independent diagnostics',value='120 comparisons within exact tails',
                            detail='Decimal arithmetic at precision 200 with independently Euler-transformed zeta values; these numerical comparisons are not rigorous enclosures.')],
                   monograph='docs/PERIOD_BRIDGE_MONOGRAPH.md',
                   formal_kernel_verified=False,live_data_is_executable_upgrade=False,
                   limits=results['limitations'])
    return summary,raw


def main():
    summary,results_bytes = build()
    DESTINATION.mkdir(parents=True,exist_ok=True)
    (DESTINATION/'results.json').write_bytes(results_bytes)
    (DESTINATION/'summary.json').write_bytes(_bytes(summary))
    print(json.dumps(dict(schema=summary['schema'],**summary['counts'],
                          results_sha256=summary['results_sha256']),sort_keys=True))


if __name__ == '__main__':
    main()
