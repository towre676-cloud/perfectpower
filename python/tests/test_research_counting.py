import itertools
import random
import pytest
from perfectpower.research_counting import MonomialPopulation, ResiduePopulation, digit_sumset
from perfectpower.divisor_square import WorkLimit


def test_monomial_exhaustive_rank_degree_and_histogram():
    rng = random.Random(22763)
    for _ in range(80):
        gs = [[rng.randrange(5) for _ in range(3)] for _ in range(rng.randrange(1, 5))]
        all_vectors = sorted({x for g in gs for x in itertools.product(*(range(b + 1) for b in g))})
        p = MonomialPopulation(gs)
        assert p.count == len(all_vectors)
        assert p.histogram() == [sum(sum(v) == d for v in all_vectors) for d in range(max(map(sum, gs)) + 1)]
        for degree in (None, rng.randrange(13)):
            pop = MonomialPopulation(gs, degree)
            values = [x for x in all_vectors if degree is None or sum(x) == degree]
            assert pop.count == len(values)
            for r, v in enumerate(values):
                assert pop.select(r) == list(v)
                assert pop.rank(v) == r


def test_huge_monomial_population_without_enumeration():
    bound = 10 ** 30
    pop = MonomialPopulation([[bound, bound, bound]], degree=bound)
    assert pop.count == (bound + 1) * (bound + 2) // 2
    for r in (0, pop.count // 2, pop.count - 1):
        assert pop.rank(pop.select(r)) == r
    with pytest.raises(WorkLimit):
        pop.histogram()


def test_crt_against_brute_force_noncoprime_negative_intervals():
    rng = random.Random(12)
    for _ in range(100):
        constraints = [{'modulus': m, 'allowed': rng.sample(range(m), rng.randrange(m + 1))} for m in (4, 6, 5)]
        values = [x for x in range(-100, 101) if all(x % c['modulus'] in c['allowed'] for c in constraints)]
        pop = ResiduePopulation(-100, 100, constraints)
        assert pop.count == len(values)
        for r, x in enumerate(values):
            assert pop.select(r) == x
            assert pop.rank(x) == r


def test_digit_sumset_counts_values_and_representations_separately():
    spec = {'left': {'base': 3, 'digits': [0, 1], 'length': 3}, 'right': {'base': 4, 'digits': [0, 1], 'length': 3}, 'stop': 40}
    left = [sum(d * 3 ** i for i, d in enumerate(v)) for v in itertools.product((0, 1), repeat=3)]
    right = [sum(d * 4 ** i for i, d in enumerate(v)) for v in itertools.product((0, 1), repeat=3)]
    pairs = [x + y for x in left for y in right if x + y < 40]
    result = digit_sumset(spec)
    assert result['values'] == sorted(set(pairs))
    assert int(result['representation_count']) == len(pairs)
    assert int(result['collision_excess']) == len(pairs) - len(set(pairs)) > 0


def test_invalid_and_limited_queries():
    for gs in ([[True, 0]], [[-1, 0]], [[1], [1, 2]]):
        with pytest.raises(ValueError): MonomialPopulation(gs)
    with pytest.raises(ValueError): MonomialPopulation([[2]]).select(3)
    with pytest.raises(ValueError): MonomialPopulation([[2]]).rank([3])
    with pytest.raises(WorkLimit): MonomialPopulation([[5, 5, 5]], 5, 1)
    with pytest.raises(WorkLimit): ResiduePopulation(0, 100, [{'modulus': 4, 'allowed': [0, 1]}], 1)


def test_codimension_three_type_two_log_concavity_instances():
    generators = [x for x in itertools.product(range(6), repeat=3) if sum(x) == 5]
    for a, b in itertools.combinations(generators, 2):
        h = MonomialPopulation([a, b]).histogram()
        assert all(h[i] ** 2 >= h[i - 1] * h[i + 1] for i in range(1, len(h) - 1))
