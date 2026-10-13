import math
import pytest
from perfectpower.arithmetic_transport import height_ballot,path_population,boundary_count,BallotPopulation

@pytest.mark.parametrize('p,q',[(2,3),(2,5),(3,5),(5,7)])
def test_iterative_counts_against_complete_path_language(p,q):
    for d in range(8):
        words=path_population(p,q,d,d)
        result=height_ballot(p,q,d)
        assert result['count']==len(words)==len(set(words))
        for word in words:
            u=v=0
            for bit in word:
                u+=bit;v+=not bit
                assert p**u<=q**v
            assert u==v==d

def test_retained_exact_large_count():
    result=height_ballot(2,3,32)
    assert result['count']==493058134611291081
    assert result['unrestricted_count']==math.comb(64,32)

def test_every_exact_rank_and_condition_against_enumeration():
    for d in range(7):
        words=path_population(2,3,d,d);pop=BallotPopulation(2,3,d)
        assert pop.count==len(words)
        for i,word in enumerate(words):
            assert pop.unrank(i)==word and pop.rank(word)==i
            for k in range(len(word)+1):
                prefix=word[:k]
                assert pop.conditional_count(prefix)==sum(x[:k]==prefix for x in words)
        assert pop.sample(42)==pop.sample(42)
        with pytest.raises(ValueError):pop.unrank(pop.count)

def test_invalid_and_empty_prefixes():
    pop=BallotPopulation(2,3,4)
    assert pop.conditional_count((True,))==0
    with pytest.raises(ValueError):pop.rank((True,)*8)
    with pytest.raises(ValueError):pop.conditional_count((1,))

def test_boundary_against_actual_integer_edges():
    for N in (32,100,257):
        for d in range(2,6):
            powers={a**d for a in range(1,N+1) if a**d<=N}
            edges=sum((n in powers)!=(p*n in powers) for p in (2,3,5,7) for n in range(1,N//p+1))
            assert boundary_count(N,d)['boundary']==edges

@pytest.mark.parametrize('p,q,d',[(4,5,3),(3,2,3),(2,3,-1),(2,3,4097),(2,3,True)])
def test_invalid_domains(p,q,d):
    with pytest.raises(ValueError):height_ballot(p,q,d)
