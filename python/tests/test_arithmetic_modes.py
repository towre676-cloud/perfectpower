from fractions import Fraction
from itertools import permutations
from collections import Counter
import pytest
from perfectpower.arithmetic_modes import Mode,ModePopulation,spin_multiply,signed_ballot,SlopeAtlas

def enumerate_paths(pop):
    counts=[0]*len(pop.modes);answers=[]
    def visit(word,value,q):
        if not pop.admissible(value):return
        if len(word)==pop.length:
            if q in pop.accepting:answers.append(tuple(word))
            return
        for j,m in enumerate(pop.modes):
            t=pop.transition[q][j]
            if counts[j]<m.quota and t is not None:
                counts[j]+=1
                visit(word+[j],value*Fraction(m.prime if m.direction==1 else 1,1 if m.direction==1 else m.prime),t)
                counts[j]-=1
    visit([],pop.start,pop.controller['initial'])
    return answers

@pytest.mark.parametrize('d',[1,2,3,4])
def test_counts_ranks_spin_and_turns_against_complete_language(d):
    pop=ModePopulation([Mode(2,1,d,1),Mode(3,-1,d,2)],3**d,3**d)
    words=enumerate_paths(pop);assert pop.count==len(words)
    hist=Counter();turns=Counter()
    for i,word in enumerate(words):
        assert pop.unrank(i)==word and pop.rank(word)==i
        state=(0,0)
        for j in word:state=spin_multiply((0,pop.modes[j].axis),state)
        hist[state]+=1;turns[sum(a!=b for a,b in zip(word,word[1:]))]+=1
        for k in range(len(word)+1):assert pop.conditional_count(word[:k])==sum(w[:k]==word[:k] for w in words)
    result=pop.spin_histogram()
    assert result['phase_population']=={f'{p}:{a}':str(n) for (p,a),n in hist.items()}
    assert pop.turn_polynomial()['coefficients']=={str(k):str(v) for k,v in sorted(turns.items())}

def test_multi_mode_rational_height_and_controller():
    modes=[Mode(2,1,2,1),Mode(3,-1,2,2),Mode(5,1,1,3)]
    controller={'initial':0,'accepting':[0,1,2],'transitions':[[None,1,2],[0,None,2],[0,1,None]]}
    for integral in (False,True):
        for cap in (9,45,180):
            pop=ModePopulation(modes,9,cap,integral,controller)
            assert pop.count==len(enumerate_paths(pop))
            for i in range(pop.count):assert pop.rank(pop.unrank(i))==i

def test_exact_height_revives_and_cancels_spin():
    modes=[Mode(2,1,1,1),Mode(3,-1,1,2)]
    unrestricted=ModePopulation(modes,3,6)
    tight=ModePopulation(modes,3,3)
    assert unrestricted.count==2 and unrestricted.spin_histogram()['exact_cancellation']
    assert tight.count==1 and tight.spin_histogram()['coherence_squared']=='1'
    even=ModePopulation([Mode(2,1,2,1),Mode(3,-1,2,2)],9,9)
    assert even.count==2 and even.spin_histogram()['exact_cancellation']

def test_minimum_height_matches_all_paths():
    modes=[Mode(2,1,2),Mode(3,-1,2),Mode(5,1,1)]
    pop=ModePopulation(modes,9,None,False)
    peaks=[]
    for word in enumerate_paths(pop):
        n=pop.start;peak=max(n.numerator,n.denominator)
        for j in word:
            m=modes[j];n*=Fraction(m.prime if m.direction==1 else 1,1 if m.direction==1 else m.prime);peak=max(peak,n.numerator,n.denominator)
        peaks.append(peak)
    assert pop.height_profile()==min(peaks)

def test_one_sweep_matches_all_separate_height_queries():
    for d in range(1,5):
        modes=[Mode(2,1,d,1),Mode(3,-1,d,2)]
        unbounded=ModePopulation(modes,3**d)
        for row in unbounded.height_filtration():
            pop=ModePopulation(modes,3**d,int(row['height']))
            assert int(row['count'])==pop.count
            assert row['coherence_squared']==pop.spin_histogram()['coherence_squared']
            assert row['exact_cancellation']==pop.spin_histogram()['exact_cancellation']
        assert unbounded.height_profile()==int(unbounded.height_filtration()[0]['height'])

def test_rational_multimode_filtration():
    modes=[Mode(2,1,2,1),Mode(3,-1,2,2),Mode(5,1,1,3)]
    pop=ModePopulation(modes,1,None,False)
    for row in pop.height_filtration():
        other=ModePopulation(modes,1,row['height'],False)
        assert str(other.count)==row['count'] and other.spin_histogram()['coherence_squared']==row['coherence_squared']

@pytest.mark.parametrize('bad',[1.5,True])
def test_inexact_height_rejected(bad):
    with pytest.raises(ValueError):ModePopulation([Mode(2,1,1)],1,bad)

def test_signed_recurrence_against_spin_histogram():
    for p,q in ((2,3),(2,5),(3,5)):
        for d in range(1,8):
            pop=ModePopulation([Mode(p,1,d,1),Mode(q,-1,d,2)],q**d,q**d)
            spin=pop.spin_histogram()['amplitude_pauli_coefficients']
            norm=sum(int(a['real'])**2+int(a['imaginary'])**2 for a in spin.values())
            assert norm==signed_ballot(p,q,d)**2

def test_node_budget_is_explicit_failure():
    with pytest.raises(ValueError,match='budget'):ModePopulation([Mode(2,1,6),Mode(3,-1,6)],729,729,max_nodes=2)

def test_empty_and_zero_horizon():
    blocked=ModePopulation([Mode(2,1,1)],2,1);assert blocked.count==0 and blocked.spin_histogram()['coherence_squared']=='0'
    empty=ModePopulation([Mode(2,1,0)],1,1);assert empty.count==1 and empty.unrank(0)==()

def test_pauli_group_associativity_and_inverses():
    elements=[(p,a) for p in range(4) for a in range(4)]
    for a in elements:
        assert any(spin_multiply(a,b)==(0,0) for b in elements)
        for b in elements:
            for c in elements:assert spin_multiply(spin_multiply(a,b),c)==spin_multiply(a,spin_multiply(b,c))

def test_symbolic_chambers_include_exact_walls():
    for d in (2,4,8):
        atlas=SlopeAtlas(d)
        for p,q in ((2,3),(2,4),(2,8),(3,9),(5,7),(3,3),(2,257)):
            pop=ModePopulation([Mode(p,1,d,1),Mode(q,-1,d,2)],q**d,q**d) if p in (2,3,5) and q in (3,7,257) and p<q else None
            # Independent enumeration of rectangle states for arbitrary bases.
            from functools import lru_cache
            @lru_cache(None)
            def count(u,v):
                if p**u>q**v:return 0
                if u==v==0:return 1
                return (count(u-1,v) if u else 0)+(count(u,v-1) if v else 0)
            query=atlas.query(p,q);assert int(query['count'])==count(d,d)
            if pop is not None:assert int(query['count'])==pop.count

def test_atlas_signed_prime_queries():
    for d in (1,2,8,16):
        atlas=SlopeAtlas(d)
        for p,q in ((2,3),(2,5),(3,5),(5,7),(11,13)):
            assert int(atlas.query(p,q)['signed'])==signed_ballot(p,q,d)
