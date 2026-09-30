"""v15 cyclic common-centre criticality compiler.

Exact arithmetic classifier on a section-separated palette, plus a Wilson
hardware helper.  Formation theory is imported from the audited v15 package;
this module is the Forge-side executable interface.
"""
from __future__ import annotations
from dataclasses import dataclass
from itertools import combinations, product
from typing import Iterable, Optional, Tuple

@dataclass(frozen=True)
class PhaseResult:
    critical: bool
    proper_factor_rank: Optional[int]
    reason: str

def prime_power(n:int)->Optional[Tuple[int,int]]:
    if n<=1: raise ValueError('n must be > 1')
    x=n
    for p in range(2,int(n**0.5)+2):
        if x%p==0:
            e=0
            while x%p==0: x//=p; e+=1
            return (p,e) if x==1 else None
    return (n,1)

def classify(n:int,multiplicities:Iterable[int],section_separated:bool=True)->PhaseResult:
    m=tuple(int(x) for x in multiplicities if int(x)>0)
    if n<=1 or not m: raise ValueError('need n>1 and positive multiplicity')
    if any(x>=3 for x in m): return PhaseResult(False,1,'multiplicity >=3 gives one-factor diagonal collapse')
    if n%2==1 and any(x==2 for x in m): return PhaseResult(False,1,'2 is a unit modulo odd n')
    pp=prime_power(n); d=sum(x==2 for x in m); o=sum(x==1 for x in m)
    if pp is None: return PhaseResult(False,2,'non-prime-power scalar quotients regenerate in two factors')
    p,e=pp
    if p%2: return PhaseResult(True,None,'odd prime power with all-distinct support')
    if e==1:
        if d==0: return PhaseResult(True,None,'binary all-distinct critical state')
        if d==1 and o==0: return PhaseResult(True,None,'isolated binary double')
        return PhaseResult(False,2,'binary doubled coordinate detaches and regenerates in two factors')
    if d==0: return PhaseResult(True,None,'higher-2-power all-distinct critical state')
    if d==1:
        if not section_separated and o>0: raise ValueError('Schur section-incidence data required')
        return PhaseResult(True,None,'unique doubled species is 2-adically tethered')
    return PhaseResult(False,2,'two complementary factors restore multiple doubled reservoirs')

def triple_frontier(n:int,route_valencies=(30,60,60,60,60,60,60),section_separated=True):
    """Enumerate canonical multiplicity patterns {1,2} on all 3-route supports.

    Three routes suffice for complete Wilson spatial closure by the frozen
    35/35 route-triple theorem.  D_m ~= C_n gives n Fourier frequencies.
    """
    rows=[]
    for supp in combinations(range(7),3):
        degree=sum(route_valencies[i] for i in supp)
        for mult in product((1,2),repeat=3):
            ph=classify(n,mult,section_separated)
            rows.append({'support_indices':supp,'multiplicities':mult,'degree':degree,
                         'critical':ph.critical,'rho':ph.proper_factor_rank,'reason':ph.reason})
    return rows
