"""Discovery-free replay of preimages, compression and closure witnesses."""
from .elliptic_arithmetic import encode_point
from .elliptic_certificate_verifier import CheckBudget,fields,exact_int,model,checked_point
from .elliptic_subgroup_verifier import _check
from .divisor_square import WorkLimit


def coefficients(cs,width,bound):
    if type(cs) is not list or len(cs)!=width:return False
    return all(type(c) is int and -bound<=c<=bound for c in cs)


def combination(E,points,cs,budget):
    out=None
    for p,c in zip(points,cs):budget.charge(1);out=E.add(out,E.mul(p,c))
    return out


def reduce(E,points,rows,bound,budget):
    if type(rows) is not list or len(rows)>len(points):raise ValueError('bad reduction list')
    current=list(points)
    for row in rows:
        fields(row,'index coefficients');i=exact_int(row['index'],0,len(current)-1)
        others=current[:i]+current[i+1:];cs=row['coefficients']
        if not coefficients(cs,len(others),bound) or combination(E,others,cs,budget)!=current[i]:
            raise ValueError('invalid generator removal')
        current=others
    return current


def verify_saturation(cert,*,work_limit=2000000,node_limit=100000):
    try:
        exact_int(node_limit,1,100000);budget=CheckBudget(work_limit);budget.packet(cert)
        fields(cert,'schema curve source_points primes max_steps coefficient_bound membership_limit initial_reductions stages generators closed_primes status node_limit root_nodes complete_mordell_weil_group execution_verified')
        if cert['schema']!='pp-bounded-elliptic-saturation/1' or cert['complete_mordell_weil_group'] is not False or cert['execution_verified'] is not False:return False
        primes=cert['primes']
        if type(primes) is not list or not primes or any(type(p) is not int or p not in (2,3,5,7,11,13) for p in primes) or primes!=sorted(set(primes)):return False
        steps=exact_int(cert['max_steps'],1,16);bound=exact_int(cert['coefficient_bound'],0,4)
        exact_int(cert['membership_limit'],1,1000000);limit=exact_int(cert['node_limit'],1,100000)
        E=model(cert['curve']);source=cert['source_points']
        if type(source) is not list or len(source)>4:return False
        current=reduce(E,[checked_point(E,p) for p in source],cert['initial_reductions'],bound,budget)
        stages=cert['stages'];closed=[];used=0
        if type(stages) is not list or len(stages)>steps:return False
        for stage in stages:
            if closed==primes or len(current)>4:return False
            fields(stage,'preimage closure_witnesses reductions generators')
            packet=stage['preimage'];prime=next(p for p in primes if p not in closed)
            if type(packet) is not dict or packet.get('curve')!=cert['curve'] or packet.get('prime')!=prime or packet.get('source_points')!=[encode_point(p) for p in current] or packet.get('node_limit')!=limit-used:return False
            if not _check(packet,budget,min(node_limit-used,limit-used)):return False
            used+=packet['root_nodes'];raw=[checked_point(E,p) for p in packet['generators']]
            ws=stage['closure_witnesses']
            if ws is not None:
                if type(ws) is not list or len(ws)!=len(raw):return False
                for point,cs in zip(raw,ws):
                    if not coefficients(cs,len(current),bound) or combination(E,current,cs,budget)!=point:return False
                closed=sorted([*closed,prime])
            else:closed=[]
            current=reduce(E,raw,stage['reductions'],bound,budget)
            if stage['generators']!=[encode_point(p) for p in current]:return False
        status='closed' if closed==primes else 'width-limit' if len(current)>4 else 'step-limit'
        if status=='step-limit' and len(stages)!=steps:return False
        return (cert['status']==status and cert['closed_primes']==closed
            and all(type(p) is int for p in cert['closed_primes'])
            and cert['generators']==[encode_point(p) for p in current]
            and type(cert['root_nodes']) is int and cert['root_nodes']==used and used<=node_limit)
    except (ValueError,TypeError,KeyError,IndexError,ArithmeticError,WorkLimit):return False
