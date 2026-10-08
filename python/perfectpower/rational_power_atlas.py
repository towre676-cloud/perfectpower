"""Denominator-aware power equations, complete Hensel/CRT chart domains and patches.

For Q=F/L, x=r+L*n transports y^d=Q(x) to y^d=G_r(n).
Congruences are transported at L*m, including primes dividing L. Bounded
source scans retain every chart, both smooth orientations and singular children.
"""
from fractions import Fraction
from math import comb, lcm
import json
from .integer_valued_polynomial import normalize
from . import polyalg as P
from .bounded_residue_patch import terms_checked, evaluate
from .residue_determinant import integer, auxiliary_packet
from .residue_atlas import atlas_packet, verify_atlas, _parameter, _canonical_equal, _bounds
from .residue_atlas_product import product_packet, _blocks
from .residue_atlas_intersection_factored import (intersect_atlases, verify_intersection,
    intersection_population, intersection_select, intersection_rank)


def _pullback(terms, r, step):
    data = {}
    for c,i,j in terms:
        for k in range(i+1):
            data[k,j] = data.get((k,j),0)+c*comb(i,k)*r**(i-k)*step**k
    return terms_checked([[c,i,j] for (i,j),c in data.items()])


def _inputs(coefficients, exponent, factors, restrictions):
    F,L,canonical = normalize(coefficients)
    exponent = _parameter(exponent,'exponent',12)
    if exponent < 2 or len(F)>13 or L>32:
        raise ValueError('power exponent 2..12, polynomial degree <=12 and denominator <=32 required')
    if not isinstance(factors,list) or not 1<=len(factors)<=8:
        raise ValueError('one through eight prime-power factors required')
    factors = sorted(factors)
    primes=[]
    for pair in factors:
        if not isinstance(pair,list) or len(pair)!=2:
            raise ValueError('factors are [prime,exponent]')
        p,k=pair;atlas_packet([[1,0,1]],p,k);primes.append(p)
    if len(set(primes))!=len(primes):raise ValueError('distinct base primes required')
    if restrictions is None:restrictions=[]
    if not isinstance(restrictions,list) or len(restrictions)>4:
        raise ValueError('at most four additional source congruences required')
    checked=[]
    for item in restrictions:
        if not isinstance(item,dict) or set(item)!={'terms','prime','exponent'}:
            raise ValueError('restriction needs terms, prime, exponent')
        terms=terms_checked(item['terms'])
        if not terms:raise ValueError('nonzero restriction required')
        atlas_packet(terms,item['prime'],item['exponent'])
        checked.append({'terms':terms,'prime':item['prime'],'exponent':item['exponent']})
    checked=json.loads(json.dumps(sorted(checked,key=lambda a:json.dumps(a,sort_keys=True))))
    return F,L,canonical,exponent,factors,checked


def _chart_data(F,L,d):
    rows=[]
    for r in range(L):
        if int(P.evaluate(F,r))%L:continue
        expanded=P.compose_linear(P.poly(F),r,L)
        if any(v.denominator!=1 or int(v)%L for v in expanded):
            raise ArithmeticError('integral chart coefficient transport failed')
        G=[int(v)//L for v in expanded]
        terms=terms_checked([[c,i,0] for i,c in enumerate(G) if c]+[[-1,0,d]])
        rows.append({'residue':r,'step':L,'quotient_coefficients':G,'equation_terms':terms})
    return rows


def power_atlas(coefficients, exponent, factors, *, restrictions=None, explicit_limit=4096):
    F,L,canonical,d,factors,restrictions=_inputs(coefficients,exponent,factors,restrictions)
    limit=_parameter(explicit_limit,'explicit_limit',100000)
    charts=[]
    for row in _chart_data(F,L,d):
        inputs=[product_packet(row['equation_terms'],factors,explicit_limit=limit)]
        inputs += [atlas_packet(_pullback(a['terms'],row['residue'],L),a['prime'],a['exponent']) for a in restrictions]
        charts.append(dict(row,cover=intersect_atlases(inputs,explicit_limit=limit)))
    period=lcm(*(p**k for p,k in factors),*(a['prime']**a['exponent'] for a in restrictions))
    return {'schema':'pp-rational-power-atlas/1','rational_coefficients':canonical,
            'numerator':F,'denominator':L,'exponent':d,'factors':factors,'restrictions':restrictions,
            'charts':charts,'equation_period':lcm(*(p**k for p,k in factors)),'parameter_period':period,'x_period':L*period,'y_period':period,
            'explicit_limit':limit,'complete_integer_domain':True,'complete_modular_cover':True,
            'global_obstruction':not charts or all(c['cover']['global_obstruction'] for c in charts),
            'execution_verified':False,'global_height_bound':False}


def verify_power_atlas(packet):
    """Independent source/chart identities and full local cover replay."""
    try:
        fields={'schema','rational_coefficients','numerator','denominator','exponent','factors',
          'restrictions','charts','equation_period','parameter_period','x_period','y_period','explicit_limit',
          'complete_integer_domain','complete_modular_cover','global_obstruction','execution_verified','global_height_bound'}
        if not isinstance(packet,dict) or set(packet)!=fields or packet['schema']!='pp-rational-power-atlas/1':return False
        F,L,canonical,d,factors,restrictions=_inputs(packet['rational_coefficients'],packet['exponent'],packet['factors'],packet['restrictions'])
        limit=_parameter(packet['explicit_limit'],'explicit_limit',100000)
        if not _canonical_equal([F,L,canonical,factors,restrictions],
          [packet['numerator'],packet['denominator'],packet['rational_coefficients'],packet['factors'],packet['restrictions']]):return False
        expected=_chart_data(F,L,d)
        if len(expected)!=len(packet['charts']):return False
        for row,actual in zip(expected,packet['charts']):
            if set(actual)!=set(row)|{'cover'} or not _canonical_equal(row,{k:actual[k] for k in row}):return False
            cover=actual['cover']
            if not verify_intersection(cover) or cover['explicit_limit']!=limit:return False
            conditions={(p,k,json.dumps(row['equation_terms'])) for p,k in factors}
            conditions|={(a['prime'],a['exponent'],json.dumps(_pullback(a['terms'],row['residue'],L))) for a in restrictions}
            supplied={(a['prime'],a['exponent'],json.dumps(a['terms'])) for a in cover['constraints']}
            if supplied!=conditions:return False
        period=lcm(*(p**k for p,k in factors),*(a['prime']**a['exponent'] for a in restrictions))
        return (_canonical_equal([packet['equation_period'],packet['parameter_period'],packet['x_period'],packet['y_period']],[lcm(*(p**k for p,k in factors)),period,L*period,period])
          and packet['complete_integer_domain'] is True and packet['complete_modular_cover'] is True
          and packet['global_obstruction'] is (not expected or all(c['cover']['global_obstruction'] for c in packet['charts']))
          and packet['execution_verified'] is False and packet['global_height_bound'] is False)
    except (ValueError,TypeError,KeyError,IndexError,OverflowError,ArithmeticError):return False


def _prepared(packet,bounds):
    if not verify_power_atlas(packet):raise ValueError('complete rational-power atlas required')
    return _bounds(bounds)


def _parameter_bounds(bounds,r,L):
    (lo,hi),ys=bounds
    return [[-((r-lo)//L),(hi-r)//L],ys]


def _populations(packet,bounds,work_limit):
    for row in packet['charts']:
        b=_parameter_bounds(bounds,row['residue'],packet['denominator'])
        count=0 if b[0][0]>b[0][1] else intersection_population(row['cover'],b,work_limit=work_limit)['count']
        yield row,b,count


def power_population(packet,bounds,*,work_limit=200000):
    bounds=_prepared(packet,bounds);budget=_parameter(work_limit,'work_limit',2000000)
    rows=[{'residue':row['residue'],'parameter_bounds':b,'count':count} for row,b,count in _populations(packet,bounds,budget)]
    return {'bounds':bounds,'count':sum(r['count'] for r in rows),'charts':rows,
      'order':'integral residue chart; prime-group tuple; parameter n then y ascending',
      'execution_verified':False,'global_height_bound':False}


def power_select(packet,bounds,index,*,work_limit=200000):
    bounds=_prepared(packet,bounds);budget=_parameter(work_limit,'work_limit',2000000)
    index=integer(index,1024)
    if index<0:raise IndexError('negative rank')
    for row,b,count in _populations(packet,bounds,budget):
        if index<count:
            n,y=intersection_select(row['cover'],b,index,work_limit=budget)
            return [row['residue']+packet['denominator']*n,y]
        index-=count
    raise IndexError('rank outside complete population')


def power_rank(packet,bounds,point,*,work_limit=200000):
    bounds=_prepared(packet,bounds);budget=_parameter(work_limit,'work_limit',2000000)
    if not isinstance(point,list) or len(point)!=2:raise ValueError('two integer coordinates required')
    x,y=[integer(v,256) for v in point];L=packet['denominator']
    if not bounds[0][0]<=x<=bounds[0][1] or not bounds[1][0]<=y<=bounds[1][1]:raise ValueError('point outside original bounds')
    offset=0
    for row,b,count in _populations(packet,bounds,budget):
        if x%L==row['residue'] and count:
            return offset+intersection_rank(row['cover'],b,[(x-row['residue'])//L,y],work_limit=budget)
        offset+=count
    raise ValueError('point fails original integer/chart conditions')


def power_scan(packet,bounds,*,candidate_limit=4096,work_limit=200000):
    bounds=_prepared(packet,bounds);limit=_parameter(candidate_limit,'candidate_limit',100000)
    population=power_population(packet,bounds,work_limit=work_limit)
    if population['count']>limit:raise ValueError('complete population exceeds scan budget; no partial list')
    points=[];by_chart=[];L=packet['denominator']
    for row,b,count in _populations(packet,bounds,work_limit):
        found=[]
        if count:
            m=row['cover']['modulus']
            for a,c,nx,ny in _blocks(row['cover'],b,work_limit):
                nf=b[0][0]+(a-b[0][0])%m;yf=b[1][0]+(c-b[1][0])%m
                for i in range(nx):
                    for j in range(ny):
                        n,y=nf+i*m,yf+j*m;x=row['residue']+L*n
                        if int(P.evaluate(packet['numerator'],x))==L*y**packet['exponent']:
                            found.append([x,y]);points.append([x,y])
        by_chart.append({'residue':row['residue'],'points':sorted(found)})
    return {'points':sorted(points),'charts':by_chart,'bounds':bounds,
      'candidates_checked':population['count'],'complete_in_box':True,
      'restrictions':'original modular conditions, not extra exact equations',
      'execution_verified':False,'global_height_bound':False}


def power_patch(packet,bounds,*,candidate_limit=4096,work_limit=200000,exponents=None):
    """Complete bounded patch with every chart/lift branch and covering relations."""
    scan=power_scan(packet,bounds,candidate_limit=candidate_limit,work_limit=work_limit)
    if len(scan['points'])>64:raise ValueError('complete patch exceeds 64-point auxiliary budget')
    exponents=[[0,0],[1,0],[0,1],[2,0]] if exponents is None else exponents
    auxiliary=auxiliary_packet(scan['points'],exponents) if scan['points'] else None
    orientations={'vertical':0,'horizontal':0,'singular':0,'obstructed':0}
    for chart in packet['charts']:
        for atlas in chart['cover']['constraints']:
            for level in atlas['levels']:
                for node in level['nodes']:
                    orientations[node['chart']]+=1;orientations['obstructed']+=node['obstructed']
    return {'schema':'pp-rational-power-patch/1','atlas':packet,'scan':scan,
      'lift_orientations':orientations,'auxiliary':auxiliary,'complete_in_box':True,
      'execution_verified':False,'global_height_bound':False}


def verify_power_patch(packet):
    from .residue_determinant import verify_auxiliary
    try:
        if set(packet)!={'schema','atlas','scan','lift_orientations','auxiliary','complete_in_box','execution_verified','global_height_bound'}:
            return False
        if packet['schema']!='pp-rational-power-patch/1' or not verify_power_atlas(packet['atlas']):return False
        atlas=packet['atlas'];scan=power_scan(atlas,packet['scan']['bounds'],candidate_limit=100000,work_limit=2000000)
        if not _canonical_equal(scan,packet['scan']):return False
        expected={'vertical':0,'horizontal':0,'singular':0,'obstructed':0}
        for c in atlas['charts']:
            for a in c['cover']['constraints']:
                for level in a['levels']:
                    for node in level['nodes']:
                        expected[node['chart']]+=1;expected['obstructed']+=node['obstructed']
        if not _canonical_equal(expected,packet['lift_orientations']) or len(scan['points'])>64:return False
        aux=packet['auxiliary']
        if scan['points']:
            if aux is None or not _canonical_equal(aux['points'],scan['points']) or not verify_auxiliary(aux):return False
        elif aux is not None:return False
        return packet['complete_in_box'] is True and packet['execution_verified'] is False and packet['global_height_bound'] is False
    except (ValueError,TypeError,KeyError,IndexError,OverflowError,ArithmeticError):return False


def native_power_atlas(packet,bounds):
    """Concrete transported covers, original-coordinate populations and complete patches."""
    import hashlib,re
    from .residue_atlas_intersection_factored import native_intersection
    from .bounded_residue_patch import formula,_finset
    if not verify_power_atlas(packet):raise ValueError('complete rational-power atlas required')
    bounds=_bounds(bounds);L=packet['denominator']
    if len(packet['charts'])>8:raise ValueError('native power chart count exceeds eight')
    source_terms=terms_checked([[c,i,0] for i,c in enumerate(packet['numerator']) if c]+[[-L,0,packet['exponent']]])
    imports={'import PerfectPower.RationalPowerAtlas'};programs=[];names=[]
    # Native local atlas generation uses nonempty bounds; no-coordinate charts
    # are replayed on a harmless singleton, then counted on the actual empty interval.
    for row in packet['charts']:
        b=_parameter_bounds(bounds,row['residue'],L)
        replay_bounds=b if b[0][0]<=b[0][1] else [[0,0],b[1]]
        native=native_intersection(row['cover'],replay_bounds)
        ns=re.findall(r'^namespace (Intersection_\w+)$',native,re.M)[-1]
        names.append(ns+'.stage'+str(len(row['cover']['locals'])-1))
        imports.update(line for line in native.splitlines() if line.startswith('import '))
        programs.append('\n'.join(line for line in native.splitlines() if not line.startswith('import ')))
    tag=hashlib.sha256(json.dumps([packet,bounds],sort_keys=True).encode()).hexdigest()[:16];ns='PowerCharts_'+tag
    lines=sorted(imports)+programs+[f'namespace {ns}',
      'open PerfectPower.RationalPowerAtlas',
      'open PerfectPower.ResidueAtlas (Bounds)',
      f'def F (x y : ℤ) : ℤ := {formula(source_terms)}',
      f'def bounds : Bounds := (({bounds[0][0]},{bounds[0][1]}),({bounds[1][0]},{bounds[1][1]}))']
    for i,(row,name) in enumerate(zip(packet['charts'],names)):
        r=row['residue'];lines += [f'def G{i} (n y : ℤ) : ℤ := {formula(row["equation_terms"],"n","y")}',
          f'theorem identity{i} (n y : ℤ) : F ({r}+{L}*n) y={L}*G{i} n y := by unfold F G{i}; ring',
          f'def chart{i} : ChartPacket F G{i} {L} {r} := ⟨by norm_num,identity{i}⟩',
          f'theorem source_transport{i} (n y : ℤ) : F ({r}+{L}*n) y=0 ↔ G{i} n y=0 := chart{i}.source_iff n y',
          f'theorem denominator_transport{i} (m n y : ℤ) : {L}*m ∣ F ({r}+{L}*n) y ↔ m ∣ G{i} n y := chart{i}.congruence_iff m n y',
          f'def candidates{i} := chartCandidates {name} bounds {L} {r}',
          f'theorem count{i} : candidates{i}.card={power_population(packet,bounds)["charts"][i]["count"]} := by',
          f'  rw [candidates{i},chart_count {name} bounds {L} {r} (by norm_num)]; decide +kernel',
          f'#print axioms identity{i}',f'#print axioms source_transport{i}',f'#print axioms denominator_transport{i}',f'#print axioms count{i}']
    if len(names)>0:
        k=len(names);period=packet['parameter_period']
        rows=[c['residue'] for c in packet['charts']]
        predicates=[]
        for name in names:
            native_ns=name.split('.')[0]
            # Recover the literal predicate type of the final stage from the emitted source.
            source=next(s for s in programs if 'namespace '+native_ns+'\n' in s)
            pattern=r'^def '+re.escape(name.split('.')[1])+r' : CoverPacket \(fun x y => (.*)\) \d+ :='
            predicates.append(re.search(pattern,source,re.M).group(1))
        lines += [f'def residue (i : Fin {k}) : ℤ := '+''.join(f'if i.val={j} then {r} else ' for j,r in enumerate(rows[:-1]))+str(rows[-1]),
          f'def P (i : Fin {k}) (x y : ℤ) : Prop := '+''.join(f'if i.val={j} then ({pred}) else ' for j,pred in enumerate(predicates[:-1]))+'('+predicates[-1]+')',
          f'def cover : (i : Fin {k}) → PerfectPower.ResidueAtlasIntersectionFactored.CoverPacket (P i) {period} := '+''.join(f'Fin.cases {name} (' for name in names)+'(fun i => Fin.elim0 i)'+')'*k]
        lines += [f'theorem residue_canonical : ∀ i : Fin {k}, 0≤residue i ∧ residue i<{L} := by decide +kernel',
          'theorem residue_injective : Function.Injective residue := by decide +kernel',
          f'def allCandidates := familyCandidates cover bounds {L} residue',
          f'theorem population_checked : allCandidates.card={power_population(packet,bounds)["count"]} := by',
          f'  rw [allCandidates,family_count cover bounds {L} residue (by norm_num) residue_canonical residue_injective]; decide +kernel',
          '#print axioms residue_canonical','#print axioms residue_injective','#print axioms population_checked']
    if not names:
        from .residue_atlas import _period_proof
        lines += [f'theorem source_periodic (x y : ℤ) : F x y % {L}=F (x%{L}) (y%{L}) % {L} := by',
          f'  change Int.ModEq {L} (F x y) (F (x%{L}) (y%{L}))',
          f'  have hx : Int.ModEq {L} x (x%{L}) := (Int.mod_modEq x {L}).symm',
          f'  have hy : Int.ModEq {L} y (y%{L}) := (Int.mod_modEq y {L}).symm',
          '  unfold F',f'  exact {_period_proof(source_terms)}',
          f'def emptyCover : PerfectPower.ResidueAtlas.AtlasPacket F {L} := ⟨by norm_num,∅,by decide +kernel,source_periodic⟩',
          'theorem no_integer_solution (x y : ℤ) : F x y≠0 := emptyCover.empty_obstruction rfl x y',
          '#print axioms source_periodic','#print axioms no_integer_solution']
    if (bounds[0][1]-bounds[0][0]+1)*(bounds[1][1]-bounds[1][0]+1)<=1024:
        patch=power_patch(packet,bounds)
        restriction=' ∧ '.join(f'({formula(a["terms"])}) % {a["prime"]**a["exponent"]}=0' for a in packet['restrictions']) or 'True'
        lines += [f'def accepts (x y : ℤ) : Prop := F x y=0 ∧ ({restriction})',
          'instance : DecidablePred (fun z : ℤ×ℤ => accepts z.1 z.2) := fun z => by unfold accepts; infer_instance',
          f'def sourcePoints : Finset (ℤ×ℤ) := ((Finset.Icc ({bounds[0][0]}) ({bounds[0][1]})).product (Finset.Icc ({bounds[1][0]}) ({bounds[1][1]}))).filter fun z => accepts z.1 z.2',
          f'def points : Finset (ℤ×ℤ) := {_finset(patch["scan"]["points"])}',
          'theorem points_checked : sourcePoints=points := by decide +kernel',
          f'theorem points_complete (x y : ℤ) : (x,y) ∈ points ↔ {bounds[0][0]}≤x ∧ x≤{bounds[0][1]} ∧ {bounds[1][0]}≤y ∧ y≤{bounds[1][1]} ∧ accepts x y := by',
          '  rw [← points_checked]; simp only [sourcePoints,Finset.mem_filter,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_Icc]; tauto',
          '#print axioms points_checked','#print axioms points_complete']
        if patch['auxiliary']:
            a=patch['auxiliary'];center=a['center']
            for j,c in enumerate(a['kernel']['relations']):
                terms=[[v,*e] for v,e in zip(c,a['exponents']) if v]
                lines += [f'def auxiliary{j} (x y : ℤ) : ℤ := {formula(terms,"x-("+str(center[0])+")","y-("+str(center[1])+")")}',
                  f'theorem auxiliary{j}_values : ∀ z ∈ points, auxiliary{j} z.1 z.2=0 := by decide +kernel',
                  f'theorem auxiliary{j}_covers (x y : ℤ) (h : {bounds[0][0]}≤x ∧ x≤{bounds[0][1]} ∧ {bounds[1][0]}≤y ∧ y≤{bounds[1][1]} ∧ accepts x y) : auxiliary{j} x y=0 := auxiliary{j}_values (x,y) ((points_complete x y).mpr h)',
                  f'#print axioms auxiliary{j}_values',f'#print axioms auxiliary{j}_covers']
    lines += [f'end {ns}'];return '\n'.join(lines)+'\n'
