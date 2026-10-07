"""Source-driven eclipse-station arithmetic and declared overlap schedules.

Months are integer lunation indices. This is not a physical visibility engine.
"""
from collections import Counter
from fractions import Fraction
from .dresden import _integer, long_count_days
from .semilinear_domains import count_domain, select, contains


def station_audit(data):
    rows=data['stations']
    if len(rows)!=69 or [r['station'] for r in rows]!=list(range(1,70)):
        raise ValueError('69 ordered station records required')
    months=[_integer(r['month']) for r in rows]
    days=[_integer(r['corrected_day']) for r in rows]
    if any(a>=b for a,b in zip([0]+months,months)) or any(a>=b for a,b in zip([0]+days,days)):
        raise ValueError('strictly increasing station months and days required')
    if any(r['classification'] not in ('intended','contrived') for r in rows):
        raise ValueError('source classification required')
    increments=[d-p for p,d in zip([0]+days,days)]
    if increments!=[r['increment'] for r in rows]:
        raise ValueError('increments do not match cumulative totals')
    raw=[]
    for r in data['selected_raw_cumulative_readings']:
        target=days[r['station']-1]
        raw.append({'station':r['station'],'raw_days':long_count_days(r['digits']),
                    'correction':r['correction'],
                    'identity_holds':long_count_days(r['digits'])+r['correction']==target})
    return {'station_count':len(rows),'last_month':months[-1],'last_day':days[-1],
            'increment_counts':dict(sorted(Counter(increments).items())),
            'month_increment_counts':dict(sorted(Counter(b-a for a,b in zip([0]+months,months)).items())),
            'classification_counts':dict(Counter(r['classification'] for r in rows)),
            'published_increment_discrepancies':[{'station':r['station'],'reported':r['reported_increment'],'derived':v}
                for r,v in zip(rows,increments) if r['reported_increment']!=v],
            'raw_corrections':raw, 'raw_corrections_hold':all(r['identity_holds'] for r in raw)}


def standard_table_candidates(data):
    """Two specifically proposed placements of the missing +1-day increment."""
    station_audit(data)
    if data['stations'][-1]['corrected_day']!=11959:
        raise ValueError('11959-day surviving model required')
    outputs=[]
    for threshold in (7619,7796):
        rows=[];previous=0
        for r in data['stations']:
            d=r['corrected_day']+(r['corrected_day']>=threshold)
            rows.append({**r,'corrected_day':d,'increment':d-previous});previous=d
        outputs.append({'shift_at_surviving_day':threshold,'first_shifted_day':threshold+1,
                        'status':'Justeson-Lowry proposed alternative; not surviving manuscript',
                        'stations':rows,'last_day':previous})
    return outputs


def overlap_schedule(station_months, restart_steps):
    """Exact distinct prediction months for repeated declared restart patterns.

    Every supplied station s is placed at base+s. Bases begin at zero, follow
    the supplied restart steps, and repeat their sum T indefinitely. Overlapping
    tables are deduplicated; earliest activation for each residue is retained.
    """
    stations=sorted(set(_integer(s) for s in station_months))
    steps=[_integer(s) for s in restart_steps]
    if not stations or stations[0]<0 or not steps or min(steps)<=0 or len(stations)*len(steps)>100000:
        raise ValueError('bounded stations and positive restart steps required')
    period=sum(steps);bases=[0]
    for step in steps[:-1]:bases.append(bases[-1]+step)
    first={};origins={}
    for i,b in enumerate(bases):
        for s in stations:
            day=b+s;residue=day%period
            first[residue]=min(first.get(residue,day),day)
            origins.setdefault(residue,[]).append({'base_phase':i,'station_month':s,'first_month':day})
    cells=[{'interval':[first[r],None],'modulus':period,'residues':[r]} for r in sorted(first)]
    return {'schema':'pp-dresden-overlap-months/1','station_months':stations,
            'restart_steps':steps,'period_months':period,'bases_in_period':bases,
            'cells':cells,'residue_origins':origins,'distinct_residues':len(first),
            'eventual_density':str(Fraction(len(first),period)),
            'complete_within_declared_month_schedule':True,
            'scope':'integer lunation indices; no eclipse visibility assertion'}


def schedule_count(packet,lo,hi):
    if _integer(lo)<0 or _integer(hi)<lo:
        raise ValueError('ordered nonnegative month bounds required')
    return count_domain(packet,lo,hi)


def schedule_select(packet,rank,*,start=0):
    if _integer(start)<0:
        raise ValueError('nonnegative starting month required')
    return select(packet,rank,start=start)


def node_drift(months,nodes,*,lunar_mean='29.530589',nodal_mean='173.30906'):
    """Exact offset between two stated rational mean-cycle models."""
    if _integer(months)<0 or _integer(nodes)<0:
        raise ValueError('nonnegative cycle counts required')
    lunar,nodal=Fraction(lunar_mean),Fraction(nodal_mean)
    if min(lunar,nodal)<=0:raise ValueError('positive reference means required')
    return str(months*lunar-nodes*nodal)


def venus_table_audit(data):
    """Check every published number against a declared 1 Ajaw canonical entry."""
    intervals=data['phase_intervals']
    if intervals!=[236,90,250,8]:raise ValueError('declared canonical phase intervals required')
    records=data['records']
    keys={(r['page'],r['row'],r['column']) for r in records}
    expected_keys={(p,r,c) for p in range(46,51) for r in range(1,14) for c in 'ABCD'}
    if len(records)!=260 or keys!=expected_keys:
        raise ValueError('complete uniquely addressed 260-number table required')
    offsets=[];acc=0
    for v in intervals:acc+=v;offsets.append(acc)
    mismatches=[]
    for r in records:
        day=(5*(r['row']-1)+r['page']-46)*584+offsets['ABCD'.index(r['column'])]
        expected=day%13+1
        number=_integer(r['reported_number'])
        if not 1<=number<=13:raise ValueError('reported ritual number out of range')
        if number!=expected:
            mismatches.append({**r,'elapsed_day':day,'canonical_expected_number':expected})
    return {'entries_checked':260,'matching_entries':260-len(mismatches),
            'mismatches':mismatches,'end_day':65*584,
            'scope':'numeric consistency with declared canonical entry; mismatch does not decide manuscript reading'}


def optimal_restart_order(long_count=4,short_count=1,*,long_drift='0.0972',short_drift='-0.42356'):
    """Global minimax prefix drift among all orders of a supplied multiset.

    Defaults reproduce figure 8's rounded offsets. States retain all optimal
    predecessor ties. This is an exact bounded mean-model policy, not historical
    evidence for an adopted ordering or a physical observability guarantee.
    """
    from math import comb
    _integer(long_count);_integer(short_count)
    if min(long_count,short_count)<0 or (long_count+1)*(short_count+1)>10000:
        raise ValueError('nonnegative counts within 10000 lattice states required')
    a,b=Fraction(long_drift),Fraction(short_drift)
    cost={(0,0):Fraction(0)};parents={(0,0):[]}
    for total in range(1,long_count+short_count+1):
        for i in range(max(0,total-short_count),min(long_count,total)+1):
            j=total-i;drift=i*a+j*b;candidates=[]
            if i:candidates.append((max(cost[i-1,j],abs(drift)),(i-1,j),'358'))
            if j:candidates.append((max(cost[i,j-1],abs(drift)),(i,j-1),'223'))
            best=min(c[0] for c in candidates)
            cost[i,j]=best;parents[i,j]=[(state,action) for c,state,action in candidates if c==best]
    # Count every ordering attaining the final global bound. Keeping only
    # prefix-minimal parents would incorrectly discard suboptimal prefixes
    # that still fit the final optimum, so use a second bounded reachability DP.
    bound=cost[long_count,short_count];counts={(0,0):1};witness={(0,0):[]}
    for total in range(1,long_count+short_count+1):
        for i in range(max(0,total-short_count),min(long_count,total)+1):
            j=total-i;state=(i,j)
            if abs(i*a+j*b)>bound:continue
            predecessors=[]
            if i and (i-1,j) in counts:predecessors.append(((i-1,j),358))
            if j and (i,j-1) in counts:predecessors.append(((i,j-1),223))
            if predecessors:
                counts[state]=sum(counts[p] for p,action in predecessors)
                p,action=predecessors[0];witness[state]=witness[p]+[action]
    return {'long_count':long_count,'short_count':short_count,
            'long_drift':str(a),'short_drift':str(b),'best_maximum_absolute_prefix_drift':str(bound),
            'terminal_drift':str(long_count*a+short_count*b),
            'all_orderings':comb(long_count+short_count,long_count),
            'optimal_orderings':counts[long_count,short_count],
            'witness':witness[long_count,short_count],
            'scope':'complete ordering optimization for supplied counts and rounded rational drift model'}


def lunar_interval_census(days,maximum_span=405,*,work_limit=4000000):
    """Exact empirical distributions of every overlapping n-month interval."""
    days=[_integer(d) for d in days];_integer(maximum_span);_integer(work_limit)
    if not days or any(a>=b for a,b in zip(days,days[1:])) or not 1<=maximum_span<len(days):
        raise ValueError('strictly increasing days and span below population length required')
    work=maximum_span*len(days)-maximum_span*(maximum_span+1)//2
    if work>work_limit:raise ValueError('interval census budget exceeded; no partial census')
    rows=[]
    for n in range(1,maximum_span+1):
        histogram=Counter(days[i+n]-days[i] for i in range(len(days)-n))
        total=len(days)-n;mode_count=max(histogram.values())
        modes=sorted(d for d,c in histogram.items() if c==mode_count)
        rows.append({'months':n,'interval_count':total,
                     'distribution':[{'days':d,'count':c,'frequency':str(Fraction(c,total))}
                                     for d,c in sorted(histogram.items())],
                     'modal_days':modes,'modal_frequency':str(Fraction(mode_count,total))})
    return {'schema':'pp-dresden-lunar-census/1','appearance_count':len(days),
            'maximum_span':maximum_span,'intervals_counted':work,'rows':rows,
            'ranked_month_spans':sorted(range(1,maximum_span+1),
                        key=lambda n:(-Fraction(rows[n-1]['modal_frequency']),n)),
            'scope':'all overlapping intervals in supplied integer-day corpus; no new visibility calculation'}


def compare_lunar_report(census,reported_rows,*,tolerance='0.000000000001'):
    """Compare exact recomputation with original spreadsheet decimal caches.

    Preserve duplicate span cells and missing categories, rather than silently
    normalizing published data. Tolerance concerns decimal caches only.
    """
    tolerance=Fraction(tolerance)
    if tolerance<0:raise ValueError('nonnegative tolerance required')
    lookup={r['months']:r for r in census['rows']};differences=[]
    months=[r['months'] for r in reported_rows]
    if len(set(months))!=len(months) or set(months)!=set(lookup):
        raise ValueError('one reported row per recomputed span required')
    for row in reported_rows:
        n=row['months'];computed=lookup[n]
        expected={r['days']:Fraction(r['frequency']) for r in computed['distribution']}
        cells=row['cells'];reported_days=[c['days'] for c in cells]
        duplicate=sorted(d for d,c in Counter(reported_days).items() if c>1)
        missing=sorted(set(expected)-set(reported_days));extra=sorted(set(reported_days)-set(expected))
        values=[{'cell':c['cell'],'days':c['days'],'reported':c['frequency'],
                 'recomputed':str(expected.get(c['days'],Fraction(0)))} for c in cells
                if abs(Fraction(c['frequency'])-expected.get(c['days'],Fraction(0)))>tolerance]
        if duplicate or missing or extra or values:
            differences.append({'months':n,'source_row':row['source_row'],
                                'duplicate_day_categories':duplicate,'missing_day_categories':missing,
                                'extra_day_categories':extra,'frequency_differences':values})
    return {'rows_compared':len(reported_rows),'matching_rows':len(reported_rows)-len(differences),
            'differences':differences,'decimal_tolerance':str(tolerance),
            'scope':'agreement under floor(JDN) extraction; discrepancies retained, source workbooks unchanged'}
