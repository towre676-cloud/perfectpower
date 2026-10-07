"""Rebuild compact source-labelled Dresden arithmetic receipts."""
import hashlib
import json
from fractions import Fraction
from pathlib import Path
from perfectpower.dresden import *
from perfectpower.dresden_eclipse import *

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'receipts/dresden'
OUT.mkdir(parents=True,exist_ok=True)
anchor=long_count_days([9,9,9,16,0])
rules=venus_rules()
corrections=[long_count_days(x) for x in ([4,12,8,0],[9,11,7,0],[1,5,14,4,0],[1,5,5,0])]
packet={
 'schema':'pp-dresden-corpus/1',
 'scope':'exact arithmetic of declared inputs; no complete manuscript transcription or ephemeris',
 'calendar':{'round_days':18980,'venus_joint_days':37960,'five_venus_eight_haab_days':2920,
             'enormous_joint_population':Progression(0,37960).count(0,37960*10**30)},
 'aldana':{'source':'https://escholarship.org/uc/item/6cr1s6jd','printed_pages':[65,66,67,69],
           'status':'literature interpretation; independently recomputed arithmetic',
           'anchor_digits':[9,9,9,16,0], 'anchor_days':anchor,
           'correction_intervals':corrections,
           'correction_coefficients':[[1,2],[2,3],[5,2],[4,61]],
           'identities_hold':all(x*37960-y*2340==c for (x,y),c in zip([(1,2),(2,3),(5,2),(4,61)],corrections)),
           'CVI1_anchor':days_long_count(anchor+71240),
           'CVI2_anchor':days_long_count(anchor+106860),
           'same_ratio':str(Fraction(71240,75920)),
           'same_mean':str(Fraction(71240,122)),
           'printed_CI3_discrepancy':{'source_location':'printed page 66, CI3 decimal line',
                    'printed_coefficient':3,'printed_expression_value':3*37960-2*2340,
                    'long_count_value':185120,'consistent_coefficient':5,
                    'note':'The preceding Long Count coefficient is 5; do not propagate the decimal-line 3.'}},
 'venus_experiments':[{'name':r.name,'mean':str(r.mean_period),
                     'round_1000000000000':r.execute(10**12),
                     'envelope':r.error_envelope(10**12)} for r in rules],
 'eclipse_numeric_seed':{'source':'https://doi.org/10.1126/sciadv.adt9039',
               'status':'proposed standard span; surviving source table totals 11959 days',
               'days':11960,'lunations':405,'ritual_rounds':46,'mean_lunation':str(Fraction(11960,405))},
 'synthetic_reconstruction':{'status':'synthetic demonstration; no damaged glyphs transcribed',
               'assumptions':'69 labelled slots, each 148, 177 or 178 days; sum 11960',
               'result':reconstruct_intervals([[148,177,178]]*69,11960,state_limit=2000000)},
 'polynomial_calendar_demo':{'status':'synthetic polynomial window in original day coordinates',
        'result':polynomial_calendar(Progression(16780,18980),
                    {'poly':[997500000000,-2000000,1],'relation':'<='},0,2000000)},
 'source_tables':{'eclipse_audit':station_audit(json.loads((ROOT/'research/dresden/eclipse_stations.json').read_text())),
                  'venus_audit':venus_table_audit(json.loads((ROOT/'research/dresden/venus_numbers.json').read_text()))},
 'standard_eclipse_hypotheses':[{'shift_at_surviving_day':c['shift_at_surviving_day'],
                 'first_shifted_day':c['first_shifted_day'],'last_day':c['last_day']}
       for c in standard_table_candidates(json.loads((ROOT/'research/dresden/eclipse_stations.json').read_text()))],
 'overlapping_restart_schedule':overlap_schedule(
        [r['month'] for r in json.loads((ROOT/'research/dresden/eclipse_stations.json').read_text())['stations'] if r['classification']=='intended'],[358]*4+[223]),
 'bounded_restart_order_policy':optimal_restart_order(),
 'mean_nodal_drift':{str(m):node_drift(m,n) for m,n in [(405,69),(358,61),(223,38),(1655,282)]},
 'source_hashes':{p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in
                 ('python/perfectpower/dresden.py','python/perfectpower/dresden_eclipse.py',
                  'research/dresden/sources.json','research/dresden/eclipse_stations.json',
                  'research/dresden/venus_numbers.json','research/dresden/lunar_source.json')}
}
source=json.loads((ROOT/'research/dresden/lunar_source.json').read_text())
census=lunar_interval_census(source['days'])
comparison=compare_lunar_report(census,source['reported_rows'])
(OUT/'lunar_census.json').write_text(json.dumps({'census':census,'published_comparison':comparison},indent=2)+'\n')
packet['lunar_dataset_summary']={'appearance_count':census['appearance_count'],
    'intervals_counted':census['intervals_counted'],'matching_published_rows':comparison['matching_rows'],
    'disagreeing_month_spans':[r['months'] for r in comparison['differences']],
    'ranked_month_spans':census['ranked_month_spans'][:15]}
(OUT/'corpus.json').write_text(json.dumps(packet,indent=2,sort_keys=True)+'\n')
print(json.dumps({'output':str(OUT/'corpus.json'),'reconstruction_count':packet['synthetic_reconstruction']['result']['count'],
 'venus_mean':packet['aldana']['same_mean'],'identities_hold':packet['aldana']['identities_hold']}))
