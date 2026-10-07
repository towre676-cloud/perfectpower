"""Produce independent Python fixtures and full deep-research receipts."""
from pathlib import Path
from fractions import Fraction
import json,hashlib
from perfectpower.dresden import calendar_round,Progression,venus_rules
from perfectpower.dresden_eclipse import overlap_schedule,schedule_select
from perfectpower.dresden_analysis import interval_distribution,distribution_summary,total_variation
ROOT=Path(__file__).resolve().parents[1]
source=json.loads((ROOT/'research/dresden/lunar_source.json').read_text())
stations=json.loads((ROOT/'research/dresden/eclipse_stations.json').read_text())
packet={'schema':'pp-dresden-deep-research/1','scope':'exact declared numerical models; descriptive supplied-corpus analysis',
 'calendar':[],'venus':[],'windows':[],'comparisons':[],'ranks':[],'policies':[]}
for number,sign,haab,v,lo,hi,rank in [(1,19,338,None,0,10**30,0),(4,19,348,0,0,37960*10**30,10**30),(2,19,348,None,0,10**30,0),(1,19,338,583,1,10**100,10**30)]:
 p=calendar_round(number,sign,haab)
 if p is not None and v is not None:p=p.intersect(Progression(v,584))
 row={'input':{'number':number,'sign':sign,'haab':haab,'venus':v,'lo':str(lo),'hi':str(hi),'rank':str(rank)},'compatible':p is not None}
 if p is not None:
  count=p.count(lo,hi);row.update(residue=str(p.residue),modulus=str(p.modulus),count=str(count),selected=str(p.select(rank,lo,hi)) if rank<count else None)
 packet['calendar'].append(row)
for i,rule in enumerate(venus_rules()):
 for rounds in [0,1,121,122,182,183,366,10**30]:
  for ref in ['583.9214','584','585','35620/61']:
   packet['venus'].append({'model':i,'rounds':str(rounds),'reference':ref,'execute':rule.execute(rounds,reference=ref),'envelope':rule.error_envelope(rounds,reference=ref)})
for n in [1,49,81,98,405]:
 for start,end in [(0,8052),(0,4026),(4026,8052),(100,2000)]:
  rows=interval_distribution(source['days'],n,start,end)
  packet['windows'].append({'span':n,'start':start,'end':end,'distribution':rows,'summary':distribution_summary(rows)})
for a,b in [(49,81),(98,405),(405,405),(1,98)]:
 offset=lambda n:int(n*Fraction('29.530589'))
 packet['comparisons'].append({'a':a,'b':b,'offsets':[offset(a),offset(b)],'distance':total_variation(interval_distribution(source['days'],a),interval_distribution(source['days'],b),offset(a),offset(b))})
months=[s['month'] for s in stations['stations'] if s['classification']=='intended']
for position in range(5):
 p=overlap_schedule(months,[223 if i==position else 358 for i in range(5)])
 for start,rank in [(0,0),(405,0),(6000,100),(10**30,10**30)]:
  packet['ranks'].append({'position':position,'start':str(start),'rank':str(rank),'selected':str(schedule_select(p,rank,start=start))})
for a,b in [('0.0972','-0.42356'),('0','0'),('1','-4'),('-2','1'),('1/3','-7/6')]:
 peaks=[];terminal=None
 for pos in range(5):
  value=Fraction(0);peak=Fraction(0)
  for i in range(5):value+=Fraction(b if i==pos else a);peak=max(peak,abs(value))
  peaks.append(peak);terminal=value
 best=min(peaks);packet['policies'].append({'long':a,'short':b,'best':str(best),'winners':[i for i,p in enumerate(peaks) if p==best],'terminal':str(terminal)})
packet['source_hashes']={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [ROOT/'research/dresden/lunar_source.json',ROOT/'research/dresden/eclipse_stations.json',ROOT/'python/perfectpower/dresden_analysis.py']}
def portable(value):
 if isinstance(value,int) and abs(value)>2**53-1:return str(value)
 if isinstance(value,dict):return {k:portable(v) for k,v in value.items()}
 if isinstance(value,list):return [portable(v) for v in value]
 return value
path=ROOT/'receipts/dresden/deep-research.json';path.write_text(json.dumps(portable(packet),indent=2)+'\n');print(path)
