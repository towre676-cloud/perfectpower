"""Independent bounded coefficient charts, recurrence transitions and reusable queries."""
import json,time
from pathlib import Path
from perfectpower.coefficient_charts import primitive_power_charts,primitive_points
from perfectpower.polynomial_charts import parameterize_relation
from perfectpower.query_space import CurveSpace
from perfectpower.curve_queries import verify_curve_query
from perfectpower.integer_image_index import IntegerImageIndex
from perfectpower.recurrence_domains import *

ROOT=Path(__file__).resolve().parents[1]
def main():
    out=ROOT/'receipts/query_space_push';out.mkdir(parents=True,exist_ok=True)
    rows=[];errors=[];comparisons=0
    values=[i for i in range(-8,9) if i]
    start=time.perf_counter()
    for c in values:
      for d in values:
       for p in range(2,6):
        for q in range(2,6):
            chart=primitive_power_charts(c,p,d,q)
            actual={(x,y) for x in range(-12,13) for y in range(-12,13) if c*x**p==d*y**q}
            generated={pt for t in range(13) for pt in primitive_points(chart,t) if max(map(abs,pt))<=12}
            comparisons+=625
            if actual!=generated:errors.append([c,d,p,q])
            rows.append({'c':c,'d':d,'p':p,'q':q,'scales':[chart['left_scale'],chart['right_scale']],
                         'signs':chart['signs'],'obstruction':chart['obstruction'],'bounded_points':sorted(actual)})
    coefficient_seconds=time.perf_counter()-start
    assert not errors,errors
    orbit_rows=[];periodic=singular=transition_checks=0
    for m in range(2,32):
      for P in ([1,1],[3,0,1],[2],[0]):
       for Q in ([1],[1,1],[1,1,1]):
        for seed in (0,1):
            orbit=recurrence_orbit(P,Q,m,seed,step_limit=2000)
            v=seed%m;ok=True
            end=300 if orbit['complete'] else orbit['singular_index']+1
            for n in range(end):
                assert orbit_value(orbit,n)==v
                p=sum(c*n**i for i,c in enumerate(P))%m
                q=sum(c*n**i for i,c in enumerate(Q))%m
                candidates=[z for z in range(m) if q*z%m==p*v%m]
                transition_checks+=1
                if not orbit['complete'] and n==orbit['singular_index']:
                    r=orbit['next_values'];encoded=[] if not r['count'] else [r['base']+i*r['step'] for i in range(r['count'])]
                    assert candidates==encoded
                else:
                    assert len(candidates)==1;v=candidates[0]
            domain=orbit_domain(orbit,power=2)
            powers={z*z%m for z in range(m)}
            limit=end-1
            expected=sum(orbit_value(orbit,n) in powers for n in range(limit+1))
            assert orbit_count(domain,0,limit)==expected
            assert verify_orbit_domain(domain)
            periodic+=orbit['complete'];singular+=not orbit['complete']
            orbit_rows.append({'modulus':m,'P':P,'Q':Q,'seed':seed,'status':orbit['status'],
                               'states':len(orbit['states']),'period':orbit['period'],
                               'singular_index':orbit['singular_index'],'bounded_hits':expected})
    space=CurveSpace([0,0,2],[0,0,0,3]);T=10**40
    huge=space.query({'expr':'y-'+str(6*T*T),'relation':'<='},point_limit=0)
    assert huge['solution_count']==2*T+1 and verify_curve_query(huge)
    ties=space.query({'expr':'y','relation':'>'},objective='x*x+y*y')
    assert ties['optimization']['optimizer_points']==[(-18,6),(18,6)] and verify_curve_query(ties)
    image=IntegerImageIndex()
    for repeat in range(3):
      for u in range(32):
        roots=image.points([1,1,1],u)
        assert roots==[x for x in range(-100,101) if x*x+x+1==u]
    dynamics=orbit_domain(recurrence_orbit([3,0,1],[1,1,1],8,1),power=2)
    H=10**100
    assert orbit_count(dynamics,0,H)==H and orbit_select(dynamics,H)==H+1
    summary={'coefficient_cases':len(rows),'independent_pair_checks':comparisons,'coefficient_mismatches':len(errors),
             'coefficient_seconds':coefficient_seconds,'recurrence_cases':len(orbit_rows),'periodic':periodic,'singular':singular,
             'independent_transition_checks':transition_checks,'reused_fibres':image.statistics(),
             'huge_curve_parameter_bound':T,'huge_curve_count':huge['solution_count'],'curve_space':space.statistics(),
             'huge_recurrence_through':H,'huge_recurrence_count':orbit_count(dynamics,0,H),'huge_selected_rank':orbit_select(dynamics,H),
             'scope':'Constructed mathematical workloads; no industrial speedup claim. Modular power residues are necessary conditions, not integer perfect-power completeness.'}
    for name,data in [('coefficient_corpus',rows),('recurrence_corpus',orbit_rows),('huge_curve',huge),('curve_ties',ties),('recurrence_domain',dynamics),('summary',summary)]:
        (out/(name+'.json')).write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps(summary,indent=2))
if __name__=='__main__':main()
