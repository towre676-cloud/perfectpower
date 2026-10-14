"""Dense retained exact experiments for multimode transport and spin filtration."""
from pathlib import Path
import sys,json,time,math,random,csv,gc
from fractions import Fraction
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'python'))
from perfectpower.arithmetic_modes import Mode,ModePopulation,signed_ballot
from perfectpower.arithmetic_transport import height_ballot
OUT=ROOT/'receipts/arithmetic_modes'

def main():
    OUT.mkdir(exist_ok=True);started=time.perf_counter();rows=[];atlas=[]
    for p,q in ((2,3),(2,5),(3,5),(5,7)):
        for d in range(1,65):
            count=height_ballot(p,q,d)['count'];signed=signed_ballot(p,q,d)
            full=0 if d%2 else math.comb(d,d//2)
            rows.append({'p':p,'q':q,'d':d,'count':str(count),'signed':str(signed),
                         'unrestricted_signed':str(full),'coherence_squared':str(Fraction(signed*signed,count*count)),
                         'height_revives_zero_unrestricted':full==0 and signed!=0,'height_cancels_nonzero_unrestricted':full!=0 and signed==0})
    with (OUT/'signed_ballot.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=rows[0],lineterminator='\n');w.writeheader();w.writerows(rows)
    for d in (1,2,3,4,6):
        pop=ModePopulation([Mode(2,1,d,1),Mode(3,-1,d,2)],3**d)
        atlas.append({'id':f'two_{d}','title':f'Two modes, power {d}',**pop.packet(True),
                      'filtration':pop.height_filtration(),'minimum_height':str(pop.height_profile())})
    presets=[
        ('four', [Mode(2,-1,2,1),Mode(3,-1,2,2),Mode(5,1,2,3),Mode(7,1,2,1)],36,1225,True,None),
        ('rational',[Mode(2,1,2,1),Mode(3,-1,2,2),Mode(5,1,1,3)],1,25,False,None),
        ('controller',[Mode(2,1,3,1),Mode(3,-1,3,2)],27,27,True,{'initial':0,'accepting':[0,1,2],'transitions':[[1,2],[None,2],[1,None]]})]
    for name,modes,start,cap,integral,controller in presets:
        pop=ModePopulation(modes,start,cap,integral,controller)
        atlas.append({'id':name,'title':name.title()+' transport',**pop.packet(True),
                      'filtration':ModePopulation(modes,start,None,integral,controller).height_filtration(),
                      'minimum_height':str(pop.height_profile())})
    (OUT/'atlas.json').write_text(json.dumps({'schema':'pp-arithmetic-mode-atlas/1','cases':atlas},indent=2)+'\n')
    benchmarks=[]
    for k,ds in ((4,(4,8,12,16,24)),(6,(3,4,5,6,7))):
        for d in ds:
            primes=(2,3,5,7) if k==4 else (2,3,5,7,11,13);split=k//2
            modes=[Mode(p,-1 if j<split else 1,d,1+j%3) for j,p in enumerate(primes)]
            start=math.prod(primes[:split])**d;cap=math.prod(primes[split:])**d
            t=time.perf_counter();pop=ModePopulation(modes,start,cap,max_nodes=650000);setup=time.perf_counter()-t
            rng=random.Random(42);ranks=[rng.randrange(pop.count) for _ in range(300)]
            t=time.perf_counter()
            for rank in ranks:assert pop.rank(pop.unrank(rank))==rank
            query=time.perf_counter()-t
            spin=None
            if len(pop.values)<90000:
                t=time.perf_counter();spin=pop.spin_histogram();spin['seconds']=time.perf_counter()-t
            result={'modes':k,'quota':d,'horizon':k*d,'nodes':len(pop.values),'count':str(pop.count),
                'construction_seconds':setup,'rank_roundtrips':300,'roundtrip_seconds':query,'spin':spin}
            benchmarks.append(result);print(json.dumps(result),flush=True)
            del pop;gc.collect()
    receipt={'schema':'pp-arithmetic-modes-benchmark/1','signed_cases':len(rows),
             'revivals':sum(r['height_revives_zero_unrestricted'] for r in rows),
             'cancellations':sum(r['height_cancels_nonzero_unrestricted'] for r in rows),
             'benchmarks':benchmarks,'seconds':time.perf_counter()-started,
             'scope':'Exact finite populations and leading Pauli word coefficients; no infinite-time quantum claim or baseline speedup.'}
    (OUT/'benchmark.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:receipt[k] for k in ('signed_cases','revivals','cancellations','seconds')}),flush=True)

if __name__=='__main__':main()
