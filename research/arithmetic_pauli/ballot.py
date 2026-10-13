"""Prime-logarithmic ballot paths, exact counts and a survival constant."""
import math,json,time
import mpmath as mp
from research import OUT,append

def exact_diagonal(p,q,D):
    powers=[p**u for u in range(D+1)];prev=[0]*(D+1);prev[0]=1
    target={1,2,4,8,16,32,64,128,256,512,1024,2048,4096}
    for v in range(1,D+1):
        qv=q**v;lo,hi=0,D+1
        while lo+1<hi:
            mid=(lo+hi)//2
            if powers[mid]<=qv:lo=mid
            else:hi=mid
        row=[0]*(D+1);row[0]=1
        for u in range(1,lo+1):row[u]=prev[u]+row[u-1]
        if v in target:
            total=math.comb(2*v,v);value=row[v]
            append('prime_ballot.csv',dict(p=p,q=q,d=v,count=value,total=total,
                fraction=value/total,ambient_cutoff=q**v,grid_states=(v+1)**2))
        prev=row

def survival(p,q,L=2400):
    mp.mp.dps=65;s=mp.mpf(0);ef=mp.mpf(0);jf=mp.mpf(0);j2f=mp.mpf(0);alpha=mp.log(q)/mp.log(p*q)
    I=alpha*mp.log(2*alpha)+(1-alpha)*mp.log(2*(1-alpha))
    for n in range(1,L+1):
        k=int(mp.floor(n*alpha))+1
        # Exact comparisons remove logarithmic rounding from the threshold.
        while k>0 and p**(k-1)>q**(n-k+1):k-=1
        while p**k<=q**(n-k):k+=1
        term=math.comb(n,k);tail=term;t1=term*(2*k-n);t2=term*(2*k-n)**2
        for j in range(k,n):
            term=term*(n-j)//(j+1);tail+=term
            t1+=term*(2*(j+1)-n);t2+=term*(2*(j+1)-n)**2
        den=mp.mpf(2)**n
        s+=mp.mpf(tail)/(den*n)
        ef+=mp.mpf(tail)/den;jf+=mp.mpf(t1)/(den*n);j2f+=mp.mpf(t2)/(den*n)
    remainder=mp.exp(-(L+1)*I)/((L+1)*(1-mp.exp(-I)))
    upper=mp.exp(-s);lower=mp.exp(-s-remainder)
    correction=upper*(j2f-ef-jf*jf)/4
    return dict(p=p,q=q,terms=L,value=mp.nstr(upper,55),
        first_correction=mp.nstr(correction,45),
        truncation_lower=mp.nstr(lower,55),truncation_upper=mp.nstr(upper,55),
        log_series_tail_bound=mp.nstr(remainder,12),
        precision_digits=65,arithmetic_thresholds='exact integer power comparisons',
        caveat='Chernoff bound controls truncation; mpmath rounding is not interval-certified')

def main():
    t=time.perf_counter()
    (OUT/'prime_ballot.csv').unlink(missing_ok=True)
    for p,q in ((2,3),(2,5),(3,5),(5,7)):exact_diagonal(p,q,2048)
    values=[survival(2,3,2400),survival(2,5,1200),survival(3,5,4000),survival(5,7,6000)]
    (OUT/'survival_constants.json').write_text(json.dumps(values,indent=2))
    (OUT/'ballot_receipt.json').write_text(json.dumps(dict(seconds=time.perf_counter()-t,
        max_d=2048,prime_pairs=4,exact_grid_cell_upper_bound=4*2049**2),indent=2))
    print('prime ballot limit complete',values[0]['value'],flush=True)

if __name__=='__main__':main()
