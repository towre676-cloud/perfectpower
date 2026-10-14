"""Exact multimode arithmetic transport, path queries, turns and Pauli phases.

The state is (completed operation counts, finite controller state). Arithmetic
values use Fraction; height is max(reduced numerator, reduced denominator).
Pauli products are accumulated in the finite group {i^k I,X,Y,Z}, not floats.
"""
from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from math import prod,isqrt
from math import comb
import json,argparse,random

def prime(p):
    return type(p) is int and 2<=p<=100000 and all(p%k for k in range(2,isqrt(p)+1))

# product of Pauli axes: (additional i-power, resulting axis)
PAULI={
 (0,0):(0,0),(0,1):(0,1),(0,2):(0,2),(0,3):(0,3),
 (1,0):(0,1),(2,0):(0,2),(3,0):(0,3),
 (1,1):(0,0),(2,2):(0,0),(3,3):(0,0),
 (1,2):(1,3),(2,1):(3,3),(2,3):(1,1),(3,2):(3,1),
 (3,1):(1,2),(1,3):(3,2)}

def spin_multiply(a,b):
    phase,axis=PAULI[a[1],b[1]]
    return ((a[0]+b[0]+phase)%4,axis)

@dataclass(frozen=True)
class Mode:
    prime:int
    direction:int
    quota:int
    axis:int=1
    def __post_init__(self):
        if not prime(self.prime) or type(self.direction) is not int or self.direction not in (-1,1) or type(self.quota) is not int or not 0<=self.quota<=256 or type(self.axis) is not int or self.axis not in (0,1,2,3):
            raise ValueError('Modes require prime≤100000, direction ±1, quota 0..256, and Pauli axis 0..3')

class ModePopulation:
    def __init__(self,modes,start=1,height_cap=None,integral=True,controller=None,max_nodes=300000):
        self.modes=tuple(x if isinstance(x,Mode) else Mode(**x) for x in modes)
        if not 1<=len(self.modes)<=8:raise ValueError('one through eight labeled modes are supported')
        if not isinstance(start,(int,str,Fraction)) or isinstance(start,bool):raise ValueError('start must be an exact integer, decimal string or Fraction')
        if type(max_nodes) is not int or max_nodes<1:raise ValueError('positive integer node budget required')
        if height_cap is not None and (isinstance(height_cap,bool) or not isinstance(height_cap,(int,str))):raise ValueError('height cap must be an exact integer or decimal string')
        self.start=Fraction(str(start));self.integral=bool(integral)
        if self.start<=0:raise ValueError('positive rational start required')
        self.cap=int(height_cap) if height_cap is not None else None
        if self.cap is not None and self.cap<1:raise ValueError('positive height cap required')
        self.quotas=tuple(m.quota for m in self.modes);self.length=sum(self.quotas)
        if self.length>512:raise ValueError('total horizon must be at most 512')
        self.controller=controller or {'initial':0,'accepting':[0],'transitions':[[0]*len(self.modes)]}
        self.transition=self.controller['transitions'];self.accepting=set(self.controller['accepting']);initial=self.controller['initial']
        if not self.transition or any(len(row)!=len(self.modes) for row in self.transition):raise ValueError('controller needs one column per mode')
        if not 0<=initial<len(self.transition) or any(type(q) is not int or not 0<=q<len(self.transition) for q in self.accepting):raise ValueError('invalid controller states')
        if any(q is not None and (type(q) is not int or not 0<=q<len(self.transition)) for row in self.transition for q in row):raise ValueError('invalid transition target')
        self.root=(tuple(0 for _ in self.modes),initial);self.values={self.root:self.start};self.edges={};self.layers=[[self.root]]
        if not self.admissible(self.start):self.layers=[[]];self.suffix={self.root:0};return
        for depth in range(self.length):
            layer=[]
            for key in self.layers[-1]:
                c,q=key;out=[]
                for j,m in enumerate(self.modes):
                    if c[j]>=m.quota or self.transition[q][j] is None:continue
                    v=self.values[key]*Fraction(m.prime if m.direction==1 else 1,1 if m.direction==1 else m.prime)
                    if not self.admissible(v):continue
                    counts=c[:j]+(c[j]+1,)+c[j+1:];child=(counts,self.transition[q][j])
                    if child not in self.values:
                        if len(self.values)>=max_nodes:raise ValueError('Exact node budget exceeded; increase max_nodes explicitly')
                        self.values[child]=v;layer.append(child)
                    else:assert self.values[child]==v
                    out.append((j,child))
                self.edges[key]=out
            self.layers.append(layer)
        self.suffix={}
        for layer in reversed(self.layers):
            for key in layer:
                self.suffix[key]=(int(key[1] in self.accepting) if key[0]==self.quotas else sum(self.suffix[c] for j,c in self.edges.get(key,())))
        self.suffix.setdefault(self.root,0)

    def admissible(self,value):
        return (not self.integral or value.denominator==1) and (self.cap is None or max(value.numerator,value.denominator)<=self.cap)

    @property
    def count(self):return self.suffix[self.root]

    def advance(self,key,symbol):
        if type(symbol) is not int:return None
        return next((c for j,c in self.edges.get(key,()) if j==symbol),None)

    def conditional_count(self,prefix=()):
        key=self.root
        for symbol in prefix:
            key=self.advance(key,symbol)
            if key is None:return 0
        return self.suffix[key]

    def unrank(self,index):
        if type(index) is not int or not 0<=index<self.count:raise ValueError('rank outside exact population')
        key=self.root;word=[]
        while key[0]!=self.quotas:
            for j,c in self.edges[key]:
                if index<self.suffix[c]:word.append(j);key=c;break
                index-=self.suffix[c]
            else:raise RuntimeError('inconsistent suffix population')
        return tuple(word)

    def rank(self,word):
        if len(word)!=self.length:raise ValueError('wrong path length')
        key=self.root;index=0
        for symbol in word:
            for j,c in self.edges.get(key,()):
                if j==symbol:key=c;break
                index+=self.suffix[c]
            else:raise ValueError('inadmissible path')
        if key[1] not in self.accepting:raise ValueError('nonaccepting endpoint')
        return index

    def sample(self,seed=0):return self.unrank(random.Random(seed).randrange(self.count))

    def spin_histogram(self):
        tables={}
        for layer in reversed(self.layers):
            for key in layer:
                if key[0]==self.quotas:tables[key]={(0,0):1} if key[1] in self.accepting else {};continue
                hist={}
                for j,c in self.edges.get(key,()):
                    for g,n in tables[c].items():
                        k=spin_multiply(g,(0,self.modes[j].axis));hist[k]=hist.get(k,0)+n
                tables[key]=hist
        hist=tables.get(self.root,{})
        assert sum(hist.values())==self.count
        coefficients={}
        for axis in range(4):
            re=hist.get((0,axis),0)-hist.get((2,axis),0)
            im=hist.get((1,axis),0)-hist.get((3,axis),0)
            if re or im:coefficients[str(axis)]={'real':str(re),'imaginary':str(im)}
        norm=sum(int(v['real'])**2+int(v['imaginary'])**2 for v in coefficients.values())
        coherence=Fraction(norm,self.count**2) if self.count else Fraction(0)
        return {'phase_population':{f'{k[0]}:{k[1]}':str(n) for k,n in sorted(hist.items())},
                'amplitude_pauli_coefficients':coefficients,'coherence_squared':str(coherence),
                'exact_cancellation':self.count>0 and norm==0}

    def turn_polynomial(self,max_augmented_states=600000):
        if len(self.values)*(len(self.modes)+1)>max_augmented_states:raise ValueError('Turn polynomial exceeds explicit augmented-state budget')
        tables={};lasts=range(-1,len(self.modes))
        for layer in reversed(self.layers):
            for key in layer:
                for last in lasts:
                    if key[0]==self.quotas:tables[key,last]={0:1} if key[1] in self.accepting else {};continue
                    poly={}
                    for j,c in self.edges.get(key,()):
                        shift=int(last>=0 and last!=j)
                        for exponent,n in tables[c,j].items():poly[exponent+shift]=poly.get(exponent+shift,0)+n
                    tables[key,last]=poly
        result=tables.get((self.root,-1),{})
        assert sum(result.values())==self.count
        mean=Fraction(sum(k*n for k,n in result.items()),self.count) if self.count else Fraction(0)
        return {'coefficients':{str(k):str(n) for k,n in sorted(result.items())},'mean_switches':str(mean)}

    def height_profile(self):
        # Minimum possible peak height among controller/integrality-admitted words.
        unbounded=ModePopulation(self.modes,self.start,None,self.integral,self.controller,max_nodes=max(len(self.values)*4,300000))
        best={}
        for layer in reversed(unbounded.layers):
            for key in layer:
                h=max(unbounded.values[key].numerator,unbounded.values[key].denominator)
                if key[0]==self.quotas:best[key]=h if key[1] in unbounded.accepting else None
                else:
                    candidates=[best[c] for j,c in unbounded.edges.get(key,()) if best[c] is not None]
                    best[key]=max(h,min(candidates)) if candidates else None
        return best.get(unbounded.root)

    def height_filtration(self,max_cells=1000000):
        """One max-height/group-algebra sweep for every ceiling in this graph.

        To obtain all possible ceilings, construct with height_cap=None first.
        Each cell retains (peak arithmetic height, exact Pauli product).
        """
        if not self.admissible(self.start):return []
        initial=max(self.start.numerator,self.start.denominator)
        tables={self.root:{(initial,(0,0)):1}};cells=1;final={}
        for layer in self.layers:
            for key in layer:
                table=tables.pop(key,{})
                if key[0]==self.quotas:
                    if key[1] in self.accepting:
                        for event,n in table.items():final[event]=final.get(event,0)+n
                    continue
                for j,child in self.edges.get(key,()):
                    target=tables.setdefault(child,{})
                    value=self.values[child];h=max(value.numerator,value.denominator)
                    for (peak,g),n in table.items():
                        event=(max(peak,h),spin_multiply((0,self.modes[j].axis),g))
                        if event not in target:
                            cells+=1
                            if cells>max_cells:raise ValueError('Exact height-filtration cell budget exceeded')
                        target[event]=target.get(event,0)+n
        cumulative={};out=[]
        for peak in sorted({h for h,g in final}):
            for (h,g),n in final.items():
                if h==peak:cumulative[g]=cumulative.get(g,0)+n
            count=sum(cumulative.values());coeff=[]
            for axis in range(4):coeff.append((cumulative.get((0,axis),0)-cumulative.get((2,axis),0),cumulative.get((1,axis),0)-cumulative.get((3,axis),0)))
            norm=sum(re*re+im*im for re,im in coeff)
            out.append({'height':str(peak),'count':str(count),'amplitude_coefficients':[[str(a),str(b)] for a,b in coeff],
                        'coherence_squared':str(Fraction(norm,count**2)),'exact_cancellation':norm==0})
        assert not out or int(out[-1]['count'])==self.count
        return out

    def packet(self,turns=False):
        result={'schema':'pp-arithmetic-modes/1','start':str(self.start),'height_cap':str(self.cap) if self.cap else None,
            'modes':[m.__dict__ for m in self.modes],'controller':self.controller,'integral':self.integral,
            'horizon':self.length,'nodes':len(self.values),'count':str(self.count),'spin':self.spin_histogram(),
            'first_path':list(self.unrank(0)) if self.count else None,
            'last_path':list(self.unrank(self.count-1)) if self.count else None}
        if turns:result['turns']=self.turn_polynomial()
        return result

def signed_ballot(p,q,d):
    if not prime(p) or not prime(q) or p>=q or type(d) is not int or not 0<=d<=4096:raise ValueError('Increasing primes and exponent 0..4096 required')
    P=[p**i for i in range(d+1)];prev=[0]*(d+1);prev[0]=1
    for v in range(1,d+1):
        threshold=q**v;row=[0]*(d+1);row[0]=1;sign=-1 if v%2 else 1
        for u in range(1,d+1):
            if P[u]<=threshold:row[u]=sign*row[u-1]+prev[u]
        prev=row
    return prev[d]

class SlopeAtlas:
    """Compile every exact height-wall chamber once, then reuse across bases.

    Grid admissibility depends only on log(q)/log(p). Finite walls are rational
    u/v. Query classification compares q^v with p^u, without numerical logs.
    The left boundary is included, so multiplicatively dependent bases work.
    """
    def __init__(self,d,max_work=10000000):
        if type(d) is not int or not 1<=d<=128:raise ValueError('atlas exponent must lie in 1..128')
        self.d=d;self.walls=sorted({Fraction(u,v) for u in range(1,d+1) for v in range(1,d+1) if u>=v})
        if len(self.walls)*(d+1)**2>max_work:raise ValueError('Exact chamber compilation work budget exceeded')
        self.results=[]
        for wall in self.walls:
            count=[0]*(d+1);signed=[0]*(d+1);count[0]=signed[0]=1
            for v in range(1,d+1):
                c=[0]*(d+1);s=[0]*(d+1);c[0]=s[0]=1
                for u in range(1,d+1):
                    if u*wall.denominator<=v*wall.numerator:
                        c[u]=c[u-1]+count[u];s[u]=(-s[u-1] if v%2 else s[u-1])+signed[u]
                count,signed=c,s
            self.results.append((count[d],signed[d]))

    def query(self,p,q):
        if type(p) is not int or type(q) is not int or not 2<=p<=q:raise ValueError('ordered integer bases 2≤p≤q required')
        lo,hi=0,len(self.walls)
        while lo+1<hi:
            mid=(lo+hi)//2;wall=self.walls[mid]
            if q**wall.denominator>=p**wall.numerator:lo=mid
            else:hi=mid
        count,signed=self.results[lo]
        return {'exponent':self.d,'count':str(count),'signed':str(signed),
                'chamber':lo,'left_wall':str(self.walls[lo]),
                'right_wall':str(self.walls[lo+1]) if lo+1<len(self.walls) else None,
                'coherence_squared':str(Fraction(signed*signed,count*count))}

def main():
    parser=argparse.ArgumentParser(description='Exact multimode arithmetic path populations and Pauli interference')
    parser.add_argument('input',help='JSON specification');parser.add_argument('--turns',action='store_true')
    parser.add_argument('--rank',type=int);parser.add_argument('--minimum-height',action='store_true')
    parser.add_argument('--filtration',action='store_true')
    args=parser.parse_args()
    with open(args.input) as f:spec=json.load(f)
    pop=ModePopulation(**spec);result=pop.packet(args.turns)
    if args.rank is not None:result['ranked_path']=pop.unrank(args.rank)
    if args.minimum_height:result['minimum_height']=str(pop.height_profile())
    if args.filtration:result['height_filtration']=pop.height_filtration()
    print(json.dumps(result))

if __name__=='__main__':main()
