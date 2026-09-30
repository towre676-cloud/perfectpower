"""Exact binary cubic transport. No unproved canonicalization or completeness."""
from math import comb
from fractions import Fraction
import json,hashlib

def evaluate(F,x,y):return sum(c*x**(3-i)*y**i for i,c in enumerate(F))
def det(T):a,b,c,d=T;return a*d-b*c
def mul(S,T):a,b,c,d=S;e,f,g,h=T;return (a*e+b*g,a*f+b*h,c*e+d*g,c*f+d*h)
def inverse(T):
 a,b,c,d=T;e=det(T)
 if abs(e)!=1:raise ValueError('unimodular matrix required')
 return (d//e,-b//e,-c//e,a//e)
def apply(T,p):a,b,c,d=T;x,y=p;return (a*x+b*y,c*x+d*y)
def substitute(F,T):
 a,b,c,d=T;out=[0]*4
 for i,coef in enumerate(F):
  for j in range(4-i):
   for k in range(i+1):out[j+k]+=coef*comb(3-i,j)*a**(3-i-j)*b**j*comb(i,k)*c**(i-k)*d**k
 return tuple(out)
def discriminant(F):
 a,b,c,d=F
 return b*b*c*c-4*a*c**3-4*b**3*d-27*a*a*d*d+18*a*b*c*d

def transport_certificate(F,M,T):
 inverse(T)
 return {'kind':'unimodular_equivalence','source':list(F),'rhs':M,'target':list(substitute(F,T)),'matrix':list(T),'inverse':list(inverse(T))}
def check_transport(c):
 try:
  T=tuple(c['matrix']);return c['kind']=='unimodular_equivalence' and tuple(c['inverse'])==inverse(T) and tuple(c['target'])==substitute(c['source'],T)
 except (ValueError,KeyError,TypeError):return False

def bound_transport(T,U,V):
 if min(U,V)<0:raise ValueError('nonnegative bounds')
 a,b,c,d=T;return abs(a)*U+abs(b)*V,abs(c)*U+abs(d)*V

def bounded_solutions(F,M,U,V):
 return [(x,y) for x in range(-U,U+1) for y in range(-V,V+1) if evaluate(F,x,y)==M]

def local_obstruction(F,M,q):
 if q<2:raise ValueError('modulus >= 2')
 residues=[(a,b) for a in range(q) for b in range(q) if (evaluate(F,a,b)-M)%q==0]
 return {'form':list(F),'rhs':M,'modulus':q,'empty':not residues,'residue_count':len(residues),'status':'exact_finite_modular_check'}

def obligation_key(F,M,restrictions=None):
 # exact content only; shared fields and bounded similarity never deduplicate
 payload={'form':list(F),'rhs':M,'restrictions':restrictions or {}}
 return hashlib.sha256(json.dumps(payload,sort_keys=True,separators=(',',':')).encode()).hexdigest()

def intern_obligations(rows):
 nodes={};mapping=[]
 for row in rows:
  k=obligation_key(row['form'],row['rhs'],row.get('restrictions'));nodes.setdefault(k,row);mapping.append(k)
 return {'nodes':nodes,'input_to_node':mapping,'input_count':len(rows),'unique_count':len(nodes)}

def discover_edges(rows,height=2):
 # bounded discovery, every returned edge exactly rechecked; not full GL2 classification
 lookup={obligation_key(r['form'],r['rhs'],r.get('restrictions')):i for i,r in enumerate(rows)};edges=[]
 for i,r in enumerate(rows):
  if r.get('restrictions'):continue # unrestricted maps require restriction transport
  for a in range(-height,height+1):
   for b in range(-height,height+1):
    for c in range(-height,height+1):
     for d in range(-height,height+1):
      T=(a,b,c,d)
      if abs(det(T))!=1:continue
      G=substitute(r['form'],T);j=lookup.get(obligation_key(G,r['rhs']))
      if j is not None and i<j:edges.append({'source_index':i,'target_index':j,'certificate':transport_certificate(r['form'],r['rhs'],T)})
 return edges

def parse_seq(text):
 # raw source preserved by caller. OEIS %S/%T/%U terms and first offset component.
 import re
 ids=set(re.findall(r'^%[A-Z] (A\d{6}) ',text,re.M))
 if len(ids)!=1:raise ValueError('one entry per file required')
 aid=next(iter(ids));offset=re.search(r'^%O '+aid+r' (-?\d+)',text,re.M)
 name=re.search(r'^%N '+aid+r' (.*)$',text,re.M)
 chunks=re.findall(r'^%[STU] '+aid+r' (.*)$',text,re.M);terms=[]
 for chunk in chunks:
  for token in chunk.split(','):
   token=token.strip()
   if token:
    if not re.fullmatch(r'-?\d+',token):raise ValueError('noninteger term token')
    terms.append(int(token))
 if not offset:raise ValueError('offset missing')
 return {'id':aid,'offset':int(offset.group(1)),'name':name.group(1) if name else '', 'terms':terms}

def pell(n):
 if n<0:raise ValueError('nonnegative index')
 a,b=1,0
 for _ in range(n):a,b=a+2*b,a+b
 return a,b

def match_shift(entry,max_shift=20):
 if not entry['terms']:return []
 out=[]
 for s in range(max_shift+1):
  # explicit convention: source index n maps to B(n+s), not B(position+s)
  if entry['offset']+s<0:continue
  if all(pell(entry['offset']+j+s)[1]==v for j,v in enumerate(entry['terms'])):out.append(s)
 return out
