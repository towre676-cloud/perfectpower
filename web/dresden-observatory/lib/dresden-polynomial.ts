/** Exact integer sign domains, adapted from PerfectPower's polynomial_domains
 * and sturm_fibres architecture. The Lean chart laws are separate from this
 * JavaScript producer; no interpreter or Sturm completeness proof is claimed. */
import {rational,add,sub,mul,type Rational} from './dresden-research.ts';
import {gcd} from './dresden-math.ts';
type Poly=bigint[];
type Relation='='|'!='|'<'|'<='|'>'|'>=';
type Tree=boolean|{atom:number}|{op:'and'|'or'|'not';args:Tree[]};
export type Atom={poly:Poly;relation:Relation};
export type Interval=[bigint,bigint];
const relations=['=','!=','<','<=','>','>='];
const trim=(p:Poly):Poly=>{while(p.length>1&&p.at(-1)===0n)p.pop();return p;};
const zero=(p:Poly)=>p.length===1&&p[0]===0n;
const absolute=(n:bigint)=>n<0n?-n:n;
const divide=(a:Rational,b:Rational)=>rational(a.n*b.d,a.d*b.n);
function primitive(p:Rational[]):Poly{let d=1n;for(const c of p)d=d/gcd(d,c.d)*c.d;const values=p.map(c=>c.n*(d/c.d));const g=values.reduce((a,b)=>gcd(a,b),0n)||1n;return trim(values.map(c=>c/g));}
function divmod(a:Poly,b:Poly){if(zero(b))throw Error('Zero polynomial divisor');const r=a.map(n=>rational(n)),q=Array.from({length:Math.max(1,a.length-b.length+1)},()=>rational(0n));for(let i=a.length-1;i>=b.length-1;i--){const c=divide(r[i],rational(b.at(-1)!));q[i-b.length+1]=c;for(let j=0;j<b.length;j++)r[i-b.length+1+j]=sub(r[i-b.length+1+j],mul(c,rational(b[j])));}return {quotient:q,remainder:r.slice(0,Math.max(1,b.length-1))};}
const derivative=(p:Poly)=>trim(p.length>1?p.slice(1).map((c,i)=>c*BigInt(i+1)):[0n]);
function squarefree(p:Poly){let a=p,b=derivative(p);while(!zero(b)){const next=primitive(divmod(a,b).remainder);a=b;b=next;}const result=divmod(p,a);if(!zero(primitive(result.remainder)))throw Error('Squarefree division failed');return primitive(result.quotient);}
export function evaluatePolynomial(p:Poly,x:bigint){let v=0n;for(let i=p.length-1;i>=0;i--)v=v*x+p[i];return v;}
export function composeDay(p:Poly,a:bigint,m:bigint):Poly{let q=[0n];for(let i=p.length-1;i>=0;i--){const next=Array<bigint>(q.length+1).fill(0n);q.forEach((c,j)=>{next[j]+=a*c;next[j+1]+=m*c;});next[0]+=p[i];q=trim(next);}return q;}
export function parsePredicate(value:unknown){const atoms:Atom[]=[];let nodes=0;const walk=(v:unknown,depth=0):Tree=>{if(++nodes>128||depth>16)throw Error('Use at most 128 predicate nodes and 16 levels');if(typeof v==='boolean')return v;if(!v||typeof v!=='object'||Array.isArray(v))throw Error('Use a Boolean polynomial predicate');const n=v as Record<string,unknown>,keys=Object.keys(n).sort().join(',');if(keys==='poly,relation'){if(!Array.isArray(n.poly)||n.poly.length<1||n.poly.length>9||!relations.includes(String(n.relation)))throw Error('Each atom needs 1–9 ascending coefficients and a supported relation');if(atoms.length>=16)throw Error('Use at most 16 polynomial atoms');const p=n.poly.map(c=>{if(typeof c==='number'&&!Number.isSafeInteger(c))throw Error('Large coefficients must be quoted decimal strings');if(typeof c!=='string'&&typeof c!=='number'||!/^[-]?\d{1,120}$/.test(String(c)))throw Error('Use integer coefficients of at most 120 digits');return BigInt(c);});const index=atoms.length;atoms.push({poly:trim(p),relation:n.relation as Relation});return {atom:index};}if(keys!=='args,op'||!['and','or','not'].includes(String(n.op))||!Array.isArray(n.args)||n.op==='not'&&n.args.length!==1)throw Error('Use and/or with argument lists, or not with one argument');return {op:n.op as 'and'|'or'|'not',args:n.args.map(c=>walk(c,depth+1))};};return {tree:walk(value),atoms};}
const relationHolds=(v:bigint,r:Relation)=>r==='='?v===0n:r==='!='?v!==0n:r==='<'?v<0n:r==='<='?v<=0n:r==='>'?v>0n:v>=0n;
function truth(tree:Tree,values:boolean[]):boolean{if(typeof tree==='boolean')return tree;if('atom'in tree)return values[tree.atom];return tree.op==='and'?tree.args.every(c=>truth(c,values)):tree.op==='or'?tree.args.some(c=>truth(c,values)):!truth(tree.args[0],values);}
export function predicateHolds(predicate:unknown,x:bigint){const p=parsePredicate(predicate);return truth(p.tree,p.atoms.map(a=>relationHolds(evaluatePolynomial(a.poly,x),a.relation)));}
function sturm(p:Poly){const chain=[p,derivative(p)];while(!zero(chain.at(-1)!)){const r=primitive(divmod(chain.at(-2)!,chain.at(-1)!).remainder).map(c=>-c);if(zero(r))break;chain.push(r);}return chain;}
function variations(chain:Poly[],x:bigint){let prior=0,count=0;for(const p of chain){const v=evaluatePolynomial(p,x),sign=v<0n?-1:v>0n?1:0;if(!sign)continue;if(prior&&sign!==prior)count++;prior=sign;}return count;}
function rootBound(p:Poly){const lead=absolute(p.at(-1)!);return 1n+p.slice(0,-1).reduce((bound,c)=>{const q=(absolute(c)+lead-1n)/lead;return q>bound?q:bound;},0n);}
const floorDiv=(a:bigint,b:bigint)=>{const q=a/b;return a<0n&&a%b!==0n?q-1n:q;};
export function polynomialCalendar(predicate:unknown,residue:bigint,period:bigint,lo:bigint,hi:bigint,rank=0n,nodeLimit=4096){if(period<=0n||residue<0n||residue>=period||hi<lo||rank<0n||!Number.isSafeInteger(nodeLimit)||nodeLimit<1)throw Error('Canonical chart, ordered bounds and nonnegative rank required');const {tree,atoms:sourceAtoms}=parsePredicate(predicate),atoms=sourceAtoms.map(a=>({...a,poly:composeDay(a.poly,residue,period)}));const cuts=new Set<bigint>(),seen=new Set<string>(),certificates:{poly:Poly;squarefree:Poly;chain:Poly[];nodes:[bigint,bigint,number,number][]}[]=[];let used=0;
 for(const atom of atoms){const p=atom.poly,key=p.join(',');if(p.length<2||seen.has(key))continue;seen.add(key);const q=squarefree(p),chain=sturm(q),bound=rootBound(q),stack:Interval[]=[[-bound,bound]],nodes:[bigint,bigint,number,number][]=[];while(stack.length){if(++used>nodeLimit)throw Error('Root subdivision budget exceeded; no partial population is returned');const[a,b]=stack.pop()!,va=variations(chain,a),vb=variations(chain,b);if(va<vb)throw Error('Invalid Sturm variation');nodes.push([a,b,va,vb]);if(va===vb)continue;if(b-a===1n){cuts.add(a);cuts.add(b);}else{const mid=floorDiv(a+b,2n);stack.push([mid,b],[a,mid]);}}certificates.push({poly:p,squarefree:q,chain,nodes});}
 const sorted=[...cuts].sort((a,b)=>a<b?-1:a>b?1:0),cells:([bigint|null,bigint|null])[]=[];if(!sorted.length)cells.push([null,null]);else{cells.push([null,sorted[0]-1n]);sorted.forEach((c,i)=>{cells.push([c,c]);if(i+1<sorted.length&&c+1n<=sorted[i+1]-1n)cells.push([c+1n,sorted[i+1]-1n]);});cells.push([sorted.at(-1)!+1n,null]);}
 const lower=floorDiv(lo-1n-residue,period)+1n,upper=floorDiv(hi-residue,period),intervals:Interval[]=[];for(const[a,b]of cells){const left=a===null||a<lower?lower:a,right=b===null||b>upper?upper:b;if(left>right)continue;if(!truth(tree,atoms.map(t=>relationHolds(evaluatePolynomial(t.poly,left),t.relation))))continue;if(intervals.length&&intervals.at(-1)![1]+1n===left)intervals.at(-1)![1]=right;else intervals.push([left,right]);}
 let count=0n,selected:bigint|null=null,remaining=rank;for(const[a,b]of intervals){const size=b-a+1n;count+=size;if(selected===null){if(remaining<size)selected=residue+period*(a+remaining);else remaining-=size;}}
 return {schema:'dresden-browser-polynomial-calendar/1',sourcePredicate:predicate,chart:{residue,period},bounds:[lo,hi],rank,count,selected,parameterIntervals:intervals,dayIntervals:intervals.map(([a,b])=>({first:residue+period*a,last:residue+period*b,stride:period,count:b-a+1n})),transportedAtoms:atoms,rootNodes:used,certificates,completeWithinDeclaredModel:true,proofScope:{chartAndPredicateMathematics:'Lean 4.20.0; standard axioms only',producer:'Exact arithmetic; independently compared with Python',sturmCompleteness:'Not formalized',parserAndInterpreter:'Not formalized'}};
}
function factors(roots:bigint[]){let p=[1n];for(const r of roots){const q=Array<bigint>(p.length+1).fill(0n);p.forEach((c,i)=>{q[i]-=r*c;q[i+1]+=c;});p=q;}return p.map(String);}
export const polynomialPresets=[
 {label:'Two separate day windows',predicate:{op:'or',args:[{poly:factors([18980n,189800n]),relation:'<='},{poly:factors([379600n,474500n]),relation:'<='}]}},
 {label:'Repeated roots and excluded days',predicate:{poly:factors([37960n,37960n,94900n,132860n]),relation:'!='}},
 {label:'A window beyond 10²⁴ days',predicate:{poly:factors([10n**24n,10n**24n+10n**20n]),relation:'<='}},
 {label:'Eight-degree sign domain',predicate:{poly:factors([1n,2n,4n,7n,11n,16n,22n,29n].map(x=>18980n*x)),relation:'<='}},
 {label:'Every matching calendar day',predicate:true},
 {label:'Empty polynomial condition',predicate:false}
];
