// Browser arithmetic uses BigInt throughout counts and residue coordinates.
export function parseExact(raw){
  // Preserve JSON integer tokens before JSON.parse can round them. Quoted
  // strings are consumed first and retained byte-for-byte by this tokenizer.
  return JSON.parse(raw.replace(/("(?:\\.|[^"\\])*")|(-?\d+)(?=[\s,\]}])/g,(whole,string,integer)=>string??JSON.stringify(integer)));
}
function big(x){if(typeof x==='bigint')return x;if(typeof x==='number'&&!Number.isSafeInteger(x))throw Error('Use a decimal string for a large integer.');if(!/^-?\d+$/.test(String(x)))throw Error('Integer required.');return BigInt(x);}
function small(x,min,max){const n=big(x);if(n<BigInt(min)||n>BigInt(max))throw Error('Input exceeds this browser work budget.');return Number(n);}
function mod(a,m){return (a%m+m)%m;}
function gcd(a,b){while(b)[a,b]=[b,a%b];return a;}
function inverse(a,m){let [r,s,x,y]=[a,m,1n,0n];while(s){const q=r/s;[r,s]=[s,r-q*s];[x,y]=[y,x-q*y];}if(r!==1n)throw Error('Inverse does not exist.');return mod(x,m);}
function floor(a,b){let q=a/b;return a<0n&&a%b!==0n?q-1n:q;}
function choose(a,k){if(a<BigInt(k)||a<0n)return 0n;let r=1n;for(let i=1;i<=k;i++)r=r*(a-BigInt(i)+1n)/BigInt(i);return r;}
function box(g,degree){if(degree===null)return g.reduce((r,x)=>r*(x+1n),1n);let answer=0n;for(let mask=0;mask<2**g.length;mask++){let d=degree,odd=0;for(let i=0;i<g.length;i++)if(mask>>i&1){d-=g[i]+1n;odd++;}if(d>=0n)answer+=(odd%2?-1n:1n)*choose(d+BigInt(g.length-1),g.length-1);}return answer;}
export function compute(operation,spec){
 if(operation==='monomial'){
  if(!Array.isArray(spec.generators)||!spec.generators.length||spec.generators.length>8)throw Error('Use one to eight exponent vectors.');
  const n=spec.generators[0].length;if(n<1||n>12)throw Error('Use one to twelve variables.');
  const gs=spec.generators.map(g=>{if(g.length!==n)throw Error('Vector dimensions differ.');return g.map(x=>{x=big(x);if(x<0n)throw Error('Nonnegative exponent required.');return x;});});
  const degree=spec.degree===undefined||spec.degree===null?null:big(spec.degree);if(degree!==null&&degree<0n)throw Error('Nonnegative degree required.');
  const terms=[];for(let mask=1;mask<2**gs.length;mask++){const chosen=gs.filter((_,i)=>mask>>i&1);terms.push([chosen.length%2?1n:-1n,Array.from({length:n},(_,i)=>chosen.reduce((a,g)=>a<g[i]?a:g[i],chosen[0][i]))]);}
  if(terms.length*2**n>1000000)throw Error('Inclusion-exclusion work budget exceeded.');
  return {schema:'pp-browser-monomial/1',count:terms.reduce((r,[sign,g])=>r+sign*box(g,degree),0n).toString(),degree:degree===null?null:degree.toString(),scope:'Exact distinct exponent vectors; browser count uses integer inclusion-exclusion.'};
 }
 if(operation==='crt'){
  const lo=big(spec.lo),hi=big(spec.hi);if(hi<lo)throw Error('Ordered interval required.');let residues=[0n],m=1n,work=0;
  for(const c of spec.constraints){const n=big(c.modulus);if(n<1n)throw Error('Positive modulus required.');const allowed=[...new Set(c.allowed.map(x=>mod(big(x),n).toString()))].map(BigInt),d=gcd(m,n),q=n/d,next=new Set();if((work+=residues.length*allowed.length)>1000000)throw Error('CRT work budget exceeded.');for(const a of residues)for(const b of allowed){if((b-a)%d)continue;const t=q===1n?0n:mod((b-a)/d*inverse(m/d,q),q);next.add(mod(a+m*t,m*q).toString());}m*=q;residues=[...next].map(BigInt);}
  const count=residues.reduce((r,a)=>r+floor(hi-a,m)-floor(lo-1n-a,m),0n);return {schema:'pp-browser-crt/1',count:count.toString(),modulus:m.toString(),residues:residues.map(String),scope:'Exact distinct integers in the inclusive interval.'};
 }
 if(operation==='digits'){
  function values(s){const base=big(s.base);if(base<2n)throw Error('Base at least two required.');const len=small(s.length,0,30),digits=[...new Set(s.digits.map(x=>big(x).toString()))].map(BigInt);if(!digits.length||digits.some(x=>x<0n||x>=base)||digits.length**len>1000000)throw Error('Invalid digits or digit work budget exceeded.');let xs=[0n],p=1n;for(let i=0;i<len;i++){xs=xs.flatMap(x=>digits.map(d=>x+p*d));p*=base;}return xs;}
  const left=values(spec.left),right=values(spec.right);if(left.length*right.length>1000000)throw Error('Pair work budget exceeded.');const stop=spec.stop===undefined?left.reduce((a,b)=>a>b?a:b)+right.reduce((a,b)=>a>b?a:b)+1n:big(spec.stop);if(stop<1n)throw Error('Positive stop required.');let pairs=0n;const sums=new Set();for(const a of left)for(const b of right)if(a+b<stop){sums.add(String(a+b));pairs++;}return {schema:'pp-browser-digits/1',count:String(sums.size),representation_count:String(pairs),collision_excess:String(pairs-BigInt(sums.size)),scope:'Exact finite digit lengths; distinct sums and representations are separate.'};
 }
 throw Error('Unknown population.');
}
