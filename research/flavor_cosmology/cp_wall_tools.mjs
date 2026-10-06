// Exact conditional CP-wall tools. No external dependencies; Node ESM or V8.
// Inputs are rational polynomials and supplied response matrices, not matched physics.
export class Q {
  constructor(n, d=1n) {
    if (n instanceof Q) { this.n=n.n; this.d=n.d; return; }
    if (typeof n==="string" && n.includes("/")) {
      const parts=n.split("/"); if(parts.length!==2) throw Error("invalid rational");
      n=parts[0]; d=parts[1];
    }
    if(typeof n==="number" && !Number.isSafeInteger(n)) throw Error("rational input requires an integer or a fraction string");
    if(typeof d==="number" && !Number.isSafeInteger(d)) throw Error("invalid denominator");
    n=BigInt(n); d=BigInt(d); if(d===0n) throw Error("zero denominator");
    if(d<0n) { n=-n; d=-d; }
    const gcd=(a,b)=>{a=a<0n?-a:a; while(b){[a,b]=[b,a%b];} return a;};
    const g=gcd(n,d); this.n=n/g; this.d=d/g;
  }
  add(v){v=q(v); return new Q(this.n*v.d+v.n*this.d,this.d*v.d);}
  sub(v){return this.add(q(v).neg());}
  mul(v){v=q(v);return new Q(this.n*v.n,this.d*v.d);}
  div(v){v=q(v);return new Q(this.n*v.d,this.d*v.n);}
  neg(){return new Q(-this.n,this.d);}
  cmp(v){v=q(v);const s=this.n*v.d-v.n*this.d;return s<0n?-1:s>0n?1:0;}
  toString(){return this.d===1n?String(this.n):this.n+"/"+this.d;}
  toJSON(){return this.toString();}
}
export const q=v=>v instanceof Q?v:new Q(v);
const zero=()=>q(0);
const trim=p=>{p=p.map(q);while(p.length>1 && p.at(-1).n===0n)p.pop();return p.length?p:[zero()];};
export const padd=(a,b)=>trim(Array.from({length:Math.max(a.length,b.length)},(_,i)=>q(a[i]??0).add(b[i]??0)));
export const pscale=(p,s)=>trim(p.map(v=>q(v).mul(s)));
export function pmul(a,b){
  const out=Array.from({length:a.length+b.length-1},zero);
  a.forEach((x,i)=>b.forEach((y,j)=>out[i+j]=out[i+j].add(q(x).mul(y))));
  return trim(out);
}
export const pderiv=p=>trim(p.slice(1).map((v,i)=>q(v).mul(i+1)));
export const peval=(p,t)=>p.reduceRight((s,v)=>s.mul(t).add(v),zero());
export const pintegral=p=>p.reduce((s,v,i)=>s.add(q(v).div(i+1)),zero());
export function pdivide(a,b){
  a=trim(a);b=trim(b); if(b.at(-1).n===0n)throw Error("zero polynomial divisor");
  const quotient=Array.from({length:Math.max(1,a.length-b.length+1)},zero);
  while(a.length>=b.length && !(a.length===1 && a[0].n===0n)){
    const i=a.length-b.length,c=a.at(-1).div(b.at(-1));quotient[i]=c;
    a=padd(a,Array.from({length:i},zero).concat(pscale(b,c.neg())));
  }
  return {quotient:trim(quotient),remainder:trim(a)};
}
function choose(n,k){
  if(k<0||k>n)return 0n;let x=1n;
  for(let i=1;i<=k;i++)x=x*BigInt(n-k+i)/BigInt(i);
  return x;
}
export function bernstein(p){
  p=trim(p);const n=p.length-1;
  return Array.from({length:n+1},(_,k)=>p.slice(0,k+1).reduce(
    (s,v,i)=>s.add(v.mul(new Q(choose(k,i),choose(n,i)))),zero()));
}
// Conservative certificate: failure means "not certified", not negativity.
export function nonnegativeCertificate(p){
  const b=bernstein(p);
  return {certified:b.every(v=>v.cmp(0)>=0),bernstein_coefficients:b};
}
export function pathTensionBound(potential,path){
  const v=trim(potential);
  if(!Array.isArray(path)||path.length===0)throw Error("empty path");
  if(peval(v,0).cmp(0)||peval(v,1).cmp(0)||
     peval(pderiv(v),0).cmp(0)||peval(pderiv(v),1).cmp(0))
    throw Error("potential must vanish quadratically at both endpoints");
  // A polynomial vanishing with its derivative at 0 and 1 has this factor.
  const f=pdivide(v,[0,0,1,-2,1]);
  if(f.remainder.some(x=>x.n!==0n))throw Error("endpoint factorization failed");
  const certificate=nonnegativeCertificate(f.quotient);
  if(!certificate.certified)throw Error("nonnegative path potential not certified");
  const speed2=path.reduce((s,p)=>padd(s,pmul(pderiv(p),pderiv(p))),[0]);
  const V=pintegral(v),K=pintegral(speed2);
  if(V.cmp(0)<0||K.cmp(0)<=0)throw Error("invalid path integral");
  return {
    scope:"Conditional variational upper bound between supplied degenerate global vacua; V must equal their potential excess along the supplied path with Euclidean canonical metric. Global minimality and composition are caller hypotheses.",
    potential_excess:v,path_coordinates:path.map(trim),
    endpoint_potential:[peval(v,0),peval(v,1)],
    endpoint_derivative:[peval(pderiv(v),0),peval(pderiv(v),1)],
    residual_potential:f.quotient,nonnegative:certificate,
    integral_potential:V,integral_speed_squared:K,
    tension_upper_squared:V.mul(K).mul(2)
  };
}
export const dot=(a,b)=>{
  if(a.length!==b.length)throw Error("dimension mismatch");
  return a.reduce((s,v,i)=>s.add(q(v).mul(b[i])),zero());
};
export function matvec(A,x){return A.map(row=>dot(row,x));}
function matrix(A){
  if(!Array.isArray(A)||A.length===0||A.some(row=>!Array.isArray(row)||row.length!==A.length))throw Error("square matrix required");
  return A.map(row=>row.map(q));
}
export function positiveDefinite(A){
  A=matrix(A);const n=A.length;
  if(A.some((r,i)=>r.some((v,j)=>v.cmp(A[j][i])!==0)))throw Error("symmetric matrix required");
  const L=Array.from({length:n},()=>Array.from({length:n},zero)),D=[];
  for(let i=0;i<n;i++){
    L[i][i]=q(1);
    D[i]=A[i][i].sub(D.reduce((s,d,k)=>s.add(d.mul(L[i][k]).mul(L[i][k])),zero()));
    if(D[i].cmp(0)<=0)throw Error("positive definite metric required");
    for(let j=i+1;j<n;j++)
      L[j][i]=A[j][i].sub(D.slice(0,i).reduce((s,d,k)=>s.add(d.mul(L[j][k]).mul(L[i][k])),zero())).div(D[i]);
  }
  return {L,D};
}
export function solve(A,b){
  A=matrix(A);if(A.length!==b.length)throw Error("dimension mismatch");
  const n=A.length,M=A.map((row,i)=>[...row,q(b[i])]);
  for(let k=0;k<n;k++){
    const pivot=M.findIndex((row,i)=>i>=k&&row[k].n!==0n);
    if(pivot<0)throw Error("singular system");
    [M[k],M[pivot]]=[M[pivot],M[k]];
    const d=M[k][k];M[k]=M[k].map(v=>v.div(d));
    for(let i=0;i<n;i++)if(i!==k){
      const c=M[i][k];M[i]=M[i].map((v,j)=>v.sub(c.mul(M[k][j])));
    }
  }
  return M.map(row=>row[n]);
}
function independentRows(A,n){
  const rows=A.map(row=>{if(row.length!==n)throw Error("constraint dimension mismatch");return row.map(q);});
  const selected=[],basis=[];
  for(const original of rows){
    const r=original.slice();
    for(const e of basis){const c=r[e.pivot];for(let j=0;j<n;j++)r[j]=r[j].sub(c.mul(e.row[j]));}
    const pivot=r.findIndex(v=>v.n!==0n);
    if(pivot>=0){
      const d=r[pivot],row=r.map(v=>v.div(d));
      basis.push({pivot,row});selected.push(original);
    }
  }
  return selected;
}
export function biasEnvelope(metric,bias,constraints=[],radiusSquared=1){
  const R=matrix(metric),n=R.length;positiveDefinite(R);
  if(bias.length!==n)throw Error("bias dimension mismatch");
  const rho=q(radiusSquared);if(rho.cmp(0)<0)throw Error("negative radius squared");
  const b=bias.map(q),A=independentRows(constraints,n),x=solve(R,b);
  let z=x;
  if(A.length){
    const dual=A.map(a=>solve(R,a));
    const gram=A.map(a=>dual.map(d=>dot(a,d)));
    const multiplier=solve(gram,matvec(A,x));
    z=x.map((v,j)=>v.sub(dual.reduce((s,d,i)=>s.add(d[j].mul(multiplier[i])),zero())));
  }
  const k=dot(b,z);
  if(k.cmp(0)<0||dot(z,matvec(R,z)).cmp(k)!==0||matvec(A,z).some(v=>v.n!==0n))
    throw Error("projection identity failed");
  return {
    scope:"Exact linear-response optimization for supplied homogeneous constraints and coefficient ellipsoid; no response is calculated here.",
    metric:R,bias_vector:b,independent_constraints:A,radius_squared:rho,
    projected_direction:z,direction_norm_squared:k,
    maximum_bias_squared:rho.mul(k),
    constraint_residuals:matvec(constraints,z),
    witness_rule:k.n===0n?"No allowed linear bias direction.":"c = sqrt(radius_squared/direction_norm_squared) * projected_direction."
  };
}
export function thermalToy(lambda,vSquared,thermalCoefficient){
  const l=q(lambda),v=q(vSquared),c=q(thermalCoefficient);
  if(l.cmp(0)<=0||v.cmp(0)<=0||c.cmp(0)<=0)throw Error("positive toy inputs required");
  return {
    scope:"One real CP-odd scalar only: V=lambda*(a^2-v^2)^2/4 + c*T^2*a^2/2. Not a repository thermal matching.",
    critical_temperature_squared:l.mul(v).div(c),
    broken_minimum_squared:"v^2 - c*T^2/lambda when positive",
    conjugate_energy_bias:"0"
  };
}
export function classicalScalingScreen(sigma,Hdeadline,planck,area=1,annihilation=1){
  const s=q(sigma),h=q(Hdeadline),m=q(planck),a=q(area),c=q(annihilation);
  if([s,h,m,a,c].some(x=>x.cmp(0)<=0))throw Error("positive scaling inputs required");
  const Hdom=a.mul(s).div(m.mul(m).mul(3));
  const Hrequired=h.cmp(Hdom)>=0?h:Hdom;
  return {
    scope:"Phenomenological classical horizon-curvature convention rho_wall=area*sigma*H, H_ann=DeltaV/(annihilation*sigma); not a network simulation or rigorous viability bound.",
    domination_H:Hdom,
    required_bias_strictly_greater_than:c.mul(s).mul(Hrequired),
    annihilation_law:"H_ann=DeltaV/(annihilation*sigma)",
    recent_simulation_caveat:"arXiv:2504.07902 reports different bias scaling in its simulated model; this screen is not universal."
  };
}
