import {Q,q,pmul,pderiv,peval,nonnegativeCertificate,pathTensionBound,biasEnvelope,thermalToy,classicalScalingScreen,positiveDefinite,solve,dot,matvec} from "./cp_wall_tools.mjs";
let checks=0;
function assert(ok,label){if(!ok)throw Error(label);checks++;}
function eq(a,b,label){assert(q(a).cmp(b)===0,label);}
function fails(fn,label){let failed=false;try{fn();}catch{failed=true;}assert(failed,label);}
eq(new Q("-6/-8"),"3/4","sign and gcd normalization");
eq(q("2/3").add("5/7"),"29/21","rational addition");
fails(()=>q(0.1),"floating-point rational rejected");
fails(()=>new Q("1/0"),"zero denominator rejected");
eq(peval(pmul([-1,2],[-1,2]),"1/3"),"1/9","polynomial product");
eq(peval(pderiv([1,2,3]),2),14,"derivative");
assert(nonnegativeCertificate([1,-2,2]).certified,"positive Bernstein certificate");
assert(!nonnegativeCertificate([-1]).certified,"negative polynomial refused");
const path=pathTensionBound([0,0,4,-8,4],[[-1,2]]);
eq(path.integral_potential,"2/15","potential integral");
eq(path.integral_speed_squared,4,"speed integral");
eq(path.tension_upper_squared,"16/15","tension upper bound");
assert(q("8/9").cmp(path.tension_upper_squared)<0,"known quartic kink lies below bound");
fails(()=>pathTensionBound([1],[[-1,2]]),"nonzero endpoint rejected");
fails(()=>pathTensionBound([0,1,-1],[[-1,2]]),"nonstationary endpoint rejected");
fails(()=>pathTensionBound([0,0,-1,2,-1],[[-1,2]]),"negative excess rejected");
fails(()=>pathTensionBound([0,0,4,-8,4],[[1]]),"constant path rejected");
eq(pathTensionBound([0,0,4,-8,4],[[-1,2],[0,3]]).tension_upper_squared,"52/15","multifield speed");
const R=[[1,0,0],[0,2,0],[0,0,3]],b=[2,2,2];
const uncon=biasEnvelope(R,b);
eq(uncon.maximum_bias_squared,"22/3","unconstrained support");
const constrained=biasEnvelope(R,b,[[1,1,0],[2,2,0]],1);
eq(constrained.maximum_bias_squared,"4/3","rank-deficient constraints removed");
assert(constrained.constraint_residuals.every(v=>v.n===0n),"both constraints hold");
eq(biasEnvelope([[1,0],[0,1]],[2,2],[[1,1]]).maximum_bias_squared,0,"quality eliminates all bias");
eq(biasEnvelope(R,b,[[1,1,0]],4).maximum_bias_squared,"16/3","radius scaling");
eq(biasEnvelope(R,b,[],0).maximum_bias_squared,0,"zero radius");
fails(()=>biasEnvelope([[1,2],[0,1]],[1,1]),"nonsymmetric metric rejected");
fails(()=>positiveDefinite([[1,2],[2,1]]),"indefinite metric rejected");
fails(()=>solve([[1,1],[2,2]],[1,2]),"singular solve rejected");
fails(()=>biasEnvelope(R,b,[[1]]),"constraint dimension rejected");
fails(()=>biasEnvelope(R,b,[],-1),"negative budget rejected");
eq(thermalToy(2,9,3).critical_temperature_squared,6,"thermal toy critical point");
fails(()=>thermalToy(1,1,0),"unphysical thermal coefficient rejected");
eq(classicalScalingScreen(3,1,10).domination_H,"1/100","scaling domination convention");
eq(classicalScalingScreen(3,1,10).required_bias_strictly_greater_than,3,"deadline bias convention");
// Generated SPD metrics check projection identities beyond the hand-worked diagonal.
for(let k=1;k<=24;k++){
  const S=[[1,k%3,0],[0,1,k%2],[0,0,1]];
  const metric=Array.from({length:3},(_,i)=>Array.from({length:3},(_,j)=>
    S.reduce((sum,row)=>sum+row[i]*row[j],0)+(i===j?1:0)));
  const bb=[k,1-k,2],A=[[1,k%2,1],[2,2*(k%2),2]];
  const out=biasEnvelope(metric,bb,A);
  eq(dot(out.projected_direction,matvec(metric,out.projected_direction)),out.direction_norm_squared,"generated norm "+k);
  assert(out.constraint_residuals.every(v=>v.n===0n),"generated constraints "+k);
  assert(out.maximum_bias_squared.cmp(biasEnvelope(metric,bb).maximum_bias_squared)<=0,"restriction cannot enlarge support "+k);
}
console.log(JSON.stringify({checks,status:"passed",arithmetic:"BigInt rational",scope:"module checks only; no full repository suite or physics matching"}));
