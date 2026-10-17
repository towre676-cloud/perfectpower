/* Shared display mathematics. Exact selected integer values use IntegralEngine. */
(function(root){'use strict';
const E=typeof module!=='undefined'&&module.exports?require('./engine.js'):root.IntegralEngine;
const TAU=2*Math.PI;
function integer(x,a,b){if(!Number.isInteger(x)||x<a||x>b)throw Error(`Integer ${a}–${b} required`);return x;}
function gcd(a,b){while(b){const t=a%b;a=b;b=t;}return a;}
function branches(power=1){integer(power,1,264);return Array.from({length:264},(_,j)=>{const exponent=1+1680*j;return {id:j,exponent,primitive:gcd(exponent,443520)===1,angle:TAU*((power*exponent)%443520)/443520};});}
function spectrum(kind,rank=7){
 if(kind==='E8')return {rank:8,h:30,exponents:[1,7,11,13,17,19,23,29],zero:2};
 if(!['B','C'].includes(kind))throw Error('Choose E8, B or C');integer(rank,1,31);
 return {rank,h:2*rank,exponents:Array.from({length:rank},(_,i)=>2*i+1),zero:1+Math.log2(rank+1)};
}
function factors(kind,rank,weight){if(!Number.isFinite(weight)||weight<=1)throw Error('Weight greater than one required');const spec=spectrum(kind,rank),t=weight-1,roots=spec.rank/spec.h**t;const cartan=kind==='E8'?-([2,3,5].reduce((a,p)=>a*(p**t-1),1))/30**t:1/(2*rank)**t-1/rank**t;return {roots,cartan,total:roots+cartan,zero:spec.zero};}
function exactFactors(kind,rank,weight){integer(weight,2,16);const spec=spectrum(kind,rank);if(kind==='E8'){const x=E.e8Factors(weight);return {roots:x.root_factor,cartan:x.reflection_factor,total:x.combined_factor};}const roots=E.Q(spec.rank).div(BigInt(spec.h)**BigInt(weight-1)),cartan=E.Q(1).div(BigInt(spec.h)**BigInt(weight-1)).sub(E.Q(1).div(BigInt(rank)**BigInt(weight-1)));return {roots:roots.toString(),cartan:cartan.toString(),total:roots.add(cartan).toString()};}
function density(kind,rank,weight,t){if(!Number.isFinite(t)||t<=0)throw Error('Positive log coordinate required');const spec=spectrum(kind,rank),x=Math.exp(-t),rootDensity=spec.rank*spec.h*Math.exp(-spec.h*t)/(-Math.expm1(-spec.h*t));let cartanDensity=0;for(const m of spec.exponents){const c=Math.cos(TAU*m/spec.h);cartanDensity+=x*(c-x)/(1-2*x*c+x*x);}return t**(weight-1)*(rootDensity+cartanDensity);}
function convergence(j,denominator,count=24){integer(j,1,8);integer(denominator,3,221760);integer(count,j,64);const theta=Math.PI/denominator,t=2*Math.sin(theta),moment=E.angleMoment(j,denominator),exact=E.Q(moment.coefficient).toNumber()*Math.PI**moment.pi_power,coefficients=E.momentCoefficients(j,count);let sum=0;return coefficients.map((c,i)=>{const term=E.Q(c).toNumber()*t**(2*(i+1));sum+=term;return {n:i+1,ratio:term/exact,cumulative:sum/exact,logRatio:term>0?(E.Q(c).logAbs()+2*(i+1)*Math.log(t)-Math.log(exact))/Math.LN10:null};}).filter(row=>row.n>=j);}
const api={branches,spectrum,factors,exactFactors,density,convergence,gcd};if(typeof module!=='undefined'&&module.exports)module.exports=api;else root.AtlasModel=api;
})(typeof globalThis!=='undefined'?globalThis:this);
