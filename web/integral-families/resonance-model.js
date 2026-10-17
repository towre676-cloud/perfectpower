// Exact integer endpoints; real coordinates and interpolations are display only.
export const TAU=2*Math.PI;
export function phaseImage(a,n,p){if(![a,n,p].every(Number.isSafeInteger)||n<1||p<0||!Number.isSafeInteger(a*p))throw Error('Safe integer phase data required');return ((a*p)%n+n)%n;}
export function phaseProjection(a,n){const t=TAU*phaseImage(a,n,1)/n;return [.88*Math.cos(t),.88*Math.sin(t),.28*Math.sin(7*t)];}
export function phaseMapPoint(row,p,u){if(!Number.isFinite(u)||u<0||u>1)throw Error('Invalid progress');const a=phaseProjection(row.exponent,row.conductor),b=phaseProjection(phaseImage(row.exponent,row.conductor,p),row.conductor);return a.map((x,i)=>x+(b[i]-x)*u);}
export function phaseRows(d,kind){if(kind==='cyclotomic')return d.calculations.primitive_phases;if(kind==='fiber')return d.branches.map(r=>({...r,conductor:443520}));if(kind==='bridge')return d.calculations.eigen_exponents.map(exponent=>({exponent,conductor:30}));throw Error('Unknown phase population');}
export function mapProgress(t){t=((t%14)+14)%14;if(t<3)return 0;if(t<8){const x=(t-3)/5;return x*x*(3-2*x);}if(t<12)return 1;const x=(t-12)/2;return 1-x*x*(3-2*x);}
export function successor(d,i,k){if(!Number.isInteger(k)||k<0||!d.roots[i])throw Error('Invalid Coxeter step');for(let j=0;j<k%30;j++)i=d.roots[i].next;return i;}
export function rootMapPoint(d,i,k,u=0){if(!Number.isFinite(u)||u<0||u>1)throw Error('Invalid interpolation');const a=d.roots[successor(d,i,k)],b=d.roots[a.next];return [(a.x+(b.x-a.x)*u)*.93,(a.y+(b.y-a.y)*u)*.93,(a.z+(b.z-a.z)*u)*.62];}
export function rootMotion(t,reduced=false){const tick=Math.floor(t/1.6),f=t/1.6%1,x=reduced?0:Math.max(0,(f-.65)/.35);return {tick,progress:x*x*(3-2*x)};}
export function rationalNumber(s){const [n,d=1]=String(s).split('/');return Number(n)/Number(d);}
export function calculationFrame(d,t,{map=null,terms=null,order=1}={}){const progress=map??mapProgress(t),n=terms??(1+Math.floor(t*2)%128),sample=d.calculations.series[n-1];if(!sample||!Number.isInteger(order)||order<1||order>3)throw Error('Invalid series sample');return {progress,terms:n,order,trace:sample.trace,partial:sample.partial[order-1],target:rationalNumber(d.calculations.profiles.reflection.moments[order])*Math.PI**(2*order),stage:progress===0?'Source phases':progress===1?'Exact power-map image':'Display interpolation',interpolating:progress!==0&&progress!==1};}
