/* Exact rational integral-family calculations. No network or numerical proof dependencies. */
(function(root){'use strict';
function gcd(a,b){a=a<0n?-a:a;b=b<0n?-b:b;while(b){const t=a%b;a=b;b=t;}return a;}
class Rational {
 constructor(n=0n,d=1n){if(n instanceof Rational){this.n=n.n;this.d=n.d;return;}if(typeof n==='string'&&n.includes('/')){const parts=n.split('/');if(parts.length!==2)throw Error('Use an integer or fraction');n=BigInt(parts[0]);d=BigInt(parts[1]);}else n=BigInt(n);d=BigInt(d);if(!d)throw Error('Zero denominator');if(d<0n){n=-n;d=-d;}const g=gcd(n,d);this.n=n/g;this.d=d/g;}
 add(b){b=Q(b);return new Rational(this.n*b.d+b.n*this.d,this.d*b.d);}
 sub(b){b=Q(b);return new Rational(this.n*b.d-b.n*this.d,this.d*b.d);}
 mul(b){b=Q(b);return new Rational(this.n*b.n,this.d*b.d);}
 div(b){b=Q(b);return new Rational(this.n*b.d,this.d*b.n);}
 pow(n){if(!Number.isInteger(n)||n<0)throw Error('Nonnegative integer power required');return new Rational(this.n**BigInt(n),this.d**BigInt(n));}
 toString(){return this.d===1n?String(this.n):`${this.n}/${this.d}`;}
 toNumber(){if(!this.n)return 0;const a=(this.n<0n?-this.n:this.n).toString(),b=this.d.toString();return (this.n<0n?-1:1)*Number(a.slice(0,16))/Number(b.slice(0,16))*10**((a.length-Math.min(16,a.length))-(b.length-Math.min(16,b.length)));}
 logAbs(){if(!this.n)return -Infinity;const a=(this.n<0n?-this.n:this.n).toString(),b=this.d.toString();return Math.log(Number(a.slice(0,16)))-Math.log(Number(b.slice(0,16)))+((a.length-Math.min(16,a.length))-(b.length-Math.min(16,b.length)))*Math.LN10;}
}
const Q=value=>value instanceof Rational?value:new Rational(value);
function integer(n,lo,hi){if(!Number.isInteger(n)||n<lo||n>hi)throw Error(`Choose an integer from ${lo} to ${hi}`);return n;}
function factorial(n){integer(n,0,256);let a=1n;for(let j=2n;j<=BigInt(n);j++)a*=j;return a;}
function binomial(n,k){let a=1n;for(let j=1;j<=k;j++)a=a*BigInt(n-j+1)/BigInt(j);return a;}
function angleMoment(j,denominator){integer(j,1,16);integer(denominator,3,1000000);return {j,denominator,coefficient:new Rational(4n**BigInt(j),factorial(2*j)*BigInt(denominator)**BigInt(2*j)).toString(),pi_power:2*j,domain:'principal real arcsine; |theta|<pi/2; absolutely convergent series'};}
function momentCoefficients(j,terms=20){integer(j,1,16);integer(terms,j,64);const e=Array.from({length:j},(_,i)=>Q(i?0:1)),out=[];for(let n=1;n<=terms;n++){out.push(e[j-1].div(BigInt(n*n)*binomial(2*n,n)).toString());for(let r=Math.min(j-1,n);r>0;r--)e[r]=e[r].add(e[r-1].div(n*n));}return out;}
function rationalMoment(j,t,terms=20){t=Q(t);integer(j,1,16);integer(terms,j,64);if(t.n*t.n>=4n*t.d*t.d)throw Error('Choose |t|<2');const coefficients=momentCoefficients(j,terms);let partial=Q(0);for(let n=1;n<=terms;n++)partial=partial.add(Q(coefficients[n-1]).mul(t.pow(2*n)));const rho=t.pow(2).div(4),tail=Q(3).mul(new Rational(2n**BigInt(j-1),factorial(j-1))).mul(rho.pow(terms+1)).div(Q(terms+1).mul(Q(1).sub(rho)));return {j,t:t.toString(),terms,partial:partial.toString(),lower:partial.toString(),upper:partial.add(tail).toString(),tail:tail.toString(),arithmetic:'exact BigInt rationals; elementary analytic tail bound'};}
function cancellation(r,s){integer(s,2,16);integer(r,1,s-1);const D=2n**BigInt(2*r+2*s-2),A=D+2n**BigInt(2*r-1)+2n**BigInt(2*s-1),multipliers=[];for(let j=1;j<=s;j++){const z=new Rational(1n,2n**BigInt(2*j-1));multipliers.push(Q(1).add(Q(D-A).mul(z)).add(Q(D).mul(z.pow(2))).toString());}return {r,s,A:String(A),D:String(D),multipliers};}
function bernoulli(n){const out=[Q(1)];for(let k=1;k<=n;k++){let total=Q(0);for(let j=0;j<k;j++)total=total.add(Q(binomial(k+1,j)).mul(out[j]));out.push(total.mul(-1).div(k+1));}return out[n];}
function e8Factors(weight){integer(weight,2,16);const roots=new Rational(8n,30n**BigInt(weight-1));let reflection=Q(1);for(const p of [2,3,5])reflection=reflection.mul(new Rational(1n,BigInt(p)**BigInt(weight-1)).sub(1));const total=roots.add(reflection),out={weight,root_factor:roots.toString(),reflection_factor:reflection.toString(),combined_factor:total.toString()};if(weight%2===0){const z=Q(weight/2%2?1:-1).mul(2n**BigInt(weight-1)).mul(bernoulli(weight)).div(factorial(weight));out.root_pi=roots.mul(z).toString();out.reflection_pi=reflection.mul(z).toString();out.combined_pi=total.mul(z).toString();}return out;}
const lambdaCache=[Q(1)];
function lambdaCoefficients(order){integer(order,0,64);for(let m=lambdaCache.length;m<=order;m++){let sum=Q(0);for(let k=1;k<=m;k++)sum=sum.add(lambdaCache[m-k].div(factorial(2*k+1)));lambdaCache.push(sum.mul(-1));}return lambdaCache.slice(0,order+1);}
function generatingMultiplier(k,j,kind){const a=4n**BigInt(k),p=base=>BigInt(base)**BigInt(j),t=new Rational(a,2n-a);if(kind==='second')return new Rational(-1n,72n*p(36)).add(new Rational(1n-a,18n*p(9))).add(new Rational(1n,8n*p(4))).add(new Rational(a-1n,2n)).add(new Rational(a*(6n-a),9n*(2n-a)).mul(new Rational(4n,9n).pow(j))).add(new Rational(a*(3n*a-2n),2n-a).mul(p(4)));
 return t.add(1).div(9n*p(9)).add(t.mul(2).add(3).sub(new Rational(4n,a)).div(8n*p(4))).add(new Rational(4n,a).sub(1).div(72n*p(36))).add(new Rational(1n,8n*a*p(16))).sub(new Rational(1n,72n*a*p(144)));}
function generatingFamily(m,kind='second'){integer(m,0,64);if(!['second','supplementary'].includes(kind))throw Error('Choose family S or B');const lambdas=lambdaCoefficients(m),harmonic=[],zetas=[];for(let j=0;j<=m;j++){const scale=lambdas[m-j].div(3n**BigInt(2*(m-j)));harmonic.push({e_index:j,pi_power:2*(m-j),coefficient:scale.toString()});zetas.push({zeta_order:2*j+3,pi_power:2*(m-j),coefficient:scale.mul(j%2?-1:1).mul(generatingMultiplier(m-j,j,kind)).toString()});}const b=2n**BigInt(2*m+1);return {family:kind,m,weight:2*m+3,harmonic_coefficients:harmonic,zeta_coefficients:zetas,harmonic_insertions:kind==='second'?{H_2n:'1',H_n:String(b),inverse_n:'0'}:{H_2n:'0',H_n:Q(1).add(new Rational(1n,b)).toString(),inverse_n:'-1/2'},strict_sign:kind==='second'?(m%2?-1:1):null};}
const api={Rational,Q,gcd,factorial,binomial,angleMoment,momentCoefficients,rationalMoment,cancellation,bernoulli,e8Factors,lambdaCoefficients,generatingFamily};
if(typeof module!=='undefined'&&module.exports)module.exports=api;else root.IntegralEngine=api;
})(typeof globalThis!=='undefined'?globalThis:this);
