/** Exact browser arithmetic. GPU coordinates are presentation only. */
export const mod = (a: bigint, m: bigint) => ((a % m) + m) % m;
export function gcd(a: bigint,b: bigint): bigint { while(b){[a,b]=[b,a%b];} return a<0n?-a:a; }
function inverse(a:bigint,m:bigint){let [r,s,t,u]=[a,m,1n,0n];while(s){const q=r/s;[r,s]=[s,r-q*s];[t,u]=[u,t-q*u];}if(r!==1n)throw Error('No modular inverse');return mod(t,m);}
export function crt(a:bigint,m:bigint,b:bigint,n:bigint){if(m<=0n||n<=0n)throw Error('Periods must be positive');const g=gcd(m,n);if(mod(b-a,g)!==0n)return null;const k=n/g===1n?0n:mod((b-a)/g*inverse(m/g,n/g),n/g);return {residue:mod(a+m*k,m*(n/g)),modulus:m*(n/g)};}
export function calendarPhase(day:bigint){return {number:Number(mod(day+3n,13n))+1,sign:Number(mod(day+19n,20n)),haab:Number(mod(day+348n,365n)),venus:Number(mod(day,584n))};}
export function longCount(day:bigint){if(day<0n)throw Error('Long Count requires nonnegative elapsed days');const weights=[144000n,7200n,360n,20n,1n];return weights.map(w=>{const digit=day/w;day%=w;return digit.toString();}).join('.');}
function floorDiv(a:bigint,b:bigint){const q=a/b;return a<0n&&a%b!==0n?q-1n:q;}
export function population(residue:bigint,period:bigint,lo:bigint,hi:bigint){return hi<lo?0n:floorDiv(hi-residue,period)-floorDiv(lo-1n-residue,period);}
export function calendarPopulation(day:bigint,hi:bigint,joint=false){return population(mod(day,joint?37960n:18980n),joint?37960n:18980n,0n,hi);}
export function fraction(s:string){const [a,b=1]=s.split('/').map(Number);return a/b;}
export function overlap(stations:number[],steps:number[]){const period=steps.reduce((a,b)=>a+b,0);const bases=[0];steps.slice(0,-1).forEach(s=>bases.push(bases[bases.length-1]+s));const first=new Map<number,number>();bases.forEach(base=>stations.forEach(s=>{const d=base+s,r=d%period;first.set(r,Math.min(d,first.get(r)??d));}));return {period,bases,first,count(hi:bigint){let count=0n;first.forEach(d=>{if(hi>=BigInt(d))count+=(hi-BigInt(d))/BigInt(period)+1n;});return count;}};}
export const signNames=['Imix','Ikʼ','Akʼbal','Kʼan','Chikchan','Kimi','Manikʼ','Lamat','Muluk','Ok','Chuwen','Ebʼ','Bʼen','Ix','Men','Kʼibʼ','Kabʼan','Etzʼnabʼ','Kawak','Ajaw'];
export const haabNames=['Pop','Woʼ','Sip','Sotzʼ','Sek','Xul','Yaxkʼin','Mol','Chʼen','Yax','Sakʼ','Keh','Mak','Kʼankʼin','Muwan','Pax','Kʼayab','Kumkʼu','Wayebʼ'];
export function haabLabel(h:number){return `${h%20} ${haabNames[Math.floor(h/20)]}`;}
export function orderedDrifts(shortIndex:number){let sum=0;return [0,...Array.from({length:5},(_,i)=>{sum+=i===shortIndex?-42356:9720;return sum/100000;})];}
export function integerInput(s:string): bigint {if(!/^\d{1,120}$/.test(s))throw Error('Enter a nonnegative integer of at most 120 digits.');return BigInt(s);}
