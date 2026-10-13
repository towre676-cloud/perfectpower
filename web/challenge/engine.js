/* Exact finite challenge engine. Uses the shipped PerfectPower integer factor counter. */
(function(root){'use strict';
function seedCode(text){let n=2166136261;for(const c of text)n=Math.imul(n^c.charCodeAt(0),16777619)>>>0;return n;}
function problem(spec,seed,mode='score'){
 if(spec.variables.some(v=>!Number.isSafeInteger(Number(v.profit))||Number(v.profit)<0)||spec.variables.reduce((s,v)=>s+Number(v.profit),0)>Number.MAX_SAFE_INTEGER)throw Error('Scores exceed exact browser integer range');
 const code=seedCode(seed),offset=code%39,projects=spec.variables.slice(offset,offset+12),resources=spec.resources.map((r,k)=>({...r,min:0,max:Math.min(r.max,Math.max(Math.max(...projects.map(p=>p.costs[k])),Math.floor(projects.reduce((a,p)=>a+p.costs[k],0)*(38+code%9)/100)))}));
 // A ceiling must fit at least the required project in keep mode.
 if(mode==='keep')resources.forEach((r,k)=>r.max=Math.max(r.max,projects[0].costs[k]));
 if(mode==='lean')resources.forEach((r,k)=>r.max=Math.max(projects[0].costs[k],Math.floor(r.max*85/100)));
 return {schema:'pp-challenge/1',seed,mode,projects,resources,required:mode==='keep'?0:null};
}
function evaluate(p,mask){let score=0,use=Array(5).fill(0);p.projects.forEach((v,j)=>{if(mask&(1<<j)){score+=Number(v.profit);use=use.map((n,k)=>n+v.costs[k]);}});return {mask,score,use,valid:use.every((n,k)=>n<=p.resources[k].max)&&(p.required===null||!!(mask&(1<<p.required)))};}
function solve(p){const rows=Array.from({length:2**p.projects.length},(_,m)=>evaluate(p,m)),masks=p.resources.map((r,k)=>rows.map(x=>x.use[k]<=r.max?1:0));if(p.required!==null)masks.push(rows.map(x=>x.mask&(1<<p.required)?1:0));const count=root.PerfectPowerCounter.countMasks(rows.map(()=>1),masks);let best=-1,bestMasks=[];for(const r of rows)if(r.valid){if(r.score>best){best=r.score;bestMasks=[r.mask];}else if(r.score===best)bestMasks.push(r.mask);}return {count:count.toString(),best,bestMasks,rows};}
const api={problem,evaluate,solve,seedCode};root.PerfectPowerChallenge=api;if(typeof module!=='undefined')module.exports=api;
})(globalThis);
