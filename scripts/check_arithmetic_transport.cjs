const assert=require('node:assert/strict');
const fs=require('node:fs');
const engine=require('../web/arithmetic-transport/engine.js');
let cases=0;
function enumerate(p,q,d,u=0,v=0){if(BigInt(p)**BigInt(u)>BigInt(q)**BigInt(v))return 0n;if(u===d&&v===d)return 1n;return(u<d?enumerate(p,q,d,u+1,v):0n)+(v<d?enumerate(p,q,d,u,v+1):0n);}
for(const[p,q]of [[2,3],[2,5],[3,5],[5,7]])for(let d=1;d<=8;d++){
 const m=engine.build(p,q,d);assert.equal(m.count,enumerate(p,q,d));
 for(const draw of [()=>0n,n=>n-1n]){const path=engine.sample(m,draw);assert.equal(path.length,2*d+1);for(const[u,v]of path)assert(m.P[u]<=m.Q[v]);assert.deepEqual(path.at(-1),[d,d]);}
 cases++;
}
const m=engine.build(2,3,32);assert.equal(m.count,493058134611291081n);
assert.throws(()=>engine.build(2,3,65));
fs.mkdirSync('receipts/arithmetic_transport',{recursive:true});
fs.writeFileSync('receipts/arithmetic_transport/browser.json',JSON.stringify({status:'passed',exact_cases:cases,edge_rank_paths:2*cases,scope:'BigInt counts against explicit enumeration and endpoint rank sampling; browser layout not exercised'},null,2)+'\n');
console.log(JSON.stringify({status:'passed',cases}));
