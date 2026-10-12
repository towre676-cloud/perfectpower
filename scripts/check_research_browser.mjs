import assert from 'node:assert/strict';
import fs from 'node:fs';
import {compute,parseExact} from '../web/research-counting/exact.mjs';
let checks=0,seed=22763;
const random=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed%n;};
for(const name of ['monomial','crt','digits']){
 const raw=fs.readFileSync(new URL('../examples/research_counting/'+name+'.json',import.meta.url),'utf8');
 const receipt=JSON.parse(fs.readFileSync(new URL('../receipts/research_counting/'+name+'.json',import.meta.url),'utf8'));
 assert.equal(compute(name,parseExact(raw)).count,receipt.count);checks++;
}
for(let trial=0;trial<80;trial++){
 const gs=Array.from({length:1+random(4)},()=>Array.from({length:3},()=>random(5))),degree=random(13);
 const objects=new Set();for(const g of gs)for(let a=0;a<=g[0];a++)for(let b=0;b<=g[1];b++)for(let c=0;c<=g[2];c++)if(a+b+c===degree)objects.add([a,b,c].join(','));
 assert.equal(compute('monomial',{generators:gs,degree}).count,String(objects.size));checks++;
}
for(let trial=0;trial<100;trial++){
 const constraints=[4,6,5].map(modulus=>({modulus,allowed:Array.from({length:modulus},(_,i)=>i).filter(()=>random(2))}));
 let count=0;for(let x=-100;x<=100;x++)if(constraints.every(c=>c.allowed.includes((x%c.modulus+c.modulus)%c.modulus)))count++;
 assert.equal(compute('crt',{lo:-100,hi:100,constraints}).count,String(count));checks++;
}
assert.equal(parseExact('{"hi":1000000000000000000000000000000,"text":"n=123"}').hi,'1000000000000000000000000000000');checks++;
assert.throws(()=>compute('crt',{lo:0,hi:1e30,constraints:[]}));checks++;
assert.equal(compute('monomial',parseExact('{"generators":[[1000000000000000000000000000000]],"degree":500000000000000000000000000000}')).count,'1');checks++;
console.log(JSON.stringify({checks,status:'passed',arithmetic:'BigInt',browser_runtime_exercised:false}));
