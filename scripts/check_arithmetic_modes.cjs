const assert=require('node:assert/strict'),fs=require('node:fs');
const engine=require('../web/arithmetic-transport/modes-engine.js');
const atlas=JSON.parse(fs.readFileSync('receipts/arithmetic_modes/atlas.json','utf8'));let cases=0;
for(const c of atlas.cases)for(const row of c.filtration){
 const m=engine.build({...c,height_cap:row.height});assert.equal(String(m.root.count),row.count);
 const A=engine.amplitude(m.root.hist);for(let a=0;a<4;a++){
  const coeff=A.entries.find(x=>x.axis===a);assert.equal(String(coeff?.re||0n),row.amplitude_coefficients[a][0]);assert.equal(String(coeff?.im||0n),row.amplitude_coefficients[a][1]);}
 if(m.root.count){for(const rank of [0n,m.root.count-1n]){const word=engine.unrank(m,rank);assert.equal(word.length,m.L);let node=m.root;for(const j of word){node=node.edges.find(e=>e[0]===j)[1];assert(node.value[0]<=m.cap&&node.value[1]<=m.cap);}assert(node.c.every((n,j)=>n===m.modes[j].quota));}}
 cases++;
}
for(let a=0;a<16;a++)for(let b=0;b<16;b++)for(let c=0;c<16;c++)assert.equal(engine.mul(engine.mul(a,b),c),engine.mul(a,engine.mul(b,c)));
fs.writeFileSync('receipts/arithmetic_modes/browser.json',JSON.stringify({status:'passed',cross_language_cases:cases,group_associativity_cases:4096,scope:'BigInt browser counts and Pauli coefficients match exact Python height sweeps; browser layout not exercised'},null,2)+'\n');console.log(JSON.stringify({status:'passed',cases}));
