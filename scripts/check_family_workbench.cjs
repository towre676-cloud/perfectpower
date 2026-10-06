// Execute the offline viewer against a minimal DOM; no native layout claim.
const fs=require('fs'),vm=require('vm'),assert=require('assert');
const html=fs.readFileSync(process.argv[2]||'receipts/curve_families/family_workbench.html','utf8');
const json=html.match(/id="data">([\s\S]*?)<\/script>/)[1],script=html.match(/<script>([\s\S]*?)<\/script>/)[1];
class Element{constructor(id){this.id=id;this.value=id==='sample'?'0':'';this.children=[];this.events={};this.textContent=''}
append(child){this.children.push(child);if(this.id==='family'&&!this.value)this.value=child.value}
setAttribute(key,value){this[key]=value}replaceChildren(){this.children=[]}addEventListener(name,fn){this.events[name]=fn}}
const elements=new Map(),get=id=>{if(!elements.has(id))elements.set(id,new Element(id));return elements.get(id)};
get('data').textContent=json;
const document={getElementById:get,createElement:()=>new Element(''),createElementNS:()=>new Element('')};
vm.runInNewContext(script,{document,Math,Number,JSON});
const cases=JSON.parse(json),select=get('family'),slider=get('sample');
for(const name of Object.keys(cases)){
    select.value=name;select.events.change();
    assert(get('dimensions').textContent.includes('observable order '+cases[name].observable.order));
    assert.strictEqual(Number(slider.max),cases[name].continuation.trajectory.length-1);
    slider.value=slider.max;slider.events.input();
    assert(get('value').textContent.includes(JSON.stringify(cases[name].continuation.trajectory.at(-1).observable)));
    assert(get('plot').children.some(e=>e.points));
    assert(get('evidence').textContent.includes('"numerical_error_certified": false'));
}
console.log('Workbench cases, endpoint samples, scalar orders and numerical scope pass; native layout not tested.');
