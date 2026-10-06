// Execute recorded geometry controls against a minimal DOM; no layout claim.
const fs=require('fs'),vm=require('vm'),assert=require('assert');
const html=fs.readFileSync(process.argv[2]||'receipts/curve_structure/structure_workbench.html','utf8');
const payload=html.match(/id="data">([\s\S]*?)<\/script>/)[1],script=html.match(/<script>([\s\S]*?)<\/script>/)[1];
class Element{constructor(id){this.id=id;this.value=id==='sample'?'0':'';this.checked=false;this.children=[];this.events={};this.textContent=''}append(e){this.children.push(e)}setAttribute(k,v){this[k]=v}replaceChildren(){this.children=[]}addEventListener(k,v){this.events[k]=v}}
const elements=new Map(),get=id=>{if(!elements.has(id))elements.set(id,new Element(id));return elements.get(id)};
get('data').textContent=payload;
const document={getElementById:get,createElement:()=>new Element(''),createElementNS:()=>new Element('')};
vm.runInNewContext(script,{document,Math,Number,JSON,String});
for(const [name,c] of Object.entries(JSON.parse(payload))){
    get('family').value=name;get('family').events.change();
    assert.strictEqual(Number(get('sample').max),c.samples.length-1);
    get('sample').value=get('sample').max;get('sample').events.input();
    assert(get('parameter').textContent.includes(c.samples.at(-1).parameter));
    assert.strictEqual(get('plot').children.filter(e=>e.fill==='#173348').length,c.samples.at(-1).roots.length);
    get('normalize').checked=true;get('normalize').events.change();
    assert(get('plot').children.some(e=>e.textContent.includes('Shape coordinates')));
    assert(get('diagnosis').textContent===c.diagnosis);
    get('normalize').checked=false;
}
console.log('Three geometry cases, final samples, root counts and shape-coordinate controls pass; native layout not tested.');
