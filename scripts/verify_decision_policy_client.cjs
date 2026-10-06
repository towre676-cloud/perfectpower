const fs=require('node:fs'),vm=require('node:vm'),assert=require('node:assert/strict');
const html=fs.readFileSync(process.argv[2]??'receipts/decision_policies/policy_workbench.html','utf8');
const elements={};function get(id){return elements[id]??={value:['x','y'].includes(id)?'1/2':'',textContent:'',events:{},attrs:{},append(){},setAttribute(k,v){this.attrs[k]=v},addEventListener(k,v){this.events[k]=v}}}
const document={getElementById:get,createElementNS(){return {attrs:{},setAttribute(k,v){this.attrs[k]=v},textContent:''}}};
get('data').textContent=html.match(/<script id="data" type="application\/json">([\s\S]*?)<\/script>/)[1];
vm.runInNewContext(html.match(/<\/script><script>([\s\S]*?)<\/script>/)[1],{document});
assert.equal(JSON.parse(get('result').textContent).minimizers.length,2);
get('x').value=get('y').value='1/3';get('x').events.input();
assert.equal(JSON.parse(get('result').textContent).minimizers.length,3);
get('x').value='0.3333333333333333333333333333333333333333333333333';get('x').events.input();
assert.equal(JSON.parse(get('result').textContent).minimizers.length,1);
get('x').value='5';get('x').events.input();assert.match(get('result').textContent,/outside/);
console.log('Policy client: exact fraction, >53-bit decimal, ties and region bounds passed; native layout not tested.');
