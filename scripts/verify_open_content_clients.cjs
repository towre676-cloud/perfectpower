/* Execute both shipped clients against DOM/canvas mocks.
   This checks script behavior and exact result transport, not native layout. */
const fs=require('node:fs'),vm=require('node:vm'),assert=require('node:assert/strict'),path=require('node:path');
function document(){
  const elements={};
  function get(id){return elements[id]??=( {value:id==='example'?'register':'',textContent:'',width:440,height:440,events:{},append(o){if(!this.value)this.value=o.value;},addEventListener(k,f){this.events[k]=f},click(){return this.onclick()},getContext(){return {fillRect(){},strokeRect(){}}}} )}
  return {getElementById:get,createElement(){return {value:'',textContent:''}}};
}
(async()=>{
  const geometry=fs.readFileSync(process.argv[2]??path.join(__dirname,'../receipts/open_content/geometry_workbench.html'),'utf8');
  const dom=document();dom.getElementById('data').textContent=geometry.match(/<script id="data" type="application\/json">([\s\S]*?)<\/script>/)[1];
  vm.runInNewContext(geometry.match(/<\/script><script>([\s\S]*?)<\/script>/)[1],{document:dom});
  dom.getElementById('panel').value='branch';dom.getElementById('panel').events.input();
  const detail=JSON.parse(dom.getElementById('detail').textContent);
  assert.equal(detail.chart,'branch');assert.equal(detail.certified_transports.finite.compatible,true);
  dom.getElementById('panel').value='infinity';dom.getElementById('panel').events.input();
  assert.equal(JSON.parse(dom.getElementById('detail').textContent).certified_transports.finite.compatible,true);
  const client=fs.readFileSync(path.join(__dirname,'../python/perfectpower/http_service.py'),'utf8').match(/CLIENT='''([\s\S]*?)'''/)[1];
  const consoleDOM=document();let sent;
  const huge='{"rank":1000000000000000000000000000000000000000000000000000000000001}';
  vm.runInNewContext(client.match(/<script>([\s\S]*?)<\/script>/)[1],{document:consoleDOM,fetch:async(url,request)=>{sent=request.body;return {ok:true,text:async()=>huge}}});
  consoleDOM.getElementById('request').value=huge;
  await consoleDOM.getElementById('run').onclick();
  assert.equal(sent,huge);assert.equal(consoleDOM.getElementById('result').textContent,huge);
  assert.equal(consoleDOM.getElementById('status').textContent,'Complete');
  consoleDOM.getElementById('request').value='invalid';await consoleDOM.getElementById('run').onclick();
  assert.equal(consoleDOM.getElementById('status').textContent,'Request failed');
  process.stdout.write('Both clients passed executable DOM/canvas checks; native layout not tested.\n');
})().catch(error=>{console.error(error);process.exitCode=1});
