const fs=require('fs'),assert=require('assert/strict'),crypto=require('crypto'),path=require('path'),{spawn}=require('child_process');
const {chromium}=require(process.env.CODEX_PRIMARY_RUNTIME_NODE_MODULES?process.env.CODEX_PRIMARY_RUNTIME_NODE_MODULES+'/playwright':'playwright');
let checks=0;const check=(a,b)=>{assert.deepEqual(a,b);checks++};
const root=__dirname;
(async()=>{
 const browser=await chromium.launch({headless:true,executablePath:process.env.BROWSER_EXECUTABLE_PATH,args:['--no-sandbox','--use-gl=angle','--use-angle=swiftshader','--enable-unsafe-swiftshader','--no-zygote'],env:{...process.env,LD_LIBRARY_PATH:process.env.BROWSER_LIBRARY_PATH,FONTCONFIG_PATH:'/etc/fonts'}});
 const page=await browser.newPage({viewport:{width:1440,height:1000}}),errors=[],external=[];
 page.on('pageerror',e=>errors.push(e.message));page.on('request',r=>{if(/^https?:/.test(r.url())&&!/^http:\/\/127\.0\.0\.1:\d+\//.test(r.url()))external.push(r.url())});
 let server;
 try{
  await page.goto('file://'+root+'/PerfectPower-Room-of-Possibilities.html');await page.waitForFunction(()=>window.__atlasState?.ready);await page.check('#motion');
  await page.click('#family-tab');await page.click('#open-exact-comparison');
  check(await page.locator('#exact-comparison').isVisible(),true);check(await page.locator('#comparison-replay').isDisabled(),true);
  for(const [index,T,M] of [['0',10n**40n,10n],['1',8n,3n]]){
   await page.selectOption('#comparison-dataset',index);
   const current=await page.evaluate(()=>window.__atlasState.exactComparison());
   const expected={universe:2n*T+1n,left:T+1n,right:2n*M+1n,both:M+1n,left_only:T-M,right_only:M,neither:T-M,union:T+M+1n,symmetric_difference:T};
   check(current.summary.counts,Object.fromEntries(Object.entries(expected).map(([k,v])=>[k,v.toString()])));
   const length=await page.locator('#comparison-samples option').count();check(length,8);
   for(let i=0;i<length;i++){
    await page.selectOption('#comparison-samples',String(i));const {record}=await page.evaluate(()=>window.__atlasState.exactComparison());
    const x=BigInt(record.record.values.x),y=BigInt(record.record.values.y),t=BigInt(record.record.parameter),category=x>=0n?(t<=M?'both':'left_only'):(t<=M?'right_only':'neither');
    check(2n*x*x,3n*y**3n);check(record.category,category);check(await page.locator('#comparison-addresses tr').count(),9);
    const U=t===0n?0n:x>0n?t:T+t,A=x<0n?null:t,B=t>M?null:(x<0n?M+t:t);
    check(record.addresses.universe,U.toString());check(record.addresses.left,A===null?null:A.toString());check(record.addresses.right,B===null?null:B.toString());
   }
  }
  await page.selectOption('#comparison-samples','4');const selected=await page.evaluate(()=>window.__atlasState.exactComparison());
  await page.click('#comparison-visit');check((await page.evaluate(()=>window.__atlasState.family)).rank,selected.record.addresses.universe);check((await page.evaluate(()=>window.__atlasState.family)).bound,'8');
  await page.click('#open-exact-comparison');const download=page.waitForEvent('download');await page.click('#comparison-download');const result=JSON.parse(fs.readFileSync(await(await download).path()));check(result.summary.counts.universe,'17');check(result.examples.length,8);
  await page.selectOption('#comparison-dataset','0');await page.evaluate(()=>document.getElementById('exact-comparison').scrollTop=0);await page.screenshot({path:root+'/exact-comparison.png'});
  await page.setViewportSize({width:390,height:844});check(await page.evaluate(()=>document.documentElement.scrollWidth<=innerWidth),true);check(await page.evaluate(()=>{const r=document.getElementById('exact-comparison').getBoundingClientRect();return r.left>=0&&r.right<=innerWidth}),true);await page.screenshot({path:root+'/mobile-exact-comparison.png',fullPage:true});
  await page.keyboard.press('Escape');check(await page.locator('#exact-comparison').isVisible(),false);
  const repo=path.resolve(root,'../..'),script="from perfectpower.http_service import QueryHTTPServer\ns=QueryHTTPServer(':memory:')\nprint(s.server_port,flush=True)\ns.serve_forever()";
  server=spawn(process.env.PYTHON_EXECUTABLE||'python',['-c',script],{cwd:repo,env:{...process.env,PYTHONPATH:path.join(repo,'python')},stdio:['ignore','pipe','pipe']});
  const port=await new Promise((resolve,reject)=>{let out='';server.stdout.on('data',chunk=>{out+=chunk;if(out.includes('\n'))resolve(Number(out.trim()))});server.once('error',reject);server.once('exit',code=>reject(Error('Local service exited '+code)))});
  await page.setViewportSize({width:1440,height:1000});await page.goto('http://127.0.0.1:'+port+'/atlas');await page.waitForFunction(()=>window.__atlasState?.ready);await page.check('#motion');await page.click('#family-tab');await page.click('#open-exact-comparison');check(await page.locator('#comparison-replay').isEnabled(),true);await page.click('#comparison-replay');
  await page.waitForFunction(()=>document.getElementById('comparison-replay-result').textContent.includes('pp-query-response/1'));
  const raw=await page.locator('#comparison-replay-result').textContent();check(raw.includes((2n*10n**40n+1n).toString()),true);check(raw.includes('"ok":true'),true);
  await page.selectOption('#comparison-dataset','1');await page.click('#comparison-replay');await page.waitForFunction(()=>document.getElementById('comparison-replay-result').textContent.includes('pp-query-response/1'));check(JSON.parse(await page.locator('#comparison-replay-result').textContent()).result.counts.universe,17);
  check(errors,[]);check(external,[]);
  fs.writeFileSync(root+'/comparison-checks.json',JSON.stringify({checks,result:'passed',bundle_sha256:crypto.createHash('sha256').update(fs.readFileSync(root+'/PerfectPower-Room-of-Possibilities.html')).digest('hex'),page_errors:errors,external_requests:external,coverage:'Exported counts, original coordinates, categories, addresses, download, mobile layout, offline behavior and live Python HTTP replay for both datasets.'},null,2));
  console.log(JSON.stringify({checks,result:'passed'}));
 }finally{if(server)server.kill();await browser.close()}
})().catch(e=>{console.error(e);process.exit(1)});
