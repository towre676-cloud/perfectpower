const fs=require('fs');
const assert=require('assert/strict');
const {chromium}=require(process.env.CODEX_PRIMARY_RUNTIME_NODE_MODULES?process.env.CODEX_PRIMARY_RUNTIME_NODE_MODULES+'/playwright':'playwright');
const root=__dirname;
let checks=0;
const check=(a,b)=>{assert.deepEqual(a,b);checks++};
function reference(load,size,square){const ids=[];let id=0;const squares=new Set([1,4,9,16,25,36,49,64,81]);for(let motor=1;motor<13;motor++)for(let gears=1;gears<9;gears++)for(let arm=1;arm<4;arm++){if(Math.floor(motor*gears/arm)>=load&&motor+gears+arm<=size&&(!square||squares.has(motor*gears)))ids.push(id);id++}return ids}
(async()=>{
 const browser=await chromium.launch({headless:true,executablePath:process.env.BROWSER_EXECUTABLE_PATH||(fs.existsSync(root+'/../browser-runtime/chromium')?root+'/../browser-runtime/chromium':undefined),args:['--no-sandbox','--use-gl=angle','--use-angle=swiftshader','--enable-unsafe-swiftshader','--no-zygote'],env:{...process.env,LD_LIBRARY_PATH:process.env.BROWSER_LIBRARY_PATH||root+'/../browser-runtime',FONTCONFIG_PATH:'/etc/fonts'}});
 const page=await browser.newPage({viewport:{width:1440,height:1000}}),errors=[],external=[];
 page.on('pageerror',e=>errors.push(e.message));page.on('request',r=>{if(/^https?:/.test(r.url()))external.push(r.url())});
 await page.goto('file://'+root+'/PerfectPower-Room-of-Possibilities.html');
 await page.waitForFunction(()=>window.__atlasState?.ready);await page.waitForTimeout(800);
 check(await page.locator('#count').textContent(),'13');
 await page.screenshot({path:root+'/desktop.png'});await page.check('#motion');
 for(const load of [1,6,12,48])for(const size of [3,8,10,15])for(const square of [false,true]){
   await page.evaluate(({load,size,square})=>{document.getElementById('load').value=load;document.getElementById('size').value=size;document.getElementById('square').checked=square;document.getElementById('load').dispatchEvent(new Event('input'))},{load,size,square});
   const q=await page.evaluate(()=>window.__atlasState.query());check(q.ids,reference(load,size,square));check(Number(await page.locator('#count').textContent()),q.ids.length);
 }
 await page.evaluate(()=>{document.getElementById('load').value=12;document.getElementById('size').value=10;document.getElementById('square').checked=false;document.getElementById('load').dispatchEvent(new Event('input'))});
 await page.uncheck('#motion');await page.click('#search');await page.waitForFunction(()=>window.__atlasState.query().selected>=0);check(await page.locator('#selected-title').textContent(),'Design 040');await page.check('#motion');
 await page.click('#best');const best=await page.evaluate(()=>{let q=window.__atlasState.query(),d=window.__atlasState.models;return {cost:d[q.selected].cost,min:Math.min(...q.ids.map(i=>d[i].cost))}});check(best.cost,best.min);
 await page.fill('#rank','13');await page.click('#jump');check((await page.evaluate(()=>window.__atlasState.query())).selected,147);
 await page.click('#another');check((await page.evaluate(()=>window.__atlasState.query())).selected,39);
 const download=page.waitForEvent('download');await page.click('#export');const dl=await download,collection=JSON.parse(fs.readFileSync(await dl.path()));check(collection.count,13);check(collection.designs.length,13);
 await page.click('#close-selection');await page.click('#tour-toggle');await page.click('#map');await page.waitForTimeout(2600);check((await page.evaluate(()=>window.__atlasState.query())).layout,true);check(await page.evaluate(()=>Math.abs(window.__atlasState.positions()[0][0]-(58-5.5*1.65))<.1),true);await page.screenshot({path:root+'/map.png'});

 for(const preset of ['compact','heavy','square','empty']){
  await page.click('[data-preset='+preset+']');const q=await page.evaluate(()=>window.__atlasState.query());
  check(q.ids,reference(q.conditions.load,q.conditions.size,q.conditions.square));
  check(Number(await page.locator('#flow-lift').textContent()),reference(q.conditions.load,24,false).length);
  check(Number(await page.locator('#flow-size').textContent()),reference(q.conditions.load,q.conditions.size,false).length);
  check(Number(await page.locator('#flow-square').textContent()),q.ids.length);
 }
 const emptyDownload=page.waitForEvent('download');await page.click('#export');const ed=await emptyDownload;check(JSON.parse(fs.readFileSync(await ed.path())).count,0);
 await page.click('[data-preset=heavy]');
 for(const objective of ['cost','lift','size']){
  await page.selectOption('#objective',objective);await page.click('#best');const d=await page.evaluate(()=>{const q=window.__atlasState.query();return {selected:window.__atlasState.models[q.selected],all:q.ids.map(i=>window.__atlasState.models[i])}});
  const score=x=>objective==='lift'?-Math.floor(x.drive/x.a):objective==='size'?x.size:x.cost;check(score(d.selected),Math.min(...d.all.map(score)));
 }
 await page.check('#hide-rejected');check((await page.evaluate(()=>window.__atlasState.query())).hiddenRejected,true);await page.uncheck('#hide-rejected');
 await page.click('#presentation');check((await page.evaluate(()=>window.__atlasState.query())).presentation,true);check(await page.locator('.sidebar').isVisible(),false);await page.waitForTimeout(2200);await page.screenshot({path:root+'/presentation.png'});await page.keyboard.press('Escape');check((await page.evaluate(()=>window.__atlasState.query())).presentation,false);
 await page.click('#close-selection');await page.click('[data-preset=square]');await page.click('#map-tab');await page.waitForTimeout(2600);await page.screenshot({path:root+'/map.png'});

 // Capture snapshots, then independently partition the entire stable domain.
 await page.locator('#comparison-panel summary').click();await page.uncheck('#square');await page.click('#capture-A');await page.check('#square');await page.click('#capture-B');
 const partition=(a,b)=>{const A=new Set(reference(a.load,a.size,a.square)),B=new Set(reference(b.load,b.size,b.square)),p={both:[],onlyA:[],onlyB:[],neither:[]};for(let id=0;id<288;id++)p[A.has(id)?B.has(id)?'both':'onlyA':B.has(id)?'onlyB':'neither'].push(id);return p};
 let ss=await page.evaluate(()=>window.__atlasState.scenarios());check(ss.partition,partition(ss.slots.A.rules,ss.slots.B.rules));check(ss.partition.both,[81]);check(ss.partition.onlyA.length,12);check(ss.active,true);
 await page.click('[data-preset=heavy]');check((await page.evaluate(()=>window.__atlasState.scenarios())).partition,ss.partition);
 await page.click('#capture-B');ss=await page.evaluate(()=>window.__atlasState.scenarios());check(ss.partition,partition(ss.slots.A.rules,ss.slots.B.rules));check(ss.partition.onlyB.length>0,true);
 await page.click('#restore-A');check((await page.evaluate(()=>window.__atlasState.query())).conditions,ss.slots.A.rules);check((await page.evaluate(()=>window.__atlasState.scenarios())).slots.B,ss.slots.B);
 await page.check('#hide-rejected');await page.click('#restore-B');check((await page.evaluate(()=>window.__atlasState.query())).conditions,ss.slots.B.rules);await page.uncheck('#hide-rejected');
 const compDownload=page.waitForEvent('download');await page.click('#compare-export');const cd=await compDownload;const cp=JSON.parse(fs.readFileSync(await cd.path()));check(cp.design_ids,ss.partition);check(Object.values(cp.counts).reduce((a,b)=>a+b,0),288);
 await page.waitForTimeout(4300);await page.screenshot({path:root+'/comparison.png'});
 for(const width of [1440,1100,700,390]){await page.setViewportSize({width,height:1000});check(await page.evaluate(()=>document.documentElement.scrollWidth<=innerWidth),true);check(await page.evaluate(()=>{const a=document.getElementById('compare-key').getBoundingClientRect(),b=document.getElementById('map-key').getBoundingClientRect();return a.bottom<=b.top}),true)}await page.screenshot({path:root+'/mobile-comparison.png',fullPage:true});await page.setViewportSize({width:1440,height:1000});

 await page.click('#best');await page.check('#hide-rejected');await page.locator('#scene-panel summary').click();await page.fill('#scene-name','Heavy atlas');await page.click('#save-scene');const saved=await page.evaluate(()=>window.__atlasState.scenarios().saved[0]);check(saved.rules,ss.slots.B.rules);check(saved.layout,true);
 await page.click('[data-preset=empty]');await page.click('#capture-A');await page.click('#capture-B');ss=await page.evaluate(()=>window.__atlasState.scenarios());check(ss.partition,{both:[],onlyA:[],onlyB:[],neither:Array.from({length:288},(_,i)=>i)});
 await page.locator('.scene-open').filter({hasText:'Heavy atlas'}).click();check((await page.evaluate(()=>window.__atlasState.query())).conditions,saved.rules);check((await page.evaluate(()=>window.__atlasState.scenarios())).active,false);check((await page.evaluate(()=>window.__atlasState.query())).selected,saved.selected);check((await page.evaluate(()=>window.__atlasState.query())).hiddenRejected,saved.hiddenRejected);check(await page.locator('#objective').inputValue(),saved.objective);
 await page.click('#family-tab');await page.waitForTimeout(1500);check((await page.evaluate(()=>window.__atlasState.family)).x,'-18');check((await page.evaluate(()=>window.__atlasState.family)).y,'6');await page.screenshot({path:root+'/family.png'});
 const samples=await page.evaluate(()=>window.__atlasState.source.rank_examples.map(r=>({expected:r.values,actual:window.__atlasState.familySelect(r.rank)})));
 for(const r of samples){check(r.actual.x,r.expected.x);check(r.actual.y,r.expected.y)}
 for(const bound of ['0','1','8','1000000000000000000000000000000000000000000000000000000000000']){
   await page.fill('#bound',bound);await page.click('#apply-bound');const n=BigInt(bound);
   check((await page.evaluate(()=>window.__atlasState.family)).count,(2n*n+1n).toString());
   const ranks=[0n,n,2n*n];for(const r of ranks){await page.fill('#family-rank',r.toString());await page.click('#family-jump');const p=await page.evaluate(()=>window.__atlasState.family);check(p.rank,r.toString());check((2n*BigInt(p.x)**2n).toString(),(3n*BigInt(p.y)**3n).toString())}
 }
 await page.fill('#bound','8');await page.click('#apply-bound');await page.fill('#family-rank','9');await page.click('#family-jump');check((await page.evaluate(()=>window.__atlasState.family)).x,'-18');
 await page.click('#family-next');check((await page.evaluate(()=>window.__atlasState.family)).x,'-144');await page.click('#family-prev');check((await page.evaluate(()=>window.__atlasState.family)).x,'-18');
 const old=await page.evaluate(()=>window.__atlasState.family.rank);await page.fill('#family-rank','17');await page.click('#family-jump');check((await page.evaluate(()=>window.__atlasState.family)).rank,old);

 await page.fill('#bound','10000000000000000000000000000000000000000');await page.click('#apply-bound');await page.locator('.inverse summary').click();
 for(const row of await page.evaluate(()=>window.__atlasState.source.rank_examples)){
  await page.fill('#inverse-x',row.values.x);await page.fill('#inverse-y',row.values.y);await page.click('#inverse-find');check((await page.evaluate(()=>window.__atlasState.family)).rank,row.rank);
 }
 let before=await page.evaluate(()=>window.__atlasState.family.rank);await page.fill('#inverse-x','1');await page.fill('#inverse-y','1');await page.click('#inverse-find');check((await page.evaluate(()=>window.__atlasState.family)).rank,before);
 for(let i=0;i<8;i++){await page.click('#random-point');const p=await page.evaluate(()=>window.__atlasState.family);check(BigInt(p.rank)>=0n&&BigInt(p.rank)<BigInt(p.count),true);check((2n*BigInt(p.x)**2n).toString(),(3n*BigInt(p.y)**3n).toString())}
 await page.fill('#bound','0');await page.click('#apply-bound');await page.click('#random-point');check((await page.evaluate(()=>window.__atlasState.family)).rank,'0');
 await page.click('#workshop-tab');await page.check('#motion');await page.locator('#steps button').nth(0).click();for(let i=1;i<8;i++){await page.click('#next');check(await page.locator('#tour-kicker').textContent(),`The guided walkthrough / ${i+1} of 8`);if(i===5){check((await page.evaluate(()=>window.__atlasState.scenarios())).partition.both,[81])}if(i===6){check((await page.evaluate(()=>window.__atlasState.query())).current,'family');check((await page.evaluate(()=>window.__atlasState.family)).rank,'0')}}check((await page.evaluate(()=>window.__atlasState.family)).x,'-18');check((await page.evaluate(()=>window.__atlasState.family)).rank,(10n**40n+1n).toString());await page.click('#next');check(await page.locator('#tour').isVisible(),false);
 await page.fill('#scene-name','Exact return');await page.click('#save-scene');const savedFamily=await page.evaluate(()=>window.__atlasState.scenarios().saved[0]);check(savedFamily.kind,'family');check(savedFamily.rank,(10n**40n+1n).toString());
 await page.reload();await page.waitForFunction(()=>window.__atlasState?.ready);await page.check('#motion');await page.locator('#scene-panel summary').click();check(await page.locator('.scene-open').count(),2);await page.locator('.scene-open').filter({hasText:'Exact return'}).click();check(await page.evaluate(()=>window.__atlasState.family),{bound:savedFamily.bound,count:(2n*10n**40n+1n).toString(),rank:savedFamily.rank,x:'-18',y:'6'});
 await page.locator('.scene-open').filter({hasText:'Heavy atlas'}).click();check((await page.evaluate(()=>window.__atlasState.query())).conditions,saved.rules);check((await page.evaluate(()=>window.__atlasState.query())).layout,true);await page.locator('[aria-label="Delete saved scene Heavy atlas"]').click();check(await page.locator('.scene-open').count(),1);
 await page.click('#family-tab');

 for(const width of [1000,1100,700]){await page.setViewportSize({width,height:900});check(await page.evaluate(()=>document.documentElement.scrollWidth<=innerWidth),true)}
 await page.setViewportSize({width:390,height:844});await page.waitForTimeout(800);check(await page.evaluate(()=>document.documentElement.scrollWidth<=innerWidth),true);await page.screenshot({path:root+'/mobile-family.png',fullPage:true});
 await page.click('#workshop-tab');await page.locator('#steps button').nth(0).click();await page.waitForTimeout(700);check(await page.evaluate(()=>document.documentElement.scrollWidth<=innerWidth),true);await page.screenshot({path:root+'/mobile.png',fullPage:true});
 check(errors,[]);check(external,[]);
 await browser.close();fs.writeFileSync(root+'/browser-checks.json',JSON.stringify({checks,bundle_sha256:require('crypto').createHash('sha256').update(fs.readFileSync(root+'/PerfectPower-Room-of-Possibilities.html')).digest('hex'),page_errors:errors,external_requests:external,desktop:[1440,1000],mobile:[390,844],renderer:'WebGL2 / ANGLE SwiftShader',result:'passed'},null,2));console.log(JSON.stringify({checks,result:'passed'}));
})().catch(e=>{console.error(e);process.exit(1)});
