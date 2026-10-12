const {chromium}=require('@playwright/test'),{spawn}=require('node:child_process'),assert=require('node:assert/strict'),fs=require('node:fs'),os=require('node:os'),path=require('node:path');
(async()=>{
 const state=fs.mkdtempSync(path.join(os.tmpdir(),'pp-portfolio-ui-'));
 const engine=spawn('python3',['-u',path.join(__dirname,'server.py'),'--no-browser','--state',state],{stdio:['pipe','pipe','inherit']});
 const url=await new Promise(resolve=>{engine.stdout.on('data',x=>{try{resolve(JSON.parse(String(x).split('\n')[0]).url);}catch{}});});
 const browser=await chromium.launch({executablePath:process.env.PP_BROWSER,headless:true,args:['--no-sandbox']});let checks=0;const errors=[];
 try{
  const page=await browser.newPage();page.on('pageerror',e=>errors.push(e.message));await page.goto(url);await page.click('[data-route=portfolio]');await page.locator('#project-grid').waitFor();assert.equal(await page.locator('.project-card').count(),50);checks++;
  for(const input of await page.locator('[data-bound=max]').all()){await input.fill('0');await input.dispatchEvent('change');}
  await page.click('#portfolio-build');await page.waitForFunction(()=>document.querySelector('#portfolio-status').textContent.includes('Complete'),null,{timeout:20000});assert.ok((await page.locator('#portfolio-answer').textContent()).includes('1'));assert.equal(await page.locator('.project-card.chosen').count(),0);checks++;
  await page.click('[data-decision="1"]');await page.click('#portfolio-condition');await page.waitForFunction(()=>document.querySelector('#portfolio-answer').textContent.includes('No feasible selection'));checks++;
  await page.click('#prefix-clear');await page.click('#portfolio-select');await page.waitForFunction(()=>document.querySelector('#portfolio-answer').textContent.includes('Portfolio at rank 0'));checks++;
  await page.click('#portfolio-sample');await page.waitForFunction(()=>document.querySelector('#portfolio-answer').textContent.includes('Seeded feasible sample'));checks++;
  const ev=await page.locator('#portfolio-answer a').first().getAttribute('href');assert.equal((await (await page.request.get(new URL(ev,url).href)).json()).summary.count,'1');checks++;
  await page.setViewportSize({width:390,height:844});assert.ok(await page.evaluate(()=>document.documentElement.scrollWidth<=innerWidth+1));checks++;
  await page.screenshot({path:'/workspace/scratch/8be0bf0d7243/portfolio-phone.png',fullPage:true});
  await page.setViewportSize({width:1440,height:1000});await page.screenshot({path:'/workspace/scratch/8be0bf0d7243/portfolio-desktop.png',fullPage:true});
  await page.fill('#portfolio-rank','9007199254740993');await page.click('#portfolio-select');await page.waitForFunction(()=>document.querySelector('#portfolio-status').textContent.includes('failed'));checks++;
  await page.fill('#portfolio-rank','0');await page.click('#portfolio-select');await page.waitForFunction(()=>document.querySelector('#portfolio-status').textContent.includes('Complete'));checks++;
  assert.deepEqual(errors,[]);checks++;fs.writeFileSync(path.join(__dirname,'PORTFOLIO_BROWSER_CHECKS.json'),JSON.stringify({checks,errors,engine:'real native residual population planner',viewports:['1440x1000','390x844'],native_device_test:false},null,2));console.log(JSON.stringify({checks,errors}));
 }finally{await browser.close();engine.stdin.end();}
})().catch(e=>{console.error(e);process.exit(1)});
