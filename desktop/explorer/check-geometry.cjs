const {chromium}=require('@playwright/test'),{spawn}=require('node:child_process'),assert=require('node:assert/strict'),fs=require('node:fs'),path=require('node:path'),os=require('node:os');
(async()=>{
 const server=spawn('python3',['-u',path.join(__dirname,'server.py'),'--no-browser','--state',fs.mkdtempSync(path.join(os.tmpdir(),'pp-geometric-'))],{stdio:['pipe','pipe','inherit']});
 const url=await new Promise(resolve=>server.stdout.on('data',d=>{try{resolve(JSON.parse(String(d).split('\n')[0]).url);}catch{}}));
 const browser=await chromium.launch({executablePath:process.env.PP_BROWSER,headless:true,args:['--no-sandbox','--use-gl=angle','--use-angle=swiftshader','--enable-unsafe-swiftshader']});const errors=[];let checks=0;
 try{
  const page=await browser.newPage({viewport:{width:1450,height:1000}});page.on('pageerror',e=>errors.push(e.message));await page.goto(url);await page.click('[data-route=portfolio]');await page.locator('#portfolio-geometry canvas').waitFor();checks++;
  await page.click('[data-geo-step="1"]');assert.ok((await page.locator('[data-geo-explanation]').textContent()).includes('Calculate your first portfolio'));checks++;await page.click('[data-geo-step="0"]');await page.selectOption('[data-geo-project]','4');assert.ok((await page.locator('[data-geo-details]').textContent()).includes('project_5'));checks++;
  await page.locator('.geometry-advanced summary').first().click();await page.selectOption('[data-geo-axis="0"]','2');assert.equal(await page.inputValue('[data-geo-axis="2"]'),'0');checks++;
  await page.click('[data-geo-motion]');assert.equal(await page.getAttribute('[data-geo-motion]','aria-pressed'),'true');await page.click('[data-geo-motion]');checks++;
  for(const input of await page.locator('[data-bound=max]').all()){await input.fill('0');await input.dispatchEvent('change');}
  await page.click('#portfolio-build');await page.waitForFunction(()=>document.querySelector('#portfolio-status').textContent.includes('Complete'));assert.ok((await page.locator('[data-geo-details]').textContent()).includes('Whole portfolio score: 0'));checks++;
  await page.click('[data-decision="0"]');await page.click('#portfolio-condition');await page.waitForFunction(()=>document.querySelector('[data-geo-branches]').textContent.includes('Exclude project_2'));assert.ok((await page.locator('[data-geo-branches]').textContent()).includes('1 completions'));checks++;
  await page.locator('.geometry-matrix summary').click();assert.equal(await page.locator('[data-geo-row]').count(),50);await page.click('[data-geo-row="15"]');assert.equal(await page.inputValue('[data-geo-project]'),'15');checks++;
  await page.screenshot({path:'/workspace/scratch/8be0bf0d7243/geometry-desktop.png',fullPage:false});await page.setViewportSize({width:390,height:844});assert.ok(await page.evaluate(()=>document.documentElement.scrollWidth<=innerWidth+1));checks++;
  await page.screenshot({path:'/workspace/scratch/8be0bf0d7243/geometry-phone.png',fullPage:false});await page.click('[data-route=commands]');await page.locator('#command-form').waitFor();assert.equal(await page.locator('#portfolio-geometry canvas').count(),0);checks++;
  assert.deepEqual(errors,[]);checks++;fs.writeFileSync(path.join(__dirname,'GEOMETRY_BROWSER_CHECKS.json'),JSON.stringify({checks,errors,engine:'real native planner',viewports:['1450x1000','390x844'],webgl:'Chromium software WebGL; no physical-device claim'},null,2));console.log(JSON.stringify({checks,errors}));
 }finally{await browser.close();server.stdin.end();}
})().catch(error=>{console.error(error);process.exit(1)});
