const {chromium}=require('playwright');
const {spawn}=require('node:child_process');const fs=require('node:fs'),path=require('node:path');
const root=path.resolve('../..','mobile-preview-root');
const engine=spawn('python',[path.join(root,'desktop/explorer/server.py'),'--no-browser','--state',path.resolve('../../mobile-preview-state')],{stdio:['pipe','pipe','pipe']});
let errors=[],checks=[];
const test=(name,pass)=>{if(!pass)throw Error(name);checks.push(name);};
(async()=>{
 const connection=await new Promise((resolve,reject)=>{let text='';engine.stdout.on('data',b=>{text+=b;if(text.includes('\n'))resolve(JSON.parse(text.split('\n')[0]));});engine.on('exit',()=>reject(Error('Engine closed before startup')));});
 const browser=await chromium.launchPersistentContext(fs.mkdtempSync(path.resolve("../../toolchain/browser-tmp/profile-")),{viewport:{width:390,height:844},deviceScaleFactor:1,isMobile:true,hasTouch:true,executablePath:process.env.CHROME_EXECUTABLE,headless:true,args:['--no-sandbox','--no-zygote','--single-process','--disable-dev-shm-usage','--use-gl=angle','--use-angle=swiftshader','--enable-unsafe-swiftshader']});
 try{
  const page=await browser.newPage();
  page.on('pageerror',e=>errors.push(e.message));
  page.on('console',message=>{if(message.type()==='error')errors.push(message.text());});
  await page.addInitScript(()=>{localStorage.ppReduce='yes';});
  await page.goto(connection.url);await page.locator('#nav button').last().waitFor();await page.waitForTimeout(1300);
  test('Seven workspace entries',await page.locator('#nav button').count()===7);
  test('Phone layout has no horizontal document overflow',await page.evaluate(()=>document.documentElement.scrollWidth<=innerWidth+1));
  test('Local 3D canvas renders',await page.locator('#hero-scene canvas').count()===1);
  await page.screenshot({path:path.resolve('../../final-delivery/PerfectPower-Explorer-Mobile-Preview.png'),fullPage:false});
  await page.locator('#mobile-menu').click();await page.locator('#mobile-navigation[open]').waitFor();
  test('All workspaces and settings in full menu',await page.locator('#mobile-navigation .mobile-links button').count()===8);
  await page.locator('#mobile-navigation .mobile-links button').filter({hasText:'Workbenches'}).click();await page.locator('#command-form').waitFor();
  test('Command forms remain available',await page.locator('.command-list button').count()===145);
  test('Phone command view has no horizontal document overflow',await page.evaluate(()=>document.documentElement.scrollWidth<=innerWidth+1));
  const result=await page.evaluate(async()=>{const response=await fetch('/api/run',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({kind:'scan',spec:{coeff:['-2','0','0','1'],d:2,lo:-20,hi:20}})});const {id}=await response.json();for(let i=0;i<100;i++){const job=await(await fetch('/api/job?id='+id)).json();if(job.status!=='running')return job;await new Promise(r=>setTimeout(r,50));}throw Error('No result');});
  test('Real exact point engine returns signed Mordell points',result.status==='complete'&&result.result.count===2);
  const exportCheck=await page.evaluate(async id=>{const data=await(await fetch('/run/'+id+'/result.json')).json();return data.result.points.length===2&&data.request.spec.coeff.length===4;},result.id);
  test('Export retains complete run and inputs',exportCheck);
  await page.evaluate(()=>location.hash='settings');await page.locator('#toggle-theme').waitFor();await page.locator('#toggle-theme').click();
  test('Dark theme changes and persists',await page.evaluate(()=>document.body.classList.contains('dark')&&localStorage.ppTheme==='dark'));
  await page.locator('#toggle-theme').click();await page.evaluate(()=>location.hash='home');await page.locator('#hero-scene canvas').waitFor();
  test('No uncaught JavaScript or browser console errors',errors.length===0);
  fs.writeFileSync(path.resolve('../MOBILE_UI_CHECKS.json'),JSON.stringify({checks:checks.length,passed:checks,errors,environment:'Standalone APK interface in Chromium at 390×844 with software WebGL; this is not an Android WebView or device test.'},null,2));
  console.log(JSON.stringify({checks:checks.length,errors}));
 }finally{await browser.close();engine.stdin.end();}
})().catch(error=>{console.error(error);engine.stdin.end();process.exitCode=1;});
