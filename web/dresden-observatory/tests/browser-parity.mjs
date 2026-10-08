/** Run the existing Python-fixture tests inside Chromium, plus the real scene.
 * Start vite.standalone.config.ts first. PLAYWRIGHT_MODULE and CHROMIUM_PATH
 * optionally select installed packages/binaries; no browser download occurs.
 */
import fs from 'node:fs';
import path from 'node:path';
import {createRequire} from 'node:module';
import {pathToFileURL} from 'node:url';
const require=createRequire(import.meta.url);
const playwright=process.env.PLAYWRIGHT_MODULE?require(process.env.PLAYWRIGHT_MODULE):require('playwright');
const origin=process.env.DRESDEN_TEST_ORIGIN??'http://127.0.0.1:4173';
const project=path.resolve(path.dirname(new URL(import.meta.url).pathname),'..');
let vite;
if(process.env.DRESDEN_START_VITE==='1'){
 const {createServer}=await import(pathToFileURL(path.join(project,'node_modules/vite/dist/node/index.js')));
 vite=await createServer({configFile:path.join(project,'vite.standalone.config.ts'),server:{host:'127.0.0.1',port:4173,strictPort:true},logLevel:'error'});
 await vite.listen();
}
const browser=await playwright.chromium.launch({headless:true,executablePath:process.env.CHROMIUM_PATH,
 args:['--no-sandbox','--disable-dev-shm-usage','--enable-unsafe-webgpu','--enable-unsafe-swiftshader',
       ...(process.env.DRESDEN_GPU_BACKEND==='webgl'?['--use-gl=angle','--use-angle=swiftshader-webgl']:
       ['--enable-features=Vulkan','--use-angle=vulkan','--use-vulkan=swiftshader','--use-webgpu-adapter=swiftshader','--disable-vulkan-surface'])]});
const page=await browser.newPage({viewport:{width:1440,height:1000}});
if(process.env.DRESDEN_GPU_BACKEND==='webgl')await page.addInitScript(()=>Object.defineProperty(Navigator.prototype,'gpu',{get:()=>undefined,configurable:true}));
const errors=[];page.on('pageerror',e=>errors.push(String(e)));const passes=[];
try{
 await page.goto(origin,{waitUntil:'networkidle'});
 for(const name of ['math-parity.mjs','deep-parity.mjs','polynomial-parity.mjs']){
  let source=fs.readFileSync(path.join(project,'tests',name),'utf8');
  source=source.replace("import assert from 'node:assert/strict';",`const stable=x=>JSON.stringify(x,(_,v)=>typeof v==='bigint'?v.toString()+'n':v&&typeof v==='object'&&!Array.isArray(v)?Object.fromEntries(Object.keys(v).sort().map(k=>[k,v[k]])):v);
const assert={ok(v,m){if(!v)throw Error(m??'assertion failed')},equal(a,b,m){if(a!==b)throw Error(m??String(a)+' != '+String(b))},deepEqual(a,b,m){if(stable(a)!==stable(b))throw Error(m??'deep comparison failed')},throws(f,pattern){let e;try{f()}catch(error){e=error}if(!e||pattern&&!pattern.test(String(e)))throw Error('expected matching error')}};`)
   .replace("import fs from 'node:fs';",'')
   .replace(/from '([^']+)'/g,(_,target)=>`from '${origin}/@fs/${path.resolve(project,'tests',target)}'`)
   .replace(/JSON.parse\(fs.readFileSync\(new URL\('([^']+)',import.meta.url\)\)\)/g,(_,target)=>`(await (await fetch('${origin}/@fs/${path.resolve(project,'tests',target)}')).json())`);
  const logs=await page.evaluate(async source=>{
   const logs=[];const original=console.log;console.log=(...args)=>logs.push(args.join(' '));
   try{await import('data:text/javascript;base64,'+btoa(unescape(encodeURIComponent(source))))}finally{console.log=original}
   return logs;
  },source);
  passes.push({test:name,logs});console.log(name,logs.join(' '));
 }
 await page.waitForFunction(()=>{const s=document.querySelector('.backend')?.textContent;return s==='WebGPU'||s==='WebGL 2'||s==='2D research views'}, {timeout:30000});
 const rendering=await page.evaluate(()=>({backend:document.querySelector('.backend')?.textContent,
  canvasCount:document.querySelectorAll('canvas').length,canvasSizes:[...document.querySelectorAll('canvas')].map(c=>[c.width,c.height]),
  mathKernelLocation:'CPU BigInt/rational TypeScript; Three.js GPU coordinates are presentation only'}));
 if(!['WebGPU','WebGL 2'].includes(rendering.backend)||!rendering.canvasCount)throw Error('GPU scene failed: '+JSON.stringify(rendering));
 const png=await page.screenshot();
 const {createHash}=await import('node:crypto');rendering.screenshot_sha256=createHash('sha256').update(png).digest('hex');
 if(errors.length)throw Error(errors.join('\n'));
 const result={schema:'pp-dresden-chromium-parity/1',browser:browser.version(),tests:passes,rendering,page_errors:errors,
  scope:'Existing independent Python fixtures run inside Chromium; real Three.js scene initialized on software adapter. No numerical GPU kernel exists in this implementation; no physical GPU performance claim.'};
 const out=process.env.DRESDEN_TEST_RECEIPT??path.resolve(project,'../../receipts/dresden/browser-parity.json');
 fs.writeFileSync(out,JSON.stringify(result,null,2)+'\n');console.log(JSON.stringify(rendering));
}finally{await browser.close();await vite?.close()}
