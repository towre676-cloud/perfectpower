import {createRequire} from 'node:module';
import {fileURLToPath} from 'node:url';
import fs from 'node:fs';
import path from 'node:path';
import assert from 'node:assert/strict';
const root=path.dirname(fileURLToPath(import.meta.url));
const require=createRequire(import.meta.url),{build}=require('esbuild');
const output=path.join(root,'.ssr-check.cjs');
try{
 await build({entryPoints:[path.join(root,'StudioApp.jsx')],bundle:true,platform:'node',format:'cjs',packages:'external',outfile:output,logLevel:'silent',define:{'process.env.NODE_ENV':'"production"'}});
 const {IntegralStudio,Definitions}=require(output),React=require('react'),{renderToString}=require('react-dom/server');
 const html=renderToString(React.createElement(IntegralStudio));
 const proof=renderToString(React.createElement(Definitions,{onClose(){}}));
 assert.ok(!html.includes('katex-error')&&!proof.includes('katex-error'),'Every displayed identity must typeset without errors');
 for(const text of ['The integral','The spectrum','The frequencies','The energy','Save study','Restore saved','Move the boundary','TOTAL SQUARED INTEGRAL'])assert.ok(html.includes(text),text+' must be present');
 assert.equal((html.match(/type="range"/g)||[]).length,5,'Four coefficient controls and one independent integration boundary');
 assert.ok(proof.includes('101'),'The seventh-selector norm remains in the exact matrix');
 const offline=fs.readFileSync(path.resolve(root,'../../../output/PerfectPower_Integral_Studio.html'),'utf8');
 const markup=offline.slice(0,offline.indexOf('<script>'))+offline.slice(offline.lastIndexOf('</script>')+9);
 assert.ok(!/<script[^>]+src=/.test(markup),'Offline JavaScript is embedded');
 assert.ok(!/<link[^>]+rel="stylesheet"/.test(markup),'Offline styles and math fonts are embedded');
 assert.equal((offline.match(/id="integral-studio"/g)||[]).length,1,'One app mount');
 console.log('React server rendering, all displayed math, five controls and the self-contained offline build verified. Browser interaction QA is a separate check.');
}finally{fs.rmSync(output,{force:true});}
