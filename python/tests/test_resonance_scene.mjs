/* Headless checks of the shipped Three.js scene's real geometry.
 * These exercise Three.BufferGeometry and curve construction; they are not
 * WebGL rendering, layout, interaction, or browser visual QA.
 */
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import {createRequire} from 'node:module';
import {fileURLToPath,pathToFileURL} from 'node:url';

const root=path.resolve(path.dirname(fileURLToPath(import.meta.url)),'../..');
const runtimeRequire=createRequire(import.meta.url);
const web=path.join(root,'web/integral-families');
const dependencyPaths=[web,path.join(root,'desktop/explorer'),...(process.env.RESONANCE_DEPENDENCY_PATHS||'').split(path.delimiter).filter(Boolean)];
const resolve=id=>runtimeRequire.resolve(id,{paths:dependencyPaths});
const {build}=runtimeRequire(resolve('esbuild'));
const threeModule=path.join(path.dirname(resolve('three')),'three.module.js');
const THREE=await import(pathToFileURL(threeModule).href);
const plugins=[{name:'test-runtime-dependencies',setup(b){
  b.onResolve({filter:/^(react(?:-dom)?)(\/.*)?$/},args=>({path:resolve(args.path)}));
  b.onResolve({filter:/^three(?:\/.*)?$/},args=>({path:args.path==='three'?threeModule:resolve(args.path)}));
}}];
const source=path.join(root,'web/integral-families/resonance-scene.js');
const result=await build({entryPoints:[source],bundle:true,write:false,
  format:'cjs',platform:'node',target:'node22',logLevel:'silent',
  plugins});
const compiled={exports:{}};
new Function('module','exports','require',result.outputFiles[0].text)(compiled,compiled.exports,runtimeRequire);
const {SCENE_MODES,NODE_ANCHORS,createRootGeometry,createFlowCurve,createResonanceScene}=compiled.exports;
assert.deepEqual(SCENE_MODES,['colimit','resonance','tower','nerve']);
assert.equal(typeof createResonanceScene,'function');
assert.equal(NODE_ANCHORS.length,5);
for(const anchor of NODE_ANCHORS){assert.equal(anchor.length,3);assert(anchor.every(Number.isFinite));}
assert.equal(new Set(NODE_ANCHORS.map(p=>p.join(','))).size,5);

const envelope=JSON.parse(fs.readFileSync(path.join(root,'web/integral-families/atlas-data.json'),'utf8'));
assert.equal(crypto.createHash('sha256').update(envelope.payload_json).digest('hex'),envelope.payload_sha256);
const data=JSON.parse(envelope.payload_json);
assert.equal(data.roots.length,240);
assert.deepEqual(Array.from({length:8},(_,i)=>data.roots.filter(r=>r.orbit===i).length),Array(8).fill(30));
assert.equal(data.branches.length,264);
assert.equal(data.branches.filter(b=>b.primitive).length,240);
let edges=0;
for(const r of data.roots){
  assert.equal(r.doubled_root.reduce((s,x)=>s+x*x,0),8);
  assert.equal(r.neighbors.length,56);
  for(const j of r.neighbors){assert.equal(r.doubled_root.reduce((s,x,k)=>s+x*data.roots[j].doubled_root[k],0),4);if(r.id<j)edges++;}
}
assert.equal(edges,6720);

const geometries=[createRootGeometry(data),createRootGeometry(data),createRootGeometry(envelope)];
for(const geometry of geometries){
  assert.equal(geometry.isBufferGeometry,true);
  for(const name of ['position','color','aSize']){
    const attr=geometry.getAttribute(name);
    assert(attr,`Missing ${name} geometry attribute`);
    assert.equal(attr.count,240);
    assert(Array.from(attr.array).every(Number.isFinite),`${name} contains nonfinite values`);
  }
}
const geometry=geometries[0],position=geometry.getAttribute('position'),colors=geometry.getAttribute('color'),sizes=geometry.getAttribute('aSize');
assert.equal(position.itemSize,3);
assert.equal(colors.itemSize,3);
assert.equal(sizes.itemSize,1);
assert(Array.from(sizes.array).every(x=>x>0));
assert(Array.from(colors.array).every(x=>x>=0&&x<=1));
assert.equal(new Set(Array.from({length:240},(_,i)=>[position.getX(i),position.getY(i),position.getZ(i)].join(','))).size,240);
const projected=data.roots.map(r=>[r.x,r.y,r.z]);
const scale=projected.reduce((sum,p,i)=>sum+p[0]*position.getX(i)+p[1]*position.getY(i),0)/projected.reduce((sum,p)=>sum+p[0]*p[0]+p[1]*p[1],0);
const depthScale=projected.reduce((sum,p,i)=>sum+p[2]*position.getZ(i),0)/projected.reduce((sum,p)=>sum+p[2]*p[2],0);
assert(scale>0&&depthScale>0,'Root projection must preserve orientation');
let maxRadius=0;
const center=[0,0,0];
for(let i=0;i<240;i++){
  const point=[position.getX(i),position.getY(i),position.getZ(i)];
  for(let k=0;k<3;k++){
    assert(Math.abs(point[k]-(k===2?depthScale:scale)*projected[i][k])<2e-6,'Root projection must retain the Coxeter plane and a uniform optional depth scale');
    center[k]+=point[k]/240;
  }
  maxRadius=Math.max(maxRadius,Math.hypot(...point));
}
assert(center.every(x=>Math.abs(x)<2e-6),'Root cloud must remain centered');
assert(maxRadius>.5&&maxRadius<1.5,'Root cloud must fit inside its displayed node');
for(const other of geometries.slice(1))for(const name of ['position','color','aSize'])assert.deepEqual(other.getAttribute(name).array,geometry.getAttribute(name).array);
assert.throws(()=>createRootGeometry({roots:data.roots.slice(1)}),/240-root/);
assert.throws(()=>createRootGeometry({...data,roots:data.roots.map((r,i)=>i? r:{...r,x:NaN})}),/projection/);

const a=new THREE.Vector3(-4.8,0,0),b=new THREE.Vector3(4.8,0,0);
let curveSamples=0;
for(const bend of [-1,0,1]){
  const curve=createFlowCurve(a,b,bend);
  assert.equal(curve.isCubicBezierCurve3,true);
  assert(curve.getPoint(0).distanceTo(a)<1e-12);
  assert(curve.getPoint(1).distanceTo(b)<1e-12);
  const repeated=createFlowCurve(a,b,bend);
  for(let i=0;i<=100;i++){
    const p=curve.getPoint(i/100);
    assert([p.x,p.y,p.z].every(Number.isFinite));
    assert(p.distanceTo(repeated.getPoint(i/100))<1e-12);
    curveSamples++;
  }
}
assert(createFlowCurve(a,b,1).getPoint(.5).distanceTo(createFlowCurve(a,b,-1).getPoint(.5))>.1,'Curvature should affect the displayed flow');
assert(a.equals(new THREE.Vector3(-4.8,0,0))&&b.equals(new THREE.Vector3(4.8,0,0)),'Flow creation must not mutate its anchors');
for(const geometry of geometries)geometry.dispose();

// Render the actual React component with ReactDOMServer. No DOM or WebGL is
// supplied: this checks useful initial markup and autonomous defaults only.
const ssr=await build({stdin:{contents:"import React from 'react'; import {renderToStaticMarkup} from 'react-dom/server'; import {ResonanceExperience} from './resonance.jsx'; export const html=renderToStaticMarkup(React.createElement(ResonanceExperience));",resolveDir:web,sourcefile:'resonance-test-entry.mjs'},bundle:true,write:false,
  format:'cjs',platform:'node',target:'node22',logLevel:'silent',plugins,
  define:{'process.env.NODE_ENV':'"production"'}});
const rendered={exports:{}};
new Function('module','exports','require',ssr.outputFiles[0].text)(rendered,rendered.exports,runtimeRequire);
const html=rendered.exports.html;
assert.equal(typeof html,'string');
assert(html.includes('AUTONOMOUS SEQUENCE'));
assert(html.includes('aria-label="Pause animation"'));
assert(html.includes('aria-label="Visualization scenes"'));
const navigation=html.match(/<nav\b[^>]*aria-label="Visualization scenes"[^>]*>([\s\S]*?)<\/nav>/)?.[1];
assert(navigation,'Scene navigation must be accessible');
assert.equal((navigation.match(/<button\b/g)||[]).length,4);
assert.equal((html.match(/class="node-label /g)||[]).length,5);
assert(html.includes('class="resonance-canvas" role="img" aria-label='));
assert(html.includes('Opening the resonance field'));
assert(!html.includes('The 3D scene could not start'));
console.log(JSON.stringify({schema:'pp-resonance-scene-checks/1',scene_modes:SCENE_MODES.length,root_points:240,coxeter_orbits:8,exact_adjacency_pairs:edges,phase_branches:264,primitive_phase_branches:240,deterministic_geometries:geometries.length,curve_samples:curveSamples,payload_sha256:envelope.payload_sha256,esbuild_scene_bundle:true,react_server_markup:true,autonomous_default:true,browser_qa:false,passed:true}));
