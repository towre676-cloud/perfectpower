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
const {SCENE_MODES,NODE_ANCHORS,createRootGeometry,createRootNeighborGeometry,createFlowCurve,createResonanceScene,createTransitionController,cameraFrameDistance,boundedCameraPosition}=compiled.exports;
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

// Every displayed E8 neighbor edge must connect the selected exact root to
// precisely one of its 56 verified neighbors, with the same projection.
let neighborSegments=0;
for(let rootIndex=0;rootIndex<240;rootIndex++){
  const edges=createRootNeighborGeometry(data,rootIndex),edgePositions=edges.getAttribute('position');
  assert.equal(edgePositions.count,112);
  for(let j=0;j<56;j++){
    const ends=[rootIndex,data.roots[rootIndex].neighbors[j]];
    for(let end=0;end<2;end++)for(let axis=0;axis<3;axis++)assert(Math.abs(edgePositions.array[j*6+end*3+axis]-position.array[ends[end]*3+axis])<1e-7);
    neighborSegments++;
  }
  edges.dispose();
}
assert.throws(()=>createRootNeighborGeometry(data,240),/56 verified neighbors/);

// Interrupted transitions must continue from the current mixture. This also
// tests the presentation clock independently of the paused simulation clock.
const anchorSets=[NODE_ANCHORS.map(p=>[...p]),NODE_ANCHORS.map(([x,y,z])=>[x*.8,y+1,z-.3]),Array.from({length:5},(_,i)=>[0,-3.5+i*1.75,0]),NODE_ANCHORS.map(([x,y,z],i)=>[x*.81,y*.94,z+i*.2])];
const anchorCopy=JSON.stringify(anchorSets),transition=createTransitionController(anchorSets);
const snapshot=()=>({positions:transition.positions.map(p=>p.toArray()),weights:Array.from(transition.weights),scales:Array.from(transition.scales)});
const assertSame=(left,right)=>{
  for(const key of ['positions','weights','scales']){
    const a=left[key].flat(),b=right[key].flat();assert.equal(a.length,b.length);
    for(let i=0;i<a.length;i++)assert(Math.abs(a[i]-b[i])<1e-6,`Discontinuous transition ${key}`);
  }
};
let transitionSamples=0;
function checkMixture(){
  const state=snapshot();
  assert(Math.abs(state.weights.reduce((sum,x)=>sum+x,0)-1)<1e-6);
  assert(state.weights.every(x=>x>=-1e-7&&x<=1+1e-7));
  assert(state.positions.flat().every(Number.isFinite));
  assert(state.scales.every(x=>x>=.66&&x<=1.01));
  transitionSamples++;
}
transition.to(1,0,2.2);transition.update(.65);checkMixture();
for(const [next,time] of [[2,.65],[3,1.1],[0,1.35],[2,1.5]]){
  transition.update(time);const before=snapshot();transition.to(next,time,2.2);assertSame(snapshot(),before);checkMixture();
}
for(let i=0;i<=100;i++){transition.update(1.5+2.2*i/100);checkMixture();}
assertSame({positions:anchorSets[2],weights:[0,0,1,0],scales:Array(5).fill(.67)},snapshot());
transition.to(1,10,0);checkMixture();
assertSame({positions:anchorSets[1],weights:[0,1,0,0],scales:[1,1,1,1,.9]},snapshot());
const held=snapshot();transition.update(100);assertSame(snapshot(),held);
assert.equal(JSON.stringify(anchorSets),anchorCopy,'Transitions must not mutate their input anchors');

// A full hour of camera motion stays on the viewing side at fixed radius.
// Project the labeled nodes' bounding boxes to check usable narrow framing.
let cameraSamples=0,frustumPoints=0;
const tanHalfFov=Math.tan(43*Math.PI/360);
for(const aspect of [.25,.5,1,16/9,4]){
  const distance=cameraFrameDistance(aspect);
  assert(Number.isFinite(distance)&&distance>=16.9);
  assert(distance*tanHalfFov*aspect>=7.1-1e-9);
  for(let i=0;i<=720;i++){
    const p=boundedCameraPosition(i*5,distance);
    assert([p.x,p.y,p.z].every(Number.isFinite));
    assert(Math.abs(p.length()-distance)<1e-9);
    assert(p.z>.99*distance,'Autonomous camera must remain in front of the reference layout');
    cameraSamples++;
  }
  const camera=new THREE.PerspectiveCamera(43,aspect,.1,120);
  for(const time of [0,15,60,300,1800,3600]){
    camera.position.copy(boundedCameraPosition(time,distance));camera.lookAt(0,0,0);camera.updateMatrixWorld();
    for(const anchor of NODE_ANCHORS)for(const x of [-1.25,1.25])for(const y of [-1.25,1.25])for(const z of [-1.25,1.25]){
      const p=new THREE.Vector3(anchor[0]+x,anchor[1]+y,anchor[2]+z).project(camera);
      assert(Math.abs(p.x)<1&&Math.abs(p.y)<1&&Math.abs(p.z)<1,'Reference node must remain inside the bounded camera frame');
      frustumPoints++;
    }
  }
}

// Measured label boxes must remain inside the usable region and separated
// even when five projected objects coincide in the smallest supported view.
const layoutBundle=await build({entryPoints:[path.join(web,'resonance-layout.js')],bundle:true,write:false,format:'cjs',platform:'node',target:'node22',logLevel:'silent'});
const layout={exports:{}};
new Function('module','exports','require',layoutBundle.outputFiles[0].text)(layout,layout.exports,runtimeRequire);
const {placeLabels}=layout.exports;
let labelLayouts=0;
for(const width of [320,360,736,1100]){
  const height=680,points=Array.from({length:5},(_,i)=>({id:`node-${i}`,x:width/2,y:height/2,visible:true}));
  const sizes=Object.fromEntries(points.map(p=>[p.id,{width:110,height:44}]));
  const options={top:width<580?170:100,bottom:width<580?185:125,gap:7};
  const input=JSON.stringify(points),placed=placeLabels(points,sizes,width,height,options);
  assert.equal(placed.filter(p=>p.visible).length,5);
  for(const p of placed){
    assert(p.x-p.width/2>=8-1e-9&&p.x+p.width/2<=width-8+1e-9);
    assert(p.y>=options.top&&p.y+p.height<=height-options.bottom+1e-9);
  }
  for(let i=0;i<placed.length;i++)for(let j=i+1;j<placed.length;j++){
    const a=placed[i],b=placed[j];
    assert(a.x+a.width/2+7<=b.x-b.width/2+1e-9||b.x+b.width/2+7<=a.x-a.width/2+1e-9||a.y+a.height+7<=b.y+1e-9||b.y+b.height+7<=a.y+1e-9,'Measured labels must not overlap');
  }
  assert.equal(JSON.stringify(points),input,'Label layout must not mutate projected geometry');
  const focused=placeLabels(points,sizes,width,height,{...options,focus:'node-2'});
  assert.deepEqual(focused.filter(p=>p.visible).map(p=>p.id),['node-2']);
  const invalid=[{id:'outside-left',x:-1000,y:200},{id:'outside-bottom',x:200,y:1000},{id:'nonfinite',x:NaN,y:200},{id:'occluded',x:200,y:200,visible:false}];
  assert(placeLabels(invalid,{},width,height,options).every(p=>!p.visible));
  labelLayouts++;
}
assert.deepEqual(placeLabels([],{},0,680),[]);

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
assert.equal((html.match(/aria-label="[^"]+: [^"]+" class="node-label /g)||[]).length,5);
assert(html.includes('class="resonance-canvas" role="img" aria-label='));
assert(html.includes('Opening the resonance field'));
assert(!html.includes('The 3D scene could not start'));
console.log(JSON.stringify({schema:'pp-resonance-scene-checks/1',scene_modes:SCENE_MODES.length,root_points:240,coxeter_orbits:8,exact_adjacency_pairs:edges,displayed_neighbor_segments:neighborSegments,phase_branches:264,primitive_phase_branches:240,deterministic_geometries:geometries.length,transition_samples:transitionSamples,camera_samples:cameraSamples,projected_frustum_points:frustumPoints,label_layout_widths:labelLayouts,curve_samples:curveSamples,payload_sha256:envelope.payload_sha256,esbuild_scene_bundle:true,react_server_markup:true,autonomous_default:true,browser_qa:false,passed:true}));
