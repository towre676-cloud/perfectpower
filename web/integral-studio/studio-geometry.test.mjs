import assert from 'node:assert/strict';
import {gramMatrix, sampleDensity, ROOT_ANGLES, EXPONENTS} from './math-engine.mjs';
import {PRIMITIVE_30, GOLDEN_ROOT_ANGLES, goldenCharacter, splitDensity, densityDisplay, eigenSymmetric3, energySlice, ellipsoidPoint, normalizedEnergyPoint} from './studio-geometry.mjs';

assert.deepEqual(PRIMITIVE_30,EXPONENTS);
assert.deepEqual(GOLDEN_ROOT_ANGLES,ROOT_ANGLES);
assert.deepEqual(PRIMITIVE_30.map(goldenCharacter),[1,-1,1,-1,-1,1,-1,1]);

const density=sampleDensity([1,.5,.1,-.01],1000);
const parts=splitDensity(density);
assert.equal(parts.length,5);
assert.equal(parts.reduce((n,p)=>n+p.length,0),density.length);
for(const part of parts) {
  for(const root of ROOT_ANGLES) assert.ok(!(part[0].theta<root&&part.at(-1).theta>root),'No line segment may cross a log singularity');
}
const display=densityDisplay(density);
assert.equal(Math.max(...display.parts.flat().map(p=>p.position[1])),4.5);
for(const p of display.parts.flat())assert.ok(Math.abs(p.position[1]*display.maxDensity/4.5-p.density)<1e-9);

const gram=gramMatrix();
const coefficients=[[1,0,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1],[.3,-.7,.2,.5],[-2,1,-.04,.013],[0,0,0,0]];
let surfaceChecks=0;
for(const t of coefficients){
  const slice=energySlice(gram,t);
  assert.ok(slice.minimum>=-1e-9);
  assert.ok(slice.energy>=slice.minimum-1e-8);
  for(let k=0;k<3;k++){
    const v=slice.eigen.vectors[k],lambda=slice.eigen.values[k];
    for(let row=0;row<3;row++)assert.ok(Math.abs(slice.h[row].reduce((s,a,j)=>s+a*v[j],0)-lambda*v[row])<1e-12);
  }
  for(let i=0;i<32;i++)for(const fraction of [.23,.6,1]){
    const p=ellipsoidPoint(slice,i*.71,i*.31,fraction);
    const u=p.map((v,j)=>v/slice.worldScale+slice.center[j]);
    const original=[...u.map((v,j)=>v/slice.norms[j]),t[3]];
    const e=original.reduce((s,v,j)=>s+original.reduce((a,w,k)=>a+v*gram[j][k]*w,0),0);
    const expected=slice.minimum+fraction*(slice.level-slice.minimum);
    assert.ok(Math.abs(e-expected)<1e-9*Math.max(1,Math.abs(expected)),`Surface energy ${e} != ${expected}`);
    surfaceChecks++;
  }
  const point=normalizedEnergyPoint(slice);
  const restored=point.map((v,j)=>(v/slice.worldScale+slice.center[j])/slice.norms[j]);
  restored.forEach((v,j)=>assert.ok(Math.abs(v-t[j])<1e-10));
}
console.log(`Studio geometry: singularity-safe density, primitive phases, ${surfaceChecks} true Gram-energy surface points verified.`);
