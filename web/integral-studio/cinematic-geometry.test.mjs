import assert from 'node:assert/strict';
import fs from 'node:fs';
import {primitive1680,phaseFiber264,eigenphases30,characterEmbedding,powerMapCurves,e8Edges,compositionPositions,bezierPoint,orientPoint} from './cinematic-geometry.mjs';
const domain=primitive1680(),fiber=phaseFiber264(),phases=eigenphases30();
assert.equal(domain.length,384);
for(const p of phases)assert.equal(domain.filter(source=>source.phase===p.a).length,48);
assert.equal(fiber.length,264);
assert.equal(fiber.filter(p=>p.primitive).length,240);
assert.deepEqual(fiber.filter(p=>!p.primitive).map(p=>p.j),Array.from({length:24},(_,i)=>4+11*i));
for(const p of [...domain,...fiber,...phases])assert.ok(p.position.every(Number.isFinite));
for(const portrait of [false,true]){
 const positions=compositionPositions(portrait),curves=powerMapCurves(domain,phases,positions,{count:80});
 assert.equal(curves.length,80);
 for(const curve of curves){
  assert.equal(curve.source%30,curve.target);
  const source=domain.find(p=>p.a===curve.source),target=phases.find(p=>p.a===curve.target);
  assert.deepEqual(curve.points[0],orientPoint(source.position,'domain').map((v,i)=>v+positions.cyclotomic[i]));
  assert.deepEqual(curve.points.at(-1),orientPoint(target.position,'bridge').map((v,i)=>v+positions.bridge[i]));
  assert.ok(curve.points.flat().every(Number.isFinite));
  for(const t of [0,.13,.5,.91,1])assert.ok(bezierPoint(...curve.control,t).every(Number.isFinite));
 }
}
const roots=JSON.parse(fs.readFileSync(new URL('./e8-roots.json',import.meta.url),'utf8')).roots,edges=e8Edges(roots);
assert.equal(roots.length,240);assert.equal(edges.length,6720);
assert.equal(new Set(edges.map(p=>p.join(':'))).size,6720);
for(const [a,b] of edges)assert.equal(roots[a].doubled_root.reduce((sum,v,i)=>sum+v*roots[b].doubled_root[i],0),4);
for(let i=0;i<4096;i++)assert.ok(characterEmbedding(2*Math.PI*i/4096).every(Number.isFinite));
console.log('Cinematic geometry passed: 384→8 phases with 48 preimages each, 240/24 fiber split, 6720 genuine E8 adjacencies, 160 finite endpoint-exact mapping paths.');
