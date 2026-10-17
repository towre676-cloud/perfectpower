/* Cross-language checks of the shipped atlas model and source-bound geometry. */
'use strict';
const assert=require('node:assert/strict'),fs=require('node:fs'),path=require('node:path'),crypto=require('node:crypto'),{execFileSync}=require('node:child_process');
const root=path.resolve(__dirname,'../..'),M=require(path.join(root,'web/integral-families/atlas-model.js'));
const sha=x=>crypto.createHash('sha256').update(x).digest('hex');
const e=JSON.parse(fs.readFileSync(path.join(root,'web/integral-families/atlas-data.json'),'utf8'));
assert.equal(sha(e.payload_json),e.payload_sha256);const d=JSON.parse(e.payload_json);
for(const [file,hash] of Object.entries(d.source_sha256))assert.equal(sha(fs.readFileSync(path.join(root,file))),hash);
assert.equal(d.roots.length,240);assert.equal(new Set(d.roots.map(r=>r.doubled_root.join(','))).size,240);
let neighborChecks=0;
for(const r of d.roots){assert.equal(r.doubled_root.reduce((a,x)=>a+x*x,0),8);assert.equal(r.neighbors.length,56);assert.equal(r.next,Math.floor(r.id/30)*30+(r.id+1)%30);for(const j of r.neighbors){const q=d.roots[j];assert.equal(r.doubled_root.reduce((a,x,k)=>a+x*q.doubled_root[k],0),4);assert(q.neighbors.includes(r.id));neighborChecks++;}const next=d.roots[r.next],a=2*Math.PI/30;assert(Math.abs(next.x-(r.x*Math.cos(a)+r.y*Math.sin(a)))<2e-11);assert(Math.abs(next.y-(-r.x*Math.sin(a)+r.y*Math.cos(a)))<2e-11);assert(Math.abs(Math.hypot(r.x,r.y)-d.orbit_radii[r.orbit])<2e-11);}
let powerChecks=0;for(let p=1;p<=264;p++){const rows=M.branches(p);assert.equal(rows.filter(r=>r.primitive).length,240);assert.equal(new Set(rows.map(r=>p*r.exponent%443520)).size,264/M.gcd(p,264));for(const r of rows)assert.equal(r.primitive,M.gcd(r.exponent,443520)===1);powerChecks++;}
assert(M.branches(264).every(r=>Math.abs(r.angle-2*Math.PI/1680)<1e-13));
const expected=JSON.parse(execFileSync('python3',['-c',"import json\nfrom perfectpower.coxeter_mellin import zeta_factor\nprint(json.dumps([[f,n,s,str(zeta_factor('E' if f=='E8' else 'A' if n==1 else f,n,s))] for f,n in [('E8',8)]+[(f,n) for f in ('B','C') for n in (1,3,7,15,31)] for s in range(2,13)]))"],{cwd:root,env:{...process.env,PYTHONPATH:path.join(root,'python')},encoding:'utf8'}));
for(const [kind,rank,s,q] of expected){assert.equal(M.exactFactors(kind,rank,s).total,q);const [n,v='1']=q.split('/'),value=Number(n)/Number(v),actual=M.factors(kind,rank,s).total;assert(Math.abs(value-actual)<1e-12*(1+Math.abs(value)));}
for(const k of [2,3,4,5,6])for(const kind of ['B','C'])assert.equal(M.exactFactors(kind,2**(k-1)-1,k).total,'0');
let curveChecks=0;for(const denominator of [3,6,12,840,221760])for(let j=1;j<=8;j++){const rows=M.convergence(j,denominator);assert.equal(rows[0].n,j);for(const r of rows){assert(Number.isFinite(r.logRatio));assert(r.ratio>=0&&r.ratio<=1+1e-12);assert(r.cumulative>=0&&r.cumulative<=1+1e-12);}curveChecks++;}
function simpson(kind,rank,s){const n=40000,end=40,dx=end/n;let sum=0;for(let i=0;i<=n;i++){const t=i*dx,value=i===0?(s===2?M.spectrum(kind,rank).rank:0):M.density(kind,rank,s,t);sum+=(i===0||i===n?1:i%2?4:2)*value;}return sum*dx/3;}
assert(Math.abs(simpson('E8',8,2))<1e-6);assert(Math.abs(simpson('B',7,4))<1e-7);assert(Math.abs(simpson('C',7,4))<1e-7);
for(const fn of [()=>M.branches(0),()=>M.branches(265),()=>M.spectrum('A',7),()=>M.factors('E8',8,1),()=>M.convergence(9,6),()=>M.density('E8',8,2,0)])assert.throws(fn);
console.log(JSON.stringify({schema:'pp-integral-atlas-checks/1',roots:240,exact_neighbor_checks:neighborChecks,power_maps:powerChecks,independent_python_coefficients:expected.length,arcsine_curves:curveChecks,numerical_zero_diagnostics:3,source_hashes:Object.keys(d.source_sha256).length,payload_sha256:e.payload_sha256,passed:true}));
