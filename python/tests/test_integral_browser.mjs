// Run directly: node python/tests/test_integral_browser.mjs
// Executes the actual shipped browser BigInt engine against retained Python
// mathematical records, then checks every current source/receipt digest.
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
import {createHash} from 'node:crypto';
import {createRequire} from 'node:module';
const root=path.resolve(path.dirname(fileURLToPath(import.meta.url)),'../..');
const read=p=>JSON.parse(fs.readFileSync(path.join(root,p),'utf8'));
const sha=bytes=>createHash('sha256').update(bytes).digest('hex');
const envelope=read('web/integral-families/browser-data.json');
assert.equal(envelope.schema,'pp-integral-browser/1');
assert.equal(sha(envelope.payload_json),envelope.payload_sha256);
const data=JSON.parse(envelope.payload_json);
const require=createRequire(import.meta.url);
const E=require(path.join(root,'web/integral-families/engine.js'));
let generating=0,pairs=0,angles=0,moments=0,e8=0,sourceDigests=0;
assert.equal(data.generating.families.length,130);
for(const row of data.generating.families){
 const actual=E.generatingFamily(row.m,row.family);
 for(const field of ['family','m','weight','harmonic_coefficients','zeta_coefficients','harmonic_insertions','strict_sign'])
  assert.deepEqual(actual[field],row[field],`${row.family} m=${row.m}: ${field}`);
 generating++;
}
assert.equal(data.pairs.length,120);
for(const row of data.pairs){
 const actual=E.cancellation(row.r,row.s);
 assert.equal(actual.A,String(row.A));assert.equal(actual.D,String(row.D));
 for(let j=0;j<row.cancellation_jets.length;j++){
  const jet=row.cancellation_jets[j];
  assert.equal(actual.multipliers[j],jet.multiplier);
  assert.equal(E.Q(jet.endpoint_even_derivative_scaled).mul(actual.multipliers[j]).toString(),'0');
 }
 pairs++;
}
for(const row of data.angles){
 const [n,d='1']=row.pi_multiple.split('/');
 assert.equal(n,'1');
 const actual=E.angleMoment(row.j,Number(d));
 assert.equal(actual.coefficient,row.exact.coefficient);
 assert.equal(actual.pi_power,row.exact.pi_power);
 angles++;
}
const first=read('receipts/period_bridge/results.json');
for(const row of first.raghava.arcsine_moment_bounds){
 const actual=E.rationalMoment(row.j,row.t,row.terms);
 for(const field of ['partial','lower','upper'])assert.equal(actual[field],row[field]);
 assert.equal(actual.tail,row.tail_absolute);
 moments++;
}
assert.equal(data.e8._adjoint_verified,true);
assert.equal(data.e8.adjoint_lift.lie_bracket_verification.complete_basis_triple_sweep,true);
for(const weight of [2,4,6,8,10,12]){
 const actual=E.e8Factors(weight);
 assert.equal(actual.combined_pi,data.e8.combined_model.pi_coefficients[String(weight)]);
 e8++;
}
assert.equal(E.e8Factors(2).combined_pi,'0');
const sourcePaths={summary:'receipts/period_bridge/summary.json',results:'receipts/period_bridge/results.json',
 deep_summary:'receipts/period_bridge_deep/summary.json',deep_results:'receipts/period_bridge_deep/results.json',
 adjoint_lift:'receipts/period_bridge_deep/e8_lift.json',dirichlet:'receipts/period_bridge_deep/dirichlet.json',
 observability:'receipts/period_bridge_deep/observability.json',coxeter:'receipts/period_bridge_deep/coxeter.json'};
for(const [key,file] of Object.entries(sourcePaths)){
 assert.equal(sha(fs.readFileSync(path.join(root,file))),envelope.source_sha256[key],`receipt digest ${key}`);
 sourceDigests++;
}
const deep=read('receipts/period_bridge_deep/results.json'),summary=read('receipts/period_bridge_deep/summary.json');
assert.equal(summary.results_sha256,sha(fs.readFileSync(path.join(root,sourcePaths.deep_results))));
for(const [file,expected] of Object.entries(envelope.code_sha256)){
 assert.equal(sha(fs.readFileSync(path.join(root,file))),expected,`current source digest ${file}`);
 assert.equal(deep.source_sha256[file],expected);
 assert.equal(summary.source_sha256[file],expected);
 sourceDigests++;
}
for(const [name,expected] of Object.entries(deep.child_receipts))
 assert.equal(sha(fs.readFileSync(path.join(root,'receipts/period_bridge_deep',name))),expected,`child digest ${name}`);
const retained=read('receipts/period_bridge_deep/retained_browser_evidence.json');
assert.equal(envelope.payload_sha256,retained.payload_sha256,'all established browser math remains byte-identical');
for(const call of [()=>E.generatingFamily(65),()=>E.generatingFamily(-1),()=>E.generatingFamily(1,'invalid'),
 ()=>E.rationalMoment(1,'2',16),()=>E.angleMoment(1,2)])assert.throws(call);
console.log(JSON.stringify({schema:'pp-integral-browser-tests/1',generating,pairs,angles,moments,e8,sourceDigests,
 historical_math_payload_preserved:true,payload_sha256:envelope.payload_sha256,passed:true}));
