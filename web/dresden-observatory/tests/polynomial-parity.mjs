import assert from 'node:assert/strict';
import fs from 'node:fs';
import {polynomialCalendar,polynomialPresets} from '../lib/dresden-polynomial.ts';
const {cases}=JSON.parse(fs.readFileSync(new URL('./polynomial-python-fixtures.json',import.meta.url)));
for(const [i,c]of cases.entries()){
 const r=polynomialCalendar(c.predicate,BigInt(c.residue),BigInt(c.period),BigInt(c.lo),BigInt(c.hi),BigInt(c.rank));
 assert.equal(r.count.toString(),c.count,`count ${i}`);
 assert.equal(r.selected?.toString()??null,c.selected,`selection ${i}`);
 assert.deepEqual(r.parameterIntervals.map(row=>row.map(String)),c.intervals,`intervals ${i}`);
}
assert.equal(polynomialCalendar(polynomialPresets[0].predicate,0n,18980n,0n,10n**30n).count,16n);
for(const malformed of [{poly:[9007199254740992],relation:'='},{poly:['1e5'],relation:'='},{poly:[0],relation:'=='},{op:'not',args:[]},{poly:Array(10).fill('1'),relation:'='},{poly:['1'],relation:'=',extra:1}])assert.throws(()=>polynomialCalendar(malformed,0n,1n,0n,100n));
assert.throws(()=>polynomialCalendar({poly:['-2','0','1'],relation:'<'},0n,1n,0n,100n,0n,1),/budget/);
assert.throws(()=>polynomialCalendar(true,1n,1n,0n,100n));
assert.throws(()=>polynomialCalendar(true,0n,1n,10n,0n));
console.log(`PASS: ${cases.length} independent Python/browser polynomial calendars, repeated and irrational roots, all relations, Boolean operations, huge coefficients/bounds/ranks, signed bounds, malformed inputs and budget exhaustion.`);
