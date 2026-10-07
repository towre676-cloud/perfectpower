import assert from 'node:assert/strict';
import fs from 'node:fs';
import {calendarPhase,longCount,crt,integerInput,calendarPopulation,overlap,orderedDrifts} from '../lib/dresden-math.ts';
const fixtures=JSON.parse(fs.readFileSync(new URL('./python-fixtures.json',import.meta.url)));
for(const f of fixtures.days){const n=BigInt(f.day),p=calendarPhase(n);assert.deepEqual([p.number,p.sign,p.haab],f.phase);assert.equal(longCount(n),f.long_count);}
const source=JSON.parse(fs.readFileSync(new URL('../lib/data/eclipse_stations.json',import.meta.url)));const stations=source.stations.filter(s=>s.classification==='intended').map(s=>s.month);
for(const f of fixtures.overlap){const schedule=overlap(stations,Array.from({length:5},(_,i)=>i===f.short_index?223:358));assert.equal(schedule.first.size,f.residues);for(const h of f.counts)assert.equal(schedule.count(BigInt(h.hi)).toString(),h.count);}
for(let m=1n;m<14n;m++)for(let n=1n;n<14n;n++)for(let a=0n;a<m;a++)for(let b=0n;b<n;b++){const hit=crt(a,m,b,n);const values=[];for(let d=0n;d<m*n;d++)if(d%m===a&&d%n===b)values.push(d);assert.equal(hit===null,values.length===0);if(hit)assert.equal(hit.residue,values[0]);}
assert.equal(calendarPopulation(0n,37960n*10n**30n,true),10n**30n+1n);
for(const bad of ['-1','1.2','1e30','','1'.repeat(121)])assert.throws(()=>integerInput(bad));
assert.equal(Math.min(...Array.from({length:5},(_,i)=>Math.max(...orderedDrifts(i).map(Math.abs)))).toFixed(5),'0.22916');
console.log('PASS: 25 Python calendar/Long Count fixtures up to 10^100; all five overlap policies at seven horizons; exhaustive small noncoprime CRT; exact huge counts; invalid inputs; minimax display.');
