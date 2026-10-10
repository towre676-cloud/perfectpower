/* DOM execution check. Install linkedom separately; no browser/layout claim. */
const fs = require('node:fs');
const vm = require('node:vm');
const assert = require('node:assert/strict');
const {parseHTML} = require('linkedom');
const path = require('node:path');
const source = process.argv[2] || path.join(__dirname, '../receipts/exact_space/index.html');
const {document} = parseHTML(fs.readFileSync(source, 'utf8'));
function select(id, value) {
  // linkedom's select.value has a getter but no setter. Supply selected options.
  const options = [...document.getElementById(id).querySelectorAll('option')];
  options.forEach(o => o.removeAttribute('selected'));
  options.find(o => o.value === value).selected = true;
}
select('filter', 'all'); select('objective', '3,5');
const context = vm.createContext({document, console});
const code = [...document.querySelectorAll('script')].filter(s => !s.type)[0].textContent;
vm.runInContext(code, context);
const text = id => document.getElementById(id).textContent;
assert.equal(text('count'), '500,000,000,001');
assert.match(text('selection'), /200,000,000,014/);
const saved = JSON.parse(document.getElementById('data').textContent);
select('filter', 'restricted');
document.getElementById('rank').value = saved.results.restricted_population.rank;
vm.runInContext('evaluate()', context);
assert.equal(text('count').replaceAll(',', ''), saved.results.restricted_population.count);
saved.results.restricted_population.point.forEach(v => assert.ok(text('selection').includes(BigInt(v).toLocaleString('en-US'))));
let checked = 0;
for (const filtered of [false, true]) {
  select('filter', filtered ? 'restricted' : 'all');
  for (let B = 0; B < 61; B++) {
    const points = [];
    for (let x = 0; x <= B; x++) {
      const y = (B-x)/2;
      if (Number.isInteger(y) && (!filtered || x%3 === 1 && y%5 === 2)) points.push([x,y]);
    }
    document.getElementById('budget').value = String(B);
    if (!points.length) {
      document.getElementById('rank').value = '0'; vm.runInContext('evaluate()', context);
      assert.match(text('error'), /empty population/); continue;
    }
    for (const rank of new Set([0, Math.floor(points.length/2), points.length-1])) {
      document.getElementById('rank').value = String(rank);
      for (const [a,b] of [[3,5],[1,3],[1,2]]) {
        select('objective', `${a},${b}`); vm.runInContext('evaluate()', context);
        assert.equal(text('error'), ''); assert.equal(text('count'), String(points.length));
        const [x,y] = points[rank];
        assert.ok(text('selection').includes(`x = ${x} · y = ${y}`));
        const scores = points.map(([x,y]) => a*x+b*y), max = Math.max(...scores);
        assert.match(text('optimum'), new RegExp('Maximum objective'+max)); checked++;
      }
    }
  }
}
document.getElementById('budget').value = '18446744073709551616';
vm.runInContext('evaluate()', context); assert.match(text('error'), /below 2/);
select('filter', 'all');
document.getElementById('budget').value = '10'; document.getElementById('rank').value = 'x';
vm.runInContext('evaluate()', context); assert.match(text('error'), /unsigned integer rank/);
document.getElementById('tab-evidence').onclick();
assert.equal(document.getElementById('evidence').hidden, false);
assert.equal(document.getElementById('space').hidden, true);
assert.equal(document.querySelectorAll('tbody tr').length, saved.benchmark ? saved.benchmark.population_cases.length : 0);
console.log(JSON.stringify({status:'passed', checkedQueries:checked, scope:'DOM execution and exact BigInt answers; layout not rendered'}));
