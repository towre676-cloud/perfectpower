"""Render a dependency-free interactive view of the exact curve receipts."""
import json
from pathlib import Path


def render(output=None):
    root=Path(__file__).resolve().parents[1]
    directory=root/'receipts/algebraic_curve_extensions'
    data={name:json.loads((directory/(name+'.json')).read_text()) for name in (
        'summary','symmetry_quotients','algebraic_local_execution',
        'differential_extensions','ramified_smooth_models',
        'arithmetic_projector_obstructions','jacobian_isogenies')}
    payload=json.dumps(data,separators=(',',':')).replace('<','\\u003c')
    page=r'''<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>PerfectPower · Algebraic curve workbench</title>
<style>
:root{color-scheme:light;--ink:#153344;--teal:#087d80;--line:#cadbdc;--muted:#486577}
*{box-sizing:border-box}body{margin:0;background:#f3f7f7;color:var(--ink);font:16px/1.6 system-ui,sans-serif}
main{max-width:1190px;margin:auto;padding:40px 28px}h1{font-size:clamp(30px,4vw,49px);line-height:1.16;letter-spacing:-1.4px;margin:12px 0 20px}
h2{font-size:23px;margin:0 0 14px}.eyebrow{letter-spacing:2px;font-size:12px;font-weight:750;color:var(--teal)}
.intro{max-width:860px;color:var(--muted)}a{color:var(--teal)}.stats{display:grid;grid-template-columns:repeat(4,1fr);gap:15px;margin:28px 0}
.stat,.card{background:white;border:1px solid var(--line);border-radius:12px;padding:22px}.stat strong{display:block;font-size:34px;color:var(--teal)}
.stat span{font-size:13px;color:var(--muted)}nav{display:flex;gap:8px;flex-wrap:wrap;margin:30px 0 20px}
button,select{font:inherit;border:1px solid var(--line);border-radius:7px;padding:9px 13px;background:white;color:var(--ink)}
button{cursor:pointer}button[aria-selected=true]{background:var(--ink);color:white}select{max-width:100%;margin:8px 0 18px}
.grid{display:grid;grid-template-columns:1fr 1fr;gap:18px}.muted{color:var(--muted);font-size:14px}.formula{font:15px/1.7 ui-monospace,monospace;overflow-wrap:anywhere;background:#eef5f5;padding:14px;border-radius:6px}
dl{display:grid;grid-template-columns:1fr 1fr;gap:6px 18px}dt{color:var(--muted)}dd{margin:0;font-weight:650}
pre{font:12px/1.6 ui-monospace,monospace;white-space:pre-wrap;overflow-wrap:anywhere;max-height:550px;overflow:auto;background:#eef5f5;padding:18px;border-radius:6px}
summary{cursor:pointer;font-weight:650;margin:12px 0}svg{display:block;width:100%;max-width:400px;margin:10px auto}input[type=range]{width:100%;accent-color:var(--teal)}
.result{border-left:4px solid var(--teal);padding:13px 17px;background:#eef5f5}.panel[hidden]{display:none}
footer{margin-top:28px;font-size:13px;color:var(--muted)}@media(max-width:760px){main{padding:25px 16px}.grid{grid-template-columns:1fr}.stats{grid-template-columns:1fr 1fr}}
</style></head><body><main>
<div class="eyebrow">PERFECTPOWER / EXACT RESEARCH OBJECTS</div><h1>From the polynomial<br>to its executable geometry.</h1>
<p class="intro">Explore actual quotient maps, algebraic degeneration charts and a precise obstruction to false splitting. Every displayed mathematical packet comes from the checked research corpus. This page works offline.</p>
<p><a href="ALGEBRAIC_CURVE_EXTENSIONS_MONOGRAPH.pdf">Read the complete mathematical monograph</a> · <a href="../receipts/algebraic_curve_extensions/summary.json">Corpus summary</a></p>
<div class="stats" id="stats"></div><nav aria-label="Research views" role="tablist">
<button role="tab" aria-selected="true" data-panel="quotients">Actual quotient maps</button><button role="tab" aria-selected="false" data-panel="local">Local execution</button>
<button role="tab" aria-selected="false" data-panel="fields">Differential algebras</button><button role="tab" aria-selected="false" data-panel="arithmetic">Arithmetic obstruction</button></nav>
<section class="panel" id="quotients" role="tabpanel"><div class="grid"><div class="card"><h2>Verified finite-action quotient</h2><label for="quotientSelect">Choose a source and action</label><br><select id="quotientSelect"></select><div id="quotientInfo"></div></div>
<div class="card"><h2>From covers to a Jacobian isogeny</h2><div id="isogenyInfo"></div><p class="muted">Actual maps supply the algebraic homomorphisms. A differential projector by itself does not establish this conclusion.</p></div></div>
<details class="card"><summary>Exact quotient, connection and pullback receipt</summary><pre id="quotientReceipt"></pre></details></section>
<section class="panel" id="local" role="tabpanel" hidden><div class="card"><h2>Algebraic points, branches and infinity</h2><label for="localSelect">Choose the local calculation</label><br><select id="localSelect"></select><p id="localExplanation"></p><pre id="localReceipt"></pre></div></section>
<section class="panel" id="fields" role="tabpanel" hidden><div class="card"><h2>Keep every algebraic branch</h2><p>Finite étale algebras retain their defining polynomial and may be products of fields. Unique extended derivations, fixed algebras and complete tensor models can be checked without approximate roots.</p><label for="fieldSelect">Choose an algebraic calculation</label><br><select id="fieldSelect"></select><pre id="fieldReceipt"></pre></div></section>
<section class="panel" id="arithmetic" role="tabpanel" hidden><div class="grid"><div class="card"><h2>Does the character sector descend?</h2><p>The geometric action x → ζ₅x on y² = x⁵+t has characters 1, 2, 3 and 4. Rational sectors commuting with it must contain complete Galois orbits.</p><label for="projectorSelect">Choose the character selection</label><br><select id="projectorSelect"></select>
<label for="orbitStep">Apply the Galois generator ζ₅ → ζ₅²: <strong id="stepLabel"></strong></label><input id="orbitStep" type="range" min="0" max="3" value="0">
<svg id="orbitDiagram" viewBox="0 0 400 350" aria-label="Cyclotomic character orbit"></svg><div id="orbitResult" class="result"></div></div>
<div class="card"><h2>The exact obstruction</h2><p>A rational projector commuting with the integral cyclic action has a rational characteristic polynomial on its image. Either rank-two selection fails this necessary condition.</p><pre id="obstructionReceipt"></pre><p class="muted">The full orbit passes this necessary test. Passing is not a proof of an algebraic correspondence or a general Jacobian decomposition.</p></div></div></section>
<footer>Exact identities and finite formal jets within declared budgets. General stable reduction, automatically marked integral kernels, arbitrary correspondences and rigorous analytic continuation remain further work. No numerical mesh is identified with this continuous de Rham structure.</footer>
</main><script type="application/json" id="researchData">__DATA__</script><script>
'use strict';
const data=JSON.parse(document.getElementById('researchData').textContent);
const el=id=>document.getElementById(id), pretty=o=>JSON.stringify(o,null,2);
const labels={genus_two_plus:'Genus 2 · reciprocal lift +',genus_two_minus:'Genus 2 · reciprocal lift −',genus_three_elliptic:'Genus 3 · elliptic quotient',genus_three_genus_two:'Genus 3 · genus-two quotient',even_sextic:'Even sextic · reflection',order_three_mobius:'Order 3 · Möbius action',cyclotomic_order_five:'Order 5 · cyclotomic action',conjugated_reciprocal:'Translated reciprocal action'};
function options(target,items){for(const [value,label] of items){const o=document.createElement('option');o.value=value;o.textContent=label;target.append(o)}}
for(const [number,label] of [[data.summary.persistent_object_kinds,'persistent object kinds'],[data.summary.symmetry_quotients,'verified quotients'],[data.summary.finite_algebraic_degeneration_roots,'finite algebraic degeneration roots'],[data.summary.jacobian_isogeny_degrees.join(' / '),'paired-cover isogeny degrees']]){
 const card=document.createElement('div');card.className='stat';const strong=document.createElement('strong');strong.textContent=number;const span=document.createElement('span');span.textContent=label;card.append(strong,span);el('stats').append(card)}
for(const tab of document.querySelectorAll('[data-panel]'))tab.addEventListener('click',()=>{for(const t of document.querySelectorAll('[data-panel]'))t.setAttribute('aria-selected',String(t===tab));for(const p of document.querySelectorAll('.panel'))p.hidden=p.id!==tab.dataset.panel});
function polynomial(a,variable){return a.map((c,i)=>`(${typeof c==='object'?scalar(c):c})${i?' '+variable+(i>1?'^'+i:''):''}`).join(' + ')}
function scalar(c){if(Array.isArray(c))return '['+c.map(scalar).join(', ')+']';if(c&&c.numerator){const n=polynomial(c.numerator,'t'),d=polynomial(c.denominator,'t');return c.denominator.length===1&&c.denominator[0]==='1'?n:'('+n+') / ('+d+')'}return String(c)}
function rational(p){return '('+polynomial(p.numerator,'x')+') / ('+polynomial(p.denominator,'x')+')'}
function addText(parent,tag,text,cls){const e=document.createElement(tag);e.textContent=text;if(cls)e.className=cls;parent.append(e);return e}
options(el('quotientSelect'),Object.keys(data.symmetry_quotients).map(k=>[k,labels[k]]));
function quotient(){const key=el('quotientSelect').value,record=data.symmetry_quotients[key],q=record.quotient,box=el('quotientInfo');box.replaceChildren();
 addText(box,'p','u = '+rational(q.u),'formula');if(q.v_over_y)addText(box,'p','w / y = '+rational(q.v_over_y),'formula');
 addText(box,'p',q.target_coefficients?'w² = '+polynomial(q.target_coefficients,'u'):q.target_equation,'formula');
 const dl=document.createElement('dl');for(const [label,value] of [['Source genus',q.source_genus],['Quotient genus',q.target_genus],['Map degree',q.map_degree],['Invariant rank',q.projector.rank],['Selected operator order',record.observable?record.observable.order:'No first cohomology']]){addText(dl,'dt',label);addText(dl,'dd',String(value))}box.append(dl);el('quotientReceipt').textContent=pretty(record);
 const isoBox=el('isogenyInfo');isoBox.replaceChildren();const pairKey=key.startsWith('genus_two_')?'genus_two_plus':key.startsWith('genus_three_')?'genus_three_elliptic':null;
 if(pairKey){const r=data.jacobian_isogenies[pairKey];addText(isoBox,'p','Jac(C) → '+r.quotient_genera.map(g=>'Jac(C genus '+g+')').join(' × '),'formula');addText(isoBox,'p','Isogeny degree '+r.isogeny_degree+'; full de Rham rank '+r.cohomology_rank+'; holomorphic rank '+r.holomorphic_pullback_rank+'.');addText(isoBox,'p',r.composition_identities.join('; '),'formula');addText(isoBox,'p','Kernel annihilated by '+r.kernel_annihilator+'. Explicit kernel generators and integral markings remain open.');const detail=document.createElement('details');addText(detail,'summary','Paired-cover certificate');addText(detail,'pre',pretty(r));isoBox.append(detail)}else addText(isoBox,'p','This view displays one quotient. The paired-involution certificates in this corpus are the reciprocal genus-two and genus-three examples.');}
el('quotientSelect').addEventListener('change',quotient);quotient();
const localNotes={quintic_all_finite:'All four algebraic degeneration parameters of x⁵−x+t, represented by exact quotient algebras.',legendre_all_finite:'The two finite Legendre degeneration locations, including repeated discriminant roots.',quintic_node_branches:'At 3125α⁴−256=0 the collision is x=5α/4. The conjugate branches have exact second coefficient 1/4 and are executed through order eight.',quintic_logarithmic_jet:'Finite logarithmic execution over the algebraic node coefficient algebra.',legendre_infinity_resonance:'The positive resonance at order one is resolved by coupled logarithmic recurrences; the formal jet is complete through order twelve.',legendre_ramified:'Exact Legendre chart after parameter ramification of order three.'};
const localRecords={...data.algebraic_local_execution,...data.ramified_smooth_models};options(el('localSelect'),Object.keys(localRecords).map(k=>[k,k.replaceAll('_',' ')]));function local(){const k=el('localSelect').value;el('localExplanation').textContent=localNotes[k]||'Verified ramified centered-binomial smooth model with exact substitution and independent connection replay.';el('localReceipt').textContent=pretty(localRecords[k])}el('localSelect').addEventListener('change',local);local();
options(el('fieldSelect'),Object.keys(data.differential_extensions).map(k=>[k,k.replaceAll('_',' ')]));function field(){el('fieldReceipt').textContent=pretty(data.differential_extensions[el('fieldSelect').value])}el('fieldSelect').addEventListener('change',field);field();
const checks=data.arithmetic_projector_obstructions.checks;options(el('projectorSelect'),checks.map((r,i)=>[String(i),'Rank '+r.de_rham_checks.rank+' · characters {'+r.selected_characters.join(', ')+'}']).concat([['full','Full Galois orbit {1, 2, 3, 4}']]));
function orbit(){const index=el('projectorSelect').value,step=Number(el('orbitStep').value),base=index==='full'?[1,2,3,4]:checks[Number(index)].selected_characters,selected=base.map(k=>(k*2**step)%5);el('stepLabel').textContent=String(step);const svg=el('orbitDiagram');svg.replaceChildren();const points={1:[200,50],2:[340,175],4:[200,300],3:[60,175]},ns='http://www.w3.org/2000/svg';function shape(tag,attrs,text){const n=document.createElementNS(ns,tag);for(const [k,v] of Object.entries(attrs))n.setAttribute(k,String(v));if(text!==undefined)n.textContent=text;svg.append(n);return n}
 for(const k of [1,2,4,3]){const a=points[k],b=points[(k*2)%5];shape('line',{x1:a[0],y1:a[1],x2:b[0],y2:b[1],stroke:'#bdd5d5','stroke-width':3});}
 for(const k of [1,2,3,4]){const [x,y]=points[k];shape('circle',{cx:x,cy:y,r:35,fill:selected.includes(k)?'#087d80':'#eef5f5',stroke:base.includes(k)?'#153344':'#cadbdc','stroke-width':base.includes(k)?4:1});shape('text',{x,y:y+7,'text-anchor':'middle',fill:selected.includes(k)?'white':'#153344','font-size':22,'font-family':'system-ui'},k)}
 const escaped=selected.filter(k=>!base.includes(k));el('orbitResult').textContent='Selected characters after conjugation: {'+selected.join(', ')+'}. '+(escaped.length?'Characters outside the starting sector: {'+escaped.join(', ')+'}.':'This step stays inside the starting sector.')+' '+(index==='full'?'The full orbit passes this necessary rationality check.':'The complete orbit is larger than this rank-two sector: rational Betti compatibility is obstructed.');el('obstructionReceipt').textContent=pretty(index==='full'?{selected_characters:base,rational_character_orbits:checks[0].rational_character_orbits,status:'Necessary orbit condition satisfied; no sufficiency claim'}:checks[Number(index)]);}
el('projectorSelect').addEventListener('change',orbit);el('orbitStep').addEventListener('input',orbit);orbit();
</script></body></html>'''
    output=Path(output or root/'docs/algebraic_curve_workbench.html')
    output.parent.mkdir(parents=True,exist_ok=True)
    output.write_text(page.replace('__DATA__',payload))
    print(output)


if __name__=='__main__':render()
