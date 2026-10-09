/** Device-local scenes and exact set comparison over the finite teaching domain. */
const KEY='perfectpower-room-scenes-v1';
const validRules=c=>c&&Number.isInteger(c.load)&&c.load>=1&&c.load<=48&&Number.isInteger(c.size)&&c.size>=3&&c.size<=15&&typeof c.square==='boolean';
export function members(models,c){return models.filter(d=>d.drive>=c.load*d.a&&d.size<=c.size&&(!c.square||Number.isInteger(Math.sqrt(d.drive)))).map(d=>d.id)}
export function compare(models,a,b){
 const A=new Set(members(models,a)),B=new Set(members(models,b));
 const result={both:[],onlyA:[],onlyB:[],neither:[]};
 for(const d of models)result[A.has(d.id)?B.has(d.id)?'both':'onlyA':B.has(d.id)?'onlyB':'neither'].push(d.id);
 return result;
}
const label=c=>`Lift ${c.load} · size ${c.size}${c.square?' · square':''}`;
export function createScenarios({models,getScene,restore,onChange,save,notify}){
 const $=id=>document.getElementById(id);let slots={A:null,B:null},active=false,partition=null,scenes=[],durable=true;
 const validScene=s=>s&&typeof s.name==='string'&&s.name.length<=64&&(s.kind==='workshop'?validRules(s.rules)&&['cost','lift','size'].includes(s.objective)&&typeof s.layout==='boolean'&&typeof s.hiddenRejected==='boolean'&&Number.isInteger(s.selected)&&s.selected>=-1&&s.selected<288:s.kind==='family'&&/^\d{1,61}$/.test(s.bound)&&/^\d{1,61}$/.test(s.rank)&&BigInt(s.bound)<=10n**60n&&BigInt(s.rank)<=2n*BigInt(s.bound));
 try{const data=JSON.parse(localStorage.getItem(KEY)||'[]');if(Array.isArray(data))scenes=data.filter(validScene).slice(0,12)}catch{durable=false}
 function persist(){try{localStorage.setItem(KEY,JSON.stringify(scenes));durable=true}catch{durable=false}}
 function renderScenes(){
  $('saved-scenes').replaceChildren();$('scene-storage').textContent=durable?'Saved on this device in this browser. Up to 12 scenes.':'Browser storage is unavailable. Scenes last for this open page.';
  $('saved-empty').hidden=!!scenes.length;
  scenes.forEach((s,i)=>{const row=document.createElement('div');row.className='saved-scene';const open=document.createElement('button');open.className='ghost scene-open';open.textContent=s.name;open.title=s.kind==='family'?`Exact family: T=${s.bound}, address ${s.rank}`:label(s.rules);open.onclick=()=>{active=false;$('compare-view').checked=false;renderComparison();restore(structuredClone(s));notify('Restored '+s.name+'.')};const del=document.createElement('button');del.textContent='×';del.setAttribute('aria-label','Delete saved scene '+s.name);del.onclick=()=>{scenes.splice(i,1);persist();renderScenes()};row.append(open,del);$('saved-scenes').append(row)})
 }
 function renderComparison(){
  const ready=!!(slots.A&&slots.B);partition=ready?compare(models,slots.A.rules,slots.B.rules):null;
  for(const key of ['A','B']){const s=slots[key];$('snapshot-'+key).textContent=s?`${label(s.rules)} · ${members(models,s.rules).length} designs`:'Capture current requirements';$('restore-'+key).disabled=!s}
  $('compare-view').disabled=!ready;$('compare-export').disabled=!ready;$('comparison-results').hidden=!ready;
  if(partition)for(const k of ['both','onlyA','onlyB','neither'])$('compare-'+k).textContent=partition[k].length;
  document.body.classList.toggle('comparing',active);$('compare-key').hidden=!active||getScene().kind==='family';$('legend').hidden=getScene().kind==='family'||active;
  onChange();
 }
 for(const k of ['A','B']){
  $('capture-'+k).onclick=()=>{const s=getScene();if(s.kind!=='workshop')return;slots[k]={rules:{...s.rules}};if(slots.A&&slots.B){active=true;$('compare-view').checked=true}renderComparison();notify(`Captured ${k}. Later slider changes leave this snapshot intact.`)};
  $('restore-'+k).onclick=()=>{if(!slots[k])return;restore({...getScene(),kind:'workshop',rules:{...slots[k].rules}});renderComparison()}
 }
 $('compare-view').onchange=()=>{active=$('compare-view').checked;renderComparison()};
 $('compare-export').onclick=()=>save('perfectpower-requirement-comparison.json',{schema:'pp-room-set-comparison/1',A:slots.A,B:slots.B,counts:Object.fromEntries(Object.entries(partition).map(([k,v])=>[k,v.length])),design_ids:partition,identity:'Stable zero-based design IDs; display labels use ID + 1.',scope:'Comparison of two complete subsets of the same 288 fictional designs.'});
 $('save-scene').onclick=()=>{if(scenes.length>=12){notify('Delete a saved scene before adding another.');return}const s=getScene();s.name=$('scene-name').value.trim().slice(0,64)||(s.kind==='family'?`Exact point ${s.rank}`:label(s.rules));scenes.unshift(s);$('scene-name').value='';persist();renderScenes();notify(durable?'Scene saved for your next visit.':'Scene saved for this open page.')};
 renderScenes();
 return {sync:renderComparison,get state(){return {active,slots:structuredClone(slots),partition:structuredClone(partition),saved:structuredClone(scenes)}},category(id){if(!active||!partition)return null;for(const k of ['both','onlyA','onlyB'])if(partition[k].includes(id))return k;return 'neither'},includes(id){return !active||!partition?null:!partition.neither.includes(id)},membership(id){if(!active||!partition)return '';const k=this.category(id);return k==='both'?'Works in both A and B.':k==='onlyA'?'Works only in A.':k==='onlyB'?'Works only in B.':'Works in neither A nor B.'}};
}
