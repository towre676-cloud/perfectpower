/* Displays finite, source-hashed backend exports; never rounds their integers. */
export function createComparisonNotebook(source, visit) {
 const $=id=>document.getElementById(id), dialog=$('exact-comparison');
 const labels={universe:'Whole room',left:'A / nonnegative x',right:'B / smaller y',both:'Both A and B',left_only:'Only A',right_only:'Only B',neither:'Neither',union:'A or B',symmetric_difference:'Exactly one'};
 let index=0,selected=0;
 const current=()=>source.comparisons[index];
 function record(){
  const row=current().examples[selected],v=row.record.values;
  $('comparison-point').textContent=`x = ${v.x}; y = ${v.y}`;
  $('comparison-object').textContent=`Original-object ID: ${row.object_id}`;
  $('comparison-category').textContent=labels[row.category];
  $('comparison-addresses').replaceChildren();
  for(const [key,label] of Object.entries(labels)){
   const tr=document.createElement('tr'),name=document.createElement('th'),address=document.createElement('td');
   name.scope='row';name.textContent=label;address.textContent=row.addresses[key]??'Excluded';tr.append(name,address);$('comparison-addresses').append(tr);
  }
  $('comparison-visit').textContent='Visit its whole-room address';
 }
 function draw(){
  const data=current();$('comparison-dataset').value=String(index);
  $('comparison-rule').textContent=`A keeps x ≥ 0. B keeps y ≤ ${6n*BigInt(data.cutoff)**2n}. Both rules are restricted to the whole room, y ≤ 6T², with T = ${data.ceiling}.`;
  $('exact-counts').replaceChildren();
  for(const key of ['both','left_only','right_only','neither']){
   const card=document.createElement('div'),label=document.createElement('span'),count=document.createElement('strong');
   card.className='partition-card '+key;label.textContent=labels[key];count.textContent=data.summary.counts[key];card.append(label,count);$('exact-counts').append(card);
  }
  const c=data.summary.counts;
  const sum=['both','left_only','right_only','neither'].reduce((s,k)=>s+BigInt(c[k]),0n);
  if(sum.toString()!==c.universe)throw new Error('Exported partition counts do not cover the universe.');
  $('comparison-identity').textContent=`The four counts add to ${c.universe}. The union contains ${c.union}; exactly one rule admits ${c.symmetric_difference}.`;
  $('comparison-samples').replaceChildren();
  data.examples.forEach((row,i)=>{const option=document.createElement('option');option.value=String(i);option.textContent=`${labels[row.category]} · whole-room address ${row.addresses.universe}`;$('comparison-samples').append(option)});
  $('comparison-samples').value=String(selected);$('comparison-replay-result').textContent='';record();
 }
 $('open-exact-comparison').onclick=()=>{draw();dialog.showModal();dialog.scrollTop=0};
 $('close-exact-comparison').onclick=()=>dialog.close();
 $('comparison-dataset').onchange=()=>{index=Number($('comparison-dataset').value);selected=0;draw()};
 $('comparison-samples').onchange=()=>{selected=Number($('comparison-samples').value);record()};
 $('comparison-visit').onclick=()=>{const data=current(),row=data.examples[selected];dialog.close();visit(BigInt(data.ceiling),BigInt(row.addresses.universe))};
 $('comparison-download').onclick=()=>{
  const blob=new Blob([JSON.stringify({schema:'pp-room-comparison-export/1',source_commit:source.source_commit,source_files:source.source_files,...current()},null,2)],{type:'application/json'});
  const url=URL.createObjectURL(blob),a=document.createElement('a');a.href=url;a.download='perfectpower-population-comparison.json';a.click();setTimeout(()=>URL.revokeObjectURL(url),1000);
 };
 const replay=$('comparison-replay');replay.disabled=!/^https?:$/.test(location.protocol);
 $('comparison-connection').textContent=replay.disabled?'Open the repository’s local query service at /atlas to replay these definitions through Python. This offline notebook displays exported backend evidence.':'Replay is available through this page’s local query service. The output is displayed as raw JSON so large integers retain every digit.';
 replay.onclick=async()=>{
  const data=current(),output=$('comparison-replay-result');replay.disabled=true;output.textContent='Replaying…';
  try{
   async function query(body){const response=await fetch('/query',{method:'POST',headers:{'Content-Type':'application/json'},body});const raw=await response.text();if(!response.ok)throw new Error(raw);return raw}
   await query(data.registration_request);
   output.textContent=await query(JSON.stringify({op:'call',object:data.object_name,method:'summary'}));
  }catch(error){output.textContent=String(error)}finally{replay.disabled=false}
 };
 return {state:()=>({dataset:index,selected,summary:current().summary,record:current().examples[selected]})};
}
