/* Shared app navigation and live public research consumption. No private inputs are sent. */
(function(){'use strict';
const base='https://raw.githubusercontent.com/towre676-cloud/perfectpower/main/data/';
const product=document.currentScript?.dataset.product||'perfectpower';let known={},busy=false,integralFocused=false;
const sha=async raw=>Array.from(new Uint8Array(await crypto.subtle.digest('SHA-256',new TextEncoder().encode(raw))),x=>x.toString(16).padStart(2,'0')).join('');
function node(tag,text){const n=document.createElement(tag);if(text)n.textContent=text;return n;}
let host=document.getElementById('our-apps-live');if(!host){host=node('section');host.id='our-apps-live';document.body.append(host);}
host.style.cssText='margin:24px auto;padding:18px 22px;max-width:1120px;border:1px solid #9aafa744;border-radius:14px;font:13px/1.6 system-ui;background:#eef3ee;color:#244c43;';
const top=node('div');top.style.cssText='display:flex;gap:18px;align-items:center;justify-content:space-between;flex-wrap:wrap';
const title=node('strong','Your app collection'),status=node('span','Checking research updates…'),link=node('a','All apps & downloads →');link.href='https://our-apps.towre676.chatgpt.site';link.style.color='#28634d';top.append(title,link);host.append(top,status);
const links=node('div');links.style.cssText='display:flex;gap:14px;flex-wrap:wrap;margin-top:10px';host.append(links);
const research=node('div');host.append(research);
const detail=node('details'),summary=node('summary','What connects these apps?'),content=node('div');detail.append(summary,content);host.append(detail);
async function envelope(url){const response=await fetch(url,{cache:'no-store'});if(!response.ok)throw Error('Research update unavailable');const e=await response.json();if(typeof e.payload_json!=='string'||await sha(e.payload_json)!==e.payload_sha256)throw Error('Research update did not match its digest');return {payload:JSON.parse(e.payload_json),digest:e.payload_sha256,source_parent:e.source_parent};}
async function refresh(){if(busy)return;busy=true;try{
 const response=await fetch(base+'app_ecosystem.json',{cache:'no-store'});if(!response.ok)throw Error('App index unavailable');const registry=await response.json();if(registry.schema!=='our-apps/1')throw Error('Unsupported app index');
 links.replaceChildren();for(const p of registry.products){const a=node('a',p.name);a.href=p.open;a.style.color='#28634d';links.append(a);}
 const current=registry.products.find(p=>p.id===product)||registry.products[0];content.replaceChildren();for(const p of registry.products){const para=node('p');para.append(node('strong',p.name+' — '),document.createTextNode(p.purpose+'. '+p.how));content.append(para);}
 const updates={};for(const source of current.sources){try{updates[source]=await envelope(registry.upstreams[source].feed);}catch(error){updates[source]={unavailable:true};}}
 research.replaceChildren();
 const integrals=updates.perfectpower?.payload.period_bridge;
 if(product==='perfectpower'&&integrals?.result){
  const data=integrals.result,card=node('section');card.id='integral-families';card.style.cssText='margin:14px 0;padding:16px;border-radius:12px;background:#fff';
  card.append(node('strong',data.title||'Integral families'),node('p',data.description||'Explore exact relationships between integral families.'));
  const highlights=node('div');highlights.style.cssText='display:flex;gap:20px;flex-wrap:wrap';
  for(const item of (data.highlights||[]).slice(0,3)){const value=node('div');value.append(node('strong',String(item.value??'')),node('div',item.label||''));highlights.append(value);}
  card.append(highlights);const explore=node('a','Explore the integral families →');explore.href=integrals.url||'https://perfectpower-explorer-download.towre676.chatgpt.site/integrals/';explore.style.cssText='display:inline-block;margin:12px 18px 0 0;color:#28634d';card.append(explore);const more=node('a','Read the mathematics →');more.href=integrals.monograph;more.style.cssText='display:inline-block;margin-top:12px;color:#28634d';card.append(more);research.append(card);
  if(!integralFocused&&location.hash==='#integral-families'){integralFocused=true;card.scrollIntoView({block:'start'});}
 }
 const changed=Object.entries(updates).some(([key,value])=>known[key]&&value.digest&&known[key]!==value.digest);
 const ready=Object.values(updates).filter(x=>x.digest).length;
 status.textContent=ready===current.sources.length?(changed?'New research is ready · refreshed from the source':'Connected to published research'):'Some sources are offline · saved app content stays available';
 for(const [key,value] of Object.entries(updates))if(value.digest)known[key]=value.digest;
 if(product==='nfl'||product==='perfectpower'){
  try{const r=await fetch('https://raw.githubusercontent.com/towre676-cloud/perfectpower/main/web/shared/finite-counter.js',{cache:'no-store'});if(!r.ok)throw Error('Counter unavailable');const source=await r.text();const counter={source,sha256:await sha(source)};
   if(globalThis.__ourCounterSHA!==counter.sha256){
    const script=document.createElement('script'),url=URL.createObjectURL(new Blob([counter.source],{type:'application/javascript'}));
    await new Promise((resolve,reject)=>{script.onload=resolve;script.onerror=reject;script.src=url;document.head.append(script);});URL.revokeObjectURL(url);script.remove();
    if(typeof globalThis.PerfectPowerCounter?.countFactors!=='function'||typeof globalThis.PerfectPowerCounter?.countMasks!=='function')throw Error('Counter API unavailable');
    globalThis.__ourCounterSHA=counter.sha256;window.dispatchEvent(new CustomEvent('ecosystem:engine-updated',{detail:{product,sha256:counter.sha256}}));
   }
  }catch(error){status.textContent+=' · using the installed counting engine';}
 }
 globalThis.OurApps={registry,updates,refresh};window.dispatchEvent(new CustomEvent('ecosystem:update',{detail:{registry,updates,product,changed}}));
}catch(error){status.textContent='Offline · your app and saved work are still available';}finally{busy=false;}}
refresh();setInterval(refresh,300000);window.addEventListener('online',refresh);
})();
