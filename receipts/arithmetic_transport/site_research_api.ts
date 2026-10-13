import bundled from '@/lib/research-feed.json';
const url='https://raw.githubusercontent.com/towre676-cloud/perfectpower/main/data/explorer_live.json';
let cached:Record<string,unknown>|null=null,checked=0;
async function decode(raw:string,status:string){
 if(raw.length>1000000)throw Error('Research feed exceeds the supported size');
 const envelope=JSON.parse(raw);
 if(envelope.schema!=='pp-explorer-live/1'||typeof envelope.payload_json!=='string')throw Error('Unknown research feed');
 const digest=Array.from(new Uint8Array(await crypto.subtle.digest('SHA-256',new TextEncoder().encode(envelope.payload_json))),x=>x.toString(16).padStart(2,'0')).join('');
 if(digest!==envelope.payload_sha256)throw Error('Research feed digest mismatch');
 const payload=JSON.parse(envelope.payload_json);
 if(!Array.isArray(payload.applications))throw Error('Application records required');
 const population=payload.arithmetic_transport?.result?.exact_population_32;
 if(population&&typeof population.count==='number'&&!Number.isSafeInteger(population.count))throw Error('Unsafe legacy integer encoding; use exact decimal strings');
 return {...payload,status,source_parent:envelope.source_parent,payload_sha256:digest};
}
export async function GET(){
 if(cached&&Date.now()-checked<60000)return Response.json(cached,{headers:{'Cache-Control':'private, max-age=30'}});
 try{
  const response=await fetch(url+'?refresh='+Math.floor(Date.now()/60000),{signal:AbortSignal.timeout(8000),headers:{'Cache-Control':'no-cache'}});
  if(!response.ok)throw Error('Public feed returned '+response.status);
  cached=await decode(await response.text(),'live');checked=Date.now();
 }catch(error){
  cached=cached?{...cached,status:'cached'}:await decode(JSON.stringify(bundled),'bundled');
  cached={...cached,error:String(error)};checked=Date.now();
 }
 return Response.json(cached,{headers:{'Cache-Control':'private, max-age=30','X-Content-Type-Options':'nosniff'}});
}
