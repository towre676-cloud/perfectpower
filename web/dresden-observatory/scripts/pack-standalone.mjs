/** Embed the static bundle and attributed source assets into one offline HTML. */
import fs from 'node:fs';
import path from 'node:path';
const root=path.resolve('dist/standalone');let html=fs.readFileSync(path.join(root,'index.html'),'utf8');
const script=html.match(/<script[^>]*src="([^"]+)"[^>]*><\/script>/);
if(!script)throw Error('Static build is missing its entrypoint');let js=fs.readFileSync(path.resolve(root,script[1]),'utf8');
const assets={};for(const [name,mime]of [['page46.webp','image/webp'],['page24.webp','image/webp'],['eclipse_figure1.jpg','image/jpeg'],['eclipse_figure8.jpg','image/jpeg'],['Dresden_Numerical_Monograph.pdf','application/pdf'],['DresdenCalendar.lean','text/plain'],['dresden-lean-axioms.log','text/plain'],['dresden-lean-proof-status.json','application/json']])assets['/sources/'+name]='data:'+mime+';base64,'+fs.readFileSync(path.join(root,'sources',name)).toString('base64');
for(const [url,data]of Object.entries(assets))js=js.replaceAll(url,data);
// Escape closing script tags embedded in strings; preserve module execution.
html=html.replace(script[0],()=>'<script type="module">'+js.replaceAll('</script','<\\/script')+'</script>');
html=html.replace(/<link[^>]*rel="stylesheet"[^>]*>/g,tag=>{const href=tag.match(/href="([^"]+)"/)?.[1];if(!href)throw Error('Missing stylesheet');return '<style>'+fs.readFileSync(path.resolve(root,href),'utf8').replaceAll('</style','<\\/style')+'</style>';});
const icon='data:image/svg+xml;base64,'+fs.readFileSync('public/favicon.svg').toString('base64');html=html.replace('href="/favicon.svg"',`href="${icon}"`);
html=html.replace(/<link[^>]*rel="modulepreload"[^>]*>/g,'');
fs.mkdirSync('outputs',{recursive:true});fs.writeFileSync('outputs/Dresden_Codex_Observatory.html',html);console.log(JSON.stringify({output:path.resolve('outputs/Dresden_Codex_Observatory.html'),bytes:Buffer.byteLength(html)}));
