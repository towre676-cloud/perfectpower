/* Execute real UI logic with a minimal DOM fixture. This is not browser QA. */
'use strict';
const assert=require('node:assert/strict'),fs=require('node:fs'),path=require('node:path'),vm=require('node:vm'),crypto=require('node:crypto');
const root=path.resolve(__dirname,'../..'),dir=path.join(root,'web/integral-families'),registry=new Map(),nodes=new Set(),resizers=[];let width=800,height=510;
class Element{
 constructor(tag,attrs={},owner=null){this.tag=tag;this.attrs=attrs;this.owner=owner;this.dataset={};for(const [k,v] of Object.entries(attrs))if(k.startsWith('data-'))this.dataset[k.slice(5).replace(/-([a-z])/g,(_,x)=>x.toUpperCase())]=v;this.value=attrs.value||'';this.checked='checked' in attrs;this.hidden='hidden' in attrs;this.events={};this.classList={add(){}};this._html='';this.textContent='';this.viewBox={baseVal:{width:800,height:510}};nodes.add(this);if(attrs.id)registry.set(attrs.id,this);}
 set innerHTML(x){for(const n of [...nodes])if(n.owner===this){nodes.delete(n);if(n.attrs.id)registry.delete(n.attrs.id);}this._html=x;parse(x,this);}
 get innerHTML(){return this._html;}
 get clientWidth(){return width;}get clientHeight(){return height;}
 setAttribute(k,v){this.attrs[k]=String(v);if(k==='viewBox'){const p=String(v).split(' ').map(Number);this.viewBox.baseVal={width:p[2],height:p[3]};}}
 addEventListener(name,fn){this.events[name]=fn;}
 setPointerCapture(){} getBoundingClientRect(){return {left:0,top:0,width,height};}
}
function parse(html,owner=null){for(const m of html.matchAll(/<([a-z][\w:-]*)\b([^>]*)>/gi)){const attrs={};for(const a of m[2].matchAll(/([\w:-]+)(?:="([^"]*)")?/g))attrs[a[1]]=a[2]??'';if(attrs.id||Object.keys(attrs).some(k=>k.startsWith('data-')))new Element(m[1],attrs,owner);}}
parse(fs.readFileSync(path.join(dir,'index.html'),'utf8'));
const document={getElementById:id=>registry.get(id)||null,querySelectorAll:selector=>{const key=selector.match(/^\[([^\]]+)\]$/)?.[1];return [...nodes].filter(n=>key in n.attrs);},addEventListener(){},hidden:false};
const context={console,document,location:{hash:''},history:{replaceState(){}},TextEncoder,crypto:crypto.webcrypto,fetch:async()=>({ok:true,json:async()=>JSON.parse(fs.readFileSync(path.join(dir,'atlas-data.json'),'utf8'))}),ResizeObserver:class{constructor(fn){resizers.push(fn);}observe(){this.fn?.();}},requestAnimationFrame:()=>1,cancelAnimationFrame(){},addEventListener(){},setTimeout,URL,Blob};
context.IntegralEngine=require(path.join(dir,'engine.js'));context.AtlasModel=require(path.join(dir,'atlas-model.js'));vm.createContext(context);vm.runInContext(fs.readFileSync(path.join(dir,'atlas.js'),'utf8'),context);
const get=id=>{const e=registry.get(id);assert(e,`missing ${id}`);return e;};
const event=(id,name,value)=>{const e=get(id);if(value!==undefined)e.value=String(value);assert(e.events[name],`unbound ${id}.${name}`);e.events[name]({target:e});};
const chapter=name=>{const b=[...nodes].find(n=>n.dataset.chapter===name);assert(b);b.onclick();};
function checkPlot(){const html=get('atlas-plot').innerHTML;assert(!/NaN|Infinity|undefined/.test(html));assert(html.includes('<title'));assert(html.includes('<desc'));return html;}
function savePlot(name){if(!process.argv[2])return;const out=path.resolve(process.argv[2]);fs.mkdirSync(out,{recursive:true});const svg=`<svg xmlns="http://www.w3.org/2000/svg" width="${width}" height="${height}" viewBox="0 0 ${width} ${height}"><style>text{font:12px sans-serif;fill:#97aeb8}.plot-label{font-size:10px}.plot-value{font:38px serif;fill:#e5eee9}.axis-title{font-size:11px;fill:#c7d7d9}.point-label{fill:#e8bb75;font-size:11px}</style><rect width="100%" height="100%" fill="#08141e"/>${checkPlot()}</svg>`;fs.writeFileSync(path.join(out,name+'.svg'),svg);}
(async()=>{for(let i=0;i<100&&!get('data-status').textContent.includes('verified');i++)await new Promise(r=>setTimeout(r,5));assert(get('data-status').textContent.includes('verified'));assert.equal((checkPlot().match(/data-root=/g)||[]).length,240);savePlot('e8-desktop');event('orbit-choice','change',5);assert(get('chapter-result').innerHTML.includes('Orbit 6'));const result=get('chapter-result').innerHTML;for(let k=0;k<30;k++)get('advance').onclick?.();
 // Listener, rather than onclick property, owns the step action.
 for(let k=0;k<30;k++)event('advance','click');assert.equal(get('chapter-result').innerHTML,result);
 event('depth','input',75);checkPlot();savePlot('e8-depth');
 const stage=get('atlas-plot');stage.events.pointerdown({clientX:100,clientY:100,pointerId:1});stage.events.pointermove({clientX:180,clientY:140,pointerId:1});stage.events.pointerup({clientX:180,clientY:140,pointerId:1});checkPlot();
 chapter('phase');event('power','change',264);assert(get('chapter-result').innerHTML.includes('1 image'));checkPlot();event('branch','input',4);const primitive=get('primitive');primitive.checked=true;primitive.events.change({target:primitive});assert(get('chapter-result').innerHTML.includes('excluded by the filter'));savePlot('phase-collapse');event('power','change',1);savePlot('phase-branches');
 chapter('raghava');event('angle','change',221760);event('order','input',8);checkPlot();savePlot('raghava');
 chapter('mellin');assert(get('chapter-result').innerHTML.includes('exactly'));savePlot('mellin-e8');event('family','change','B');event('target','change',6);assert(get('chapter-result').innerHTML.includes('exactly'));event('weight','input',3.75);assert(!get('chapter-result').innerHTML.includes('exactly'));const density=[...nodes].find(n=>n.dataset.view==='density');density.onclick();checkPlot();savePlot('density');
 let responsiveDraws=0;for(const size of [284,360,640,1100]){width=size;height=size<400?370:510;for(const c of ['e8','phase','raghava','mellin']){chapter(c);for(const resize of resizers)resize();checkPlot();responsiveDraws++;savePlot(c+'-'+size);}}
 console.log(JSON.stringify({schema:'pp-integral-atlas-ui-checks/1',chapters:4,responsive_draws:responsiveDraws,root_selection:true,coxeter_cycle:true,drag_rotation:true,phase_filter:true,exact_zero_controls:true,scope:'Executed shipped UI JavaScript with a minimal DOM fixture; not browser layout QA.',passed:true}));
})().catch(e=>{console.error(e);process.exitCode=1;});
