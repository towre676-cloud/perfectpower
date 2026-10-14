(function(root){'use strict';
const table=[[0,1,2,3],[1,0,7,14],[2,15,0,5],[3,6,13,0]];
function mul(a,b){const x=table[a%4][b%4];return((Math.floor(a/4)+Math.floor(b/4)+Math.floor(x/4))%4)*4+x%4;}
function gcd(a,b){while(b){const x=a%b;a=b;b=x;}return a;}
function normalize(n,d){const g=gcd(n,d);return[n/g,d/g];}
function build(spec){const modes=spec.modes,k=modes.length,L=modes.reduce((a,m)=>a+m.quota,0);if(k<1||k>6||L>48)throw Error('Browser supports 1–6 modes and at most 48 moves');
 const raw=String(spec.start).split('/'),start=normalize(BigInt(raw[0]),BigInt(raw[1]||1)),cap=BigInt(spec.height_cap),integral=spec.integral!==false;
 const controller=spec.controller||{initial:0,accepting:[0],transitions:[modes.map(()=>0)]},accept=new Set(controller.accepting);
 const allowed=v=>(!integral||v[1]===1n)&&v[0]<=cap&&v[1]<=cap;
 const key=(c,q)=>c.join(',')+'|'+q,zero=modes.map(()=>0),id=key(zero,controller.initial),rootNode={id,c:zero,q:controller.initial,value:start,edges:[],count:0n,hist:new Map()};
 const nodes=new Map([[id,rootNode]]),layers=[[rootNode]];
 if(!allowed(start))return{root:rootNode,modes,L,nodes,cap};
 for(let depth=0;depth<L;depth++){const next=[];for(const n of layers.at(-1)){for(let j=0;j<k;j++){const m=modes[j],q=controller.transitions[n.q][j];if(n.c[j]>=m.quota||q===null)continue;
 const v=normalize(n.value[0]*BigInt(m.direction===1?m.prime:1),n.value[1]*BigInt(m.direction===1?1:m.prime));if(!allowed(v))continue;
 const c=n.c.slice();c[j]++;const childId=key(c,q);let child=nodes.get(childId);if(!child){if(nodes.size>=50000)throw Error('Exact browser state budget reached');child={id:childId,c,q,value:v,edges:[],count:0n,hist:new Map()};nodes.set(childId,child);next.push(child);}n.edges.push([j,child]);}}
 layers.push(next);}
 for(const layer of layers.slice().reverse())for(const n of layer){if(n.c.every((x,j)=>x===modes[j].quota)){n.count=accept.has(n.q)?1n:0n;if(n.count)n.hist.set(0,1n);}else for(const[j,c]of n.edges){n.count+=c.count;for(const[g,count]of c.hist){const product=mul(g,modes[j].axis);n.hist.set(product,(n.hist.get(product)||0n)+count);}}}
 return{root:rootNode,modes,L,nodes,cap};}
function unrank(model,index){index=BigInt(index);if(index<0n||index>=model.root.count)throw Error('Rank outside the complete population');let n=model.root;const path=[];while(path.length<model.L){let found=false;for(const[j,c]of n.edges){if(index<c.count){path.push(j);n=c;found=true;break;}index-=c.count;}if(!found)throw Error('Invalid suffix counts');}return path;}
function amplitude(hist){const entries=[];let norm=0n;for(let a=0;a<4;a++){const re=(hist.get(a)||0n)-(hist.get(8+a)||0n),im=(hist.get(4+a)||0n)-(hist.get(12+a)||0n);if(re||im)entries.push({axis:a,re,im});norm+=re*re+im*im;}return{entries,norm};}
const api={build,unrank,mul,amplitude};if(typeof module!=='undefined'&&module.exports)module.exports=api;else root.ArithmeticModes=api;
})(typeof globalThis!=='undefined'?globalThis:this);
