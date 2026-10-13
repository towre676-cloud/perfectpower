(function(root){'use strict';
function build(p,q,d){if(![2,3,5,7].includes(p)||![2,3,5,7].includes(q)||p>=q||!Number.isInteger(d)||d<1||d>64)throw Error('Unsupported prime pair or power');
 const P=Array.from({length:d+1},(_,i)=>BigInt(p)**BigInt(i)),Q=Array.from({length:d+1},(_,i)=>BigInt(q)**BigInt(i));
 const suffix=Array.from({length:d+1},()=>Array(d+1).fill(0n));
 for(let u=d;u>=0;u--)for(let v=d;v>=0;v--){if(P[u]>Q[v])continue;suffix[u][v]=(u===d&&v===d)?1n:(u<d?suffix[u+1][v]:0n)+(v<d?suffix[u][v+1]:0n);}
 let total=1n;for(let k=1;k<=d;k++)total=total*BigInt(d+k)/BigInt(k);
 return {p,q,d,P,Q,suffix,count:suffix[0][0],total,fraction:Number(suffix[0][0]*1000000000000n/total)/1e12};}
function randomBelow(n){if(n<1n)throw Error('Empty population');const bits=n.toString(2).length,bytes=Math.ceil(bits/8);let x;do{const data=new Uint8Array(bytes);crypto.getRandomValues(data);data[0]&=(1<<((bits-1)%8+1))-1;x=0n;for(const b of data)x=(x<<8n)+BigInt(b);}while(x>=n);return x;}
function sample(model,draw=randomBelow){let u=0,v=0;const path=[[u,v]];while(u<model.d||v<model.d){const up=u<model.d?model.suffix[u+1][v]:0n,down=v<model.d?model.suffix[u][v+1]:0n;if(draw(up+down)<up)u++;else v++;path.push([u,v]);}return path;}
const api={build,sample,randomBelow};if(typeof module!=='undefined'&&module.exports)module.exports=api;else root.ArithmeticTransport=api;
})(typeof globalThis!=='undefined'?globalThis:this);
