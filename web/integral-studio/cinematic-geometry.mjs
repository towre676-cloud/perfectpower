/** Display embeddings of finite arithmetic objects; interpolation adds no new roots. */
export function gcd(a,b){while(b)[a,b]=[b,a%b];return Math.abs(a);}
export function chi5(n){const r=((n%5)+5)%5;return r===0?0:r===1||r===4?1:-1;}
export const PHASE30=Object.freeze([1,7,11,13,17,19,23,29]);
export const EMBEDDING_ROTATIONS=Object.freeze({domain:[.6,.3,-.2],fiber:[-.54,.36,.21],bridge:[.58,-.3,.22]});
export function orientPoint(point,kind='domain'){
 const [rx,ry,rz]=EMBEDDING_ROTATIONS[kind];let[x,y,z]=point;
 // Three.js Euler XYZ is R_x R_y R_z, applied to a column vector.
 [x,y]=[Math.cos(rz)*x-Math.sin(rz)*y,Math.sin(rz)*x+Math.cos(rz)*y];
 [x,z]=[Math.cos(ry)*x+Math.sin(ry)*z,-Math.sin(ry)*x+Math.cos(ry)*z];
 [y,z]=[Math.cos(rx)*y-Math.sin(rx)*z,Math.sin(rx)*y+Math.cos(rx)*z];
 return[x,y,z];
}
export function characterEmbedding(theta,{radius=1.42,tube=.43,character=7}={}){
 const r=radius+tube*Math.cos(character*theta);
 return [r*Math.cos(theta),r*Math.sin(theta),tube*Math.sin(character*theta)];
}
export function primitive1680(){return Array.from({length:1680},(_,a)=>a).filter(a=>gcd(a,1680)===1).map(a=>({a,phase:a%30,sector:chi5(a),theta:2*Math.PI*a/1680,position:characterEmbedding(2*Math.PI*a/1680)}));}
export function phaseFiber264(){return Array.from({length:264},(_,j)=>{const exponent=1+1680*j,theta=2*Math.PI*exponent/443520;return{j,exponent,primitive:gcd(exponent,443520)===1,theta,position:characterEmbedding(theta,{radius:1.24,tube:.37,character:11})};});}
export function eigenphases30(){return PHASE30.map(a=>({a,sector:chi5(a),theta:2*Math.PI*a/30,position:characterEmbedding(2*Math.PI*a/30,{radius:1.11,tube:.21,character:7})}));}
export function bezierPoint(p0,p1,p2,p3,t){const s=1-t;return p0.map((v,i)=>s*s*s*v+3*s*s*t*p1[i]+3*s*t*t*p2[i]+t*t*t*p3[i]);}
export function powerMapCurves(domain,target,positions,{count=64,mobile=false}={}){
 const selection=Array.from({length:Math.min(count,domain.length)},(_,i)=>domain[Math.floor(i*domain.length/Math.min(count,domain.length))]);
 return selection.map((source,i)=>{
  const dest=target.find(p=>p.a===source.phase);
  const start=orientPoint(source.position,'domain').map((v,j)=>v+positions.cyclotomic[j]);
  const end=orientPoint(dest.position,'bridge').map((v,j)=>v+positions.bridge[j]);
  const lane=(source.a%11)/11-.5;
  const p1=[start[0]*.6,start[1]+.8+lane*.3,start[2]+.5+lane*1.1];
  const p2=[end[0]-.7-lane*.5,end[1]-.3,end[2]+.8+lane];
  return{source:source.a,target:dest.a,sector:source.sector,control:[start,p1,p2,end],points:Array.from({length:49},(_,j)=>bezierPoint(start,p1,p2,end,j/48))};
 });
}
export function e8Edges(roots){const edges=[];for(const root of roots)for(const neighbor of root.neighbors)if(neighbor>root.id)edges.push([root.id,neighbor]);return edges;}
export function compositionPositions(portrait=false){return portrait?{
 cyclotomic:[-1.7,2.0,-.75],e8:[1.7,-1.45,-.55],bridge:[.65,4.85,-1.05],fiber:[0,.45,.8],integral:[-.9,-3.85,-.6]
 }:{cyclotomic:[-4.35,.05,0],e8:[4.3,-.03,0],bridge:[0,2.65,-.5],fiber:[0,.1,.75],integral:[0,-2.25,.1]};}
