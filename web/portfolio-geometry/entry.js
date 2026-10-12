import {mountPortfolioGeometry} from '../../desktop/explorer/portfolio_geometry.js';
const host=document.querySelector('#geometry-observatory'),status=document.querySelector('#geometry-status');
(async()=>{
 try{
  const response=await fetch('data.json',{cache:'no-cache'});if(!response.ok)throw Error('The retained geometry data could not be loaded');const data=await response.json();
  const view=mountPortfolioGeometry(host,data.model,{mode:'retained'});
  function show(){const result=data.results[document.querySelector('#geometry-case').value];view.update(result.specification.resources,result);status.textContent=`Retained exact engine result · ${BigInt(result.summary.count).toLocaleString()} original feasible portfolios · global best ${result.summary.optimization.maximum} · ${result.conditional?result.conditional.prefix.length+' fixed original decisions':'original resource limits'}`;}
  document.querySelector('#geometry-case').onchange=show;show();
  document.querySelector('#geometry-source').textContent=data.model.source_sha256;
  window.addEventListener('pagehide',()=>view.dispose(),{once:true});
 }catch(error){status.textContent=error.message;}
})();
