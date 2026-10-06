// Gaussian matching supplies canonical full-field paths to the wall tools.
import {q,padd,pscale,pmul,pathTensionBound} from './cp_wall_tools.mjs';
import {writeFileSync} from 'node:fs';
const x=[-1,2],square=pmul(x,x),S=pscale(square,'-1/9');
const shifted=padd(square,[-1]);
const potential=pscale(pmul(shifted,shifted),'1/4');
const heavyResidual=padd(S,pscale(square,'1/9'));
if(heavyResidual.some(a=>q(a).cmp(0)!==0))throw Error('Gaussian valley residual');
const bound=pathTensionBound(potential,[x,S]);
if(bound.tension_upper_squared.toString()!=='3952/3645')throw Error('Gaussian path bound');
const result={
  action:'V=(x^2-1)^2/4+9(S+x^2/9)^2/2; canonical x,S',
  global_minima:[['-1','-1/9'],['1','-1/9']],
  exact_global_minimum_reason:'Both nonnegative squares vanish precisely at the two listed points.',
  CP:'x->-x, S->S',gaussian_path_bound:bound,
  rigorous_tension_lower_squared:'8/9',rigorous_tension_upper_squared:'3952/3645',
  sandwich:'sigma_canonical_EFT <= sigma_full_Gaussian_UV <= sigma_Gaussian_valley',
  proof:'Every full static profile has energy at least that of its projected canonical x profile. The Gaussian valley is an admissible full canonical path; its energy gives an upper bound.',
  scope:'Exact dimensionless two-field example with proved global minima. No tension, CP sign selection, thermal history or wall network is assigned to the quark flavor benchmark.'
};
writeFileSync(new URL('../../receipts/flavor_cosmology/gaussian_wall_bridge.json',import.meta.url),JSON.stringify(result,null,2)+'\n');
console.log(JSON.stringify({lower_squared:result.rigorous_tension_lower_squared,upper_squared:result.rigorous_tension_upper_squared}));
