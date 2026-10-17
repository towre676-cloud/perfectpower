import React from 'react';

// These identities describe the retained calculations. The ribbons, tower and
// simplex meshes remain illustrations; they are not inputs to these formulas.
export const MATH_VIEWS = {
 bridge: {kind:'bridge', title:'The phase bridge', label:'Exact conductor map',
  caption:'384 primitive phases reach 8 Coxeter eigenphases, with 48 copies of each.',
  explanation:'Set q = exp(iπ/840) and ζ₃₀ = exp(2πi/30). Raising q to the 56th power gives ζ₃₀. On primitive conjugates this map reaches the eight primitive 30th-root phases, each 48 times. This is an exact phase map; it does not identify phase branches with E₈ roots.'},
 trace: {kind:'trace', title:'264 integrals become one', label:'Exact period identity · Re(s) > 1',
  caption:'Add all 264 phase branches. Their Mellin integrals reduce to one scaled period.',
  explanation:'Here Q = exp(iπ/221760), q = Q²⁶⁴, and Iₛ(z) is the normalized Mellin integral shown below. Expanding in powers of z, the sum over all 264 roots of unity removes every exponent that is not a multiple of 264. The result holds for Re(s) > 1. This full-fiber identity includes all 264 branches, not only the 240 primitive branches.'},
 raghava: {kind:'raghava', title:'Raghava’s angle identity', label:'Arcsine moment · |θ| < π/2',
  caption:'At θ = π/840 the entire infinite sum is exactly π²/352800.',
  explanation:'This is the first member of the arcsine moment family used by Raghava. Put t = 2 sin θ. More generally Mⱼ(2 sin θ) = 4ʲθ²ʲ/(2j)!, with eₖ(n) the coefficient of zᵏ in ∏ₐ₌₁ⁿ⁻¹(1 + z/a²). Refining the angle θ to θ/264 scales moment j by 264⁻²ʲ. It is the angle that is divided by 264; the sine argument t is not simply divided by 264.'},
 reciprocity: {kind:'reciprocity', title:'Two views of the same linear map', label:'Ordinary Frobenius reciprocity',
  caption:'Induction and restriction give an explicit linear bijection. The simplex mesh is illustrative.',
  explanation:'For n = 1680 dividing N = 443520, the retained finite linear category implements induction, restriction and this Hom-space bijection on actual phase-graded matrices. The source checks inverse maps and naturality. This is an ordinary linear correspondence; the animated nerve does not establish a higher categorical equivalence.'},
 cyclotomic: {kind:'cyclotomic', title:'The blue cyclotomic field', label:'Primitive 1680th roots',
  caption:'q generates a degree-384 cyclotomic field. The blue surface illustrates its phase count.',
  explanation:'The primitive root q = exp(iπ/840) has order 1680. Euler’s totient gives φ(1680) = 384, the degree of the full cyclotomic field over the rationals. The blue points illustrate the number of conjugates; their decorative spatial arrangement is not a field embedding.'},
 fiber: {kind:'fiber', title:'The refined phase fiber', label:'264 preimages · 240 primitive',
  caption:'The power map has 264 branches: 240 primitive and 24 of lower conductor.',
  explanation:'All solutions of z²⁶⁴ = q are zⱼ = Q exp(2πij/264), for 0 ≤ j < 264. Their exponents at conductor 443520 are 1 + 1680j. Exactly 240 of these integers are coprime to 443520; the remaining 24 have conductor 40320. The 240 primitive branches and the 240 E₈ roots are distinct collections.'},
 e8: {kind:'e8', title:'The E₈ integral balance', label:'Exact normalized Mellin value · weight 2',
  caption:'The 240 root directions and 8 Cartan directions contribute equal and opposite terms.',
  explanation:'For the retained E₈ adjoint Coxeter lift, the normalized Mellin trace separates into the root-permutation contribution +2π²/45 and Cartan contribution −2π²/45 at weight two. Their sum is exactly zero. The highlighted point follows the exact Coxeter successor; its 56 neighbors have inner product one with it.'}
};

export const CHAPTER_MATH = ['bridge','trace','raghava','reciprocity'];
export const NODE_MATH = {left:'cyclotomic',right:'e8',upper:'bridge',lower:'raghava',center:'fiber'};

const M=({children})=><math display="block" aria-hidden="true">{children}</math>;
const pi=<mi>π</mi>,theta=<mi>θ</mi>,q=<mi>q</mi>,Q=<mi>Q</mi>;
const power=(base,exponent)=><msup>{base}<mrow>{exponent}</mrow></msup>;
const exp=value=>power(<mi>e</mi>,value);
const fraction=(a,b)=><mfrac><mrow>{a}</mrow><mrow>{b}</mrow></mfrac>;
const binomial=<mrow><mo>(</mo><mfrac linethickness="0"><mrow><mn>2</mn><mi>n</mi></mrow><mi>n</mi></mfrac><mo>)</mo></mrow>;
const I=<msub><mi>I</mi><mi>s</mi></msub>;
const ind=<msub><mi mathvariant="normal">Ind</mi><mrow><msub><mi>C</mi><mi>n</mi></msub></mrow></msub>;
const res=<msub><mi mathvariant="normal">Res</mi><mrow><msub><mi>C</mi><mi>n</mi></msub></mrow></msub>;
const hom=letter=><msub><mi mathvariant="normal">Hom</mi><msub><mi>C</mi><mi>{letter}</mi></msub></msub>;

const LABELS={
 bridge:'q to the power 56 equals zeta 30; 384 equals 48 times 8.',
 trace:'The sum from j equals zero to 263 of I sub s of Q times exp of 2 pi i j over 264 equals 264 to the power 1 minus s times I sub s of q.',
 raghava:'The sum from n equals one to infinity of 2 sine theta to the power 2 n, divided by n squared times the binomial coefficient 2 n choose n, equals 2 theta squared.',
 reciprocity:'Hom over C N from induced V to W is isomorphic to Hom over C n from V to restricted W.',
 cyclotomic:'q equals exp of i pi over 840; Euler phi of 1680 equals 384.',
 fiber:'Q to the power 264 equals q; 264 equals 240 plus 24.',
 e8:'J sub 2 equals 2 pi squared over 45 minus 2 pi squared over 45 equals zero.'
};

export function MathIdentity({kind='bridge'}){
 let equation;
 if(kind==='bridge')equation=<><M>{power(q,<mn>56</mn>)}<mo>=</mo><msub><mi>ζ</mi><mn>30</mn></msub></M><M><mn>384</mn><mo>=</mo><mn>48</mn><mo>×</mo><mn>8</mn></M></>;
 if(kind==='cyclotomic')equation=<><M>{q}<mo>=</mo>{exp(fraction(<><mi>i</mi>{pi}</>,<mn>840</mn>))}</M><M><mi>φ</mi><mo>(</mo><mn>1680</mn><mo>)</mo><mo>=</mo><mn>384</mn></M></>;
 if(kind==='fiber')equation=<><M>{power(Q,<mn>264</mn>)}<mo>=</mo>{q}</M><M><mn>264</mn><mo>=</mo><mn>240</mn><mo>+</mo><mn>24</mn></M></>;
 if(kind==='trace')equation=<><M><munderover><mo>∑</mo><mrow><mi>j</mi><mo>=</mo><mn>0</mn></mrow><mn>263</mn></munderover>{I}<mo>(</mo>{Q}{exp(fraction(<><mn>2</mn>{pi}<mi>i</mi><mi>j</mi></>,<mn>264</mn>))}<mo>)</mo></M><M><mo>=</mo>{power(<mn>264</mn>,<><mn>1</mn><mo>−</mo><mi>s</mi></>)}{I}<mo>(</mo>{q}<mo>)</mo></M></>;
 if(kind==='raghava')equation=<><M><munderover><mo>∑</mo><mrow><mi>n</mi><mo>=</mo><mn>1</mn></mrow><mo>∞</mo></munderover>{fraction(power(<mrow><mo>(</mo><mn>2</mn><mi mathvariant="normal">sin</mi>{theta}<mo>)</mo></mrow>,<><mn>2</mn><mi>n</mi></>),<>{power(<mi>n</mi>,<mn>2</mn>)}{binomial}</>)}</M><M><mo>=</mo><mn>2</mn>{power(theta,<mn>2</mn>)}</M></>;
 if(kind==='reciprocity')equation=<><M>{hom('N')}<mo>(</mo>{ind}<mi>V</mi><mo>,</mo><mi>W</mi><mo>)</mo></M><M><mo>≅</mo>{hom('n')}<mo>(</mo><mi>V</mi><mo>,</mo>{res}<mi>W</mi><mo>)</mo></M></>;
 if(kind==='e8')equation=<M><msub><mi>J</mi><mn>2</mn></msub><mo>=</mo>{fraction(<><mn>2</mn>{power(pi,<mn>2</mn>)}</>,<mn>45</mn>)}<mo>−</mo>{fraction(<><mn>2</mn>{power(pi,<mn>2</mn>)}</>,<mn>45</mn>)}<mo>=</mo><mn>0</mn></M>;
 return <div className="math-equation" data-identity={kind} role="math" aria-label={LABELS[kind]}>{equation}</div>;
}

export function MathDefinition({kind}){
 if(kind==='trace')return <div className="math-definition" role="math" aria-label="I sub s of z equals one over Gamma s times the integral from zero to one of z times negative log x to the power s minus one over one minus z x, d x; it equals the polylogarithm Li sub s of z."><M>{I}<mo>(</mo><mi>z</mi><mo>)</mo><mo>=</mo>{fraction(<mn>1</mn>,<><mi>Γ</mi><mo>(</mo><mi>s</mi><mo>)</mo></>)}</M><M><msubsup><mo>∫</mo><mn>0</mn><mn>1</mn></msubsup>{fraction(<><mi>z</mi>{power(<mrow><mo>(</mo><mo>−</mo><mi mathvariant="normal">log</mi><mi>x</mi><mo>)</mo></mrow>,<><mi>s</mi><mo>−</mo><mn>1</mn></>)}</>,<><mn>1</mn><mo>−</mo><mi>z</mi><mi>x</mi></>)}<mi mathvariant="normal">d</mi><mi>x</mi></M><M><mo>=</mo><msub><mi mathvariant="normal">Li</mi><mi>s</mi></msub><mo>(</mo><mi>z</mi><mo>)</mo></M></div>;
 if(kind==='raghava')return <div className="math-definition" role="math" aria-label="Moment j at 2 sine theta equals 4 to the j theta to the 2 j over factorial 2 j."><M><msub><mi>M</mi><mi>j</mi></msub><mo>(</mo><mn>2</mn><mi mathvariant="normal">sin</mi>{theta}<mo>)</mo><mo>=</mo>{fraction(<>{power(<mn>4</mn>,<mi>j</mi>)}{power(theta,<><mn>2</mn><mi>j</mi></>)}</>,<><mo>(</mo><mn>2</mn><mi>j</mi><mo>)</mo><mo>!</mo></>)}</M></div>;
 return null;
}

export function RootReadout({root}){
 return <div className="root-coordinates"><span>α =</span><code>({root.doubled_root.map(n=>n/2).join(', ')})</code><span>‖α‖² = 2</span></div>;
}
