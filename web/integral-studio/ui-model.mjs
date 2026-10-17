export const DEFAULT_COEFFICIENTS = [.7,.8,.13,.02];
export const VIEWS = [
 {id:'integral',name:'The integral',mark:'∫',title:'Watch the area become a number',text:'The curve is the actual squared response, written in the angle θ so the endpoint weight disappears. Four quadratic zeros mark the possible logarithmic singularities; their contributions can cancel in special mixtures.',formula:'\\mathcal E=\\int_0^\\pi [aA(\\cos\\theta)+bK(\\cos\\theta)+cP(\\cos\\theta)+dR(\\cos\\theta)]^2\\,d\\theta'},
 {id:'spectrum',name:'The spectrum',mark:'◉',title:'Eight phases. Two golden sectors.',text:'The ring shows the eight primitive thirtieth-root eigenphases. Gold and cyan separate the quadratic character modulo five. The neutral cloud is a projection of the 240 E₈ roots.',formula:'\\det(I-zC)=\\Phi_{30}(z),\\qquad G=I+C^6+C^{24},\\quad G^2=G+I'},
 {id:'fourier',name:'The frequencies',mark:'≋',title:'Arithmetic becomes a Fourier signal',text:'Each stem is an actual Fourier coefficient of a spectral logarithm. The character changes signs by residues modulo five; the same coefficients give the zeta and L-value identities.',formula:'A(\\cos\\theta)=-\\sum_{n\\ge1}\\frac{c_{30}(n)}n\\cos n\\theta,\\quad K(\\cos\\theta)=-\\sum_{n\\ge1}\\frac{\\sqrt5\\,\\chi_5(n)c_6(n)}n\\cos n\\theta'},
 {id:'energy',name:'The energy',mark:'◇',title:'One integral is a quadratic geometry',text:'The translucent ellipsoid is a three-dimensional slice of the exact four-variable energy. Its axes use basis-norm-scaled a, b and c coordinates; d is held fixed.',formula:'\\mathcal E(\\mathbf t)=\\mathbf t^{\\mathsf T}\\Gamma\\mathbf t,\\qquad\\Gamma_{ij}=\\int_{-1}^{1}\\frac{f_i(x)f_j(x)}{\\sqrt{1-x^2}}\\,dx'}
];
export const PRESETS = [
 {id:'all',name:'All four voices',coefficients:DEFAULT_COEFFICIENTS,view:'integral',note:'The full master integral, with all four modes present.'},
 {id:'golden',name:'The π³ identity',coefficients:[0,1,0,0],view:'integral',note:'Only the golden difference remains. Its squared integral is exactly 8π³/15.',formula:'\\mathcal E(0,1,0,0)=\\frac{8\\pi^3}{15}'},
 {id:'zeta5',name:'Find ζ(5)',coefficients:[1,0,.3,0],view:'fourier',note:'The ac cross term isolates ζ(5). The whole energy also includes its two diagonal terms.',formula:'\\Gamma_{AP}=\\frac{832\\pi}{1125}\\zeta(5)'},
 {id:'zeta7',name:'Find ζ(7)',coefficients:[1,0,0,.05],view:'energy',note:'The ad cross term isolates ζ(7) through the next Bernoulli selector.',formula:'\\Gamma_{AR}=\\frac{157976\\pi}{28125}\\zeta(7)'},
 {id:'L5',name:'Find L(5, χ₅)',coefficients:[0,1,.3,0],view:'spectrum',note:'The bc cross term selects the quadratic Dirichlet character modulo five.',formula:'\\Gamma_{KP}=\\frac{41\\pi\\sqrt5}{54}L(5,\\chi_5)'},
 {id:'L7',name:'Find L(7, χ₅)',coefficients:[0,1,0,.05],view:'fourier',note:'The bd cross term is the seventh-order character evaluation.',formula:'\\Gamma_{KR}=\\frac{1825\\pi\\sqrt5}{324}L(7,\\chi_5)'},
 {id:'orthogonal',name:'The orthogonal partner',coefficients:[3,10,0,0],view:'energy',note:'A and 3A+10K have zero inner product. The partner itself has positive squared energy.',formula:'\\langle A,3A+10K\\rangle=0,\\quad\\|3A+10K\\|^2=\\frac{776\\pi^3}{15}'}
];
export const TOUR = [
 {view:'integral',preset:'all',title:'Begin with one integral',text:'Four simple controls mix two spectral logarithms and two arcsine modes. The highlighted area accumulates to the energy shown at right.'},
 {view:'spectrum',preset:'golden',title:'Read the golden split',text:'Tap an eigenphase. The signs come from its residue modulo five, while the 240-root cloud retains its separate geometric meaning.'},
 {view:'fourier',preset:'zeta5',title:'Hear the arithmetic frequencies',text:'The first 32 Fourier coefficients show where the sums acquire their arithmetic filters. Polynomial cancellation isolates the fifth-order zeta value.'},
 {view:'energy',preset:'zeta7',title:'See the cross terms',text:'A different arcsine selector isolates ζ(7). The integral remains one positive quadratic energy as the coefficient point moves.'},
 {view:'spectrum',preset:'L5',title:'Change the character',text:'The logarithmic ratio retains the difference between golden sectors. The cross terms now select Dirichlet L-values.'},
 {view:'energy',preset:'orthogonal',title:'Finish with exact orthogonality',text:'The two nonzero functions A and 3A+10K are orthogonal. Their cancellation is a statement about an inner product, not zero total energy.'}
];
export function cleanCoefficients(value){return Array.isArray(value)&&value.length===4&&value.every(x=>typeof x==='number'&&Number.isFinite(x)&&Math.abs(x)<=100)?value:[...DEFAULT_COEFFICIENTS];}
export function decodeState(search=''){try{const q=new URLSearchParams(search);const c=q.get('mix');return{coefficients:cleanCoefficients(c?JSON.parse(c):null),view:VIEWS.some(v=>v.id===q.get('view'))?q.get('view'):'integral',shared:!!c};}catch{return{coefficients:[...DEFAULT_COEFFICIENTS],view:'integral',shared:false};}}
export function shareState(coefficients,view){const p=new URLSearchParams({mix:JSON.stringify(cleanCoefficients(coefficients)),view:VIEWS.some(v=>v.id===view)?view:'integral'});return'?'+p.toString();}
