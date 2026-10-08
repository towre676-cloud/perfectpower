"""Render the source monograph. Optional dependencies: reportlab, matplotlib.

Run: python python/render_polynomial_monograph.py --output /path/report.pdf
Core computational modules do not import this document renderer.
"""
import argparse
from pathlib import Path
import re
import textwrap
from html import escape
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from reportlab.lib import colors
from reportlab.lib.styles import ParagraphStyle
from reportlab.lib.enums import TA_CENTER
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.platypus import (SimpleDocTemplate, Paragraph, Spacer, PageBreak,
                                Image, Preformatted, Table, TableStyle, KeepTogether)


def render(source,output,*,edition='polynomial'):
    editions={
        'torsionpell':{
            'title':'Complete relations with torsion',
            'subtitle':'Actual elliptic subgroup indices<br/>and the full Pell-7 family',
            'description':'Injective finite torsion coordinates and complete integer kernels remove the free-only index restriction. Strict inverse-unit descent gives every Pell-7 solution and its unique address.',
            'metrics':[('56','independent coordinate models'),('7,000','exact relation checks'),('2','complete Pell seed orbits')],
            'scope':'Witnessed subgroup coordinates, exact finite torsion injection and Smith replay; all-solutions Pell paper proof. No new Lean theorem or global Mordell rank claim.',
            'running':'Torsion-aware relation lattices and complete Pell descent',
        },
        'mordelltwodescent':{
            'title':'Two-descent and Brainpool primality',
            'subtitle':'Mordell rank bounds, maximal cubic orders<br/>and a complete ECPP chain',
            'description':'General cubic-field descent yields every frontier upper bound, corrects eleven rank records, and exports exact quartic maps and integral-order arithmetic.',
            'metrics':[('457','descent upper bounds'),('289','ranks determined'),('15','Brainpool ECPP stages')],
            'scope':'Exact arithmetic and externally computed Selmer bounds. Integral-point completeness and Lean rank/primality refinement remain separate.',
            'running':'Mordell two-descent, nonmonic norms and elliptic primality',
        },
        'primesubgroups':{
            'title':'Prime-preimage lattices and bounded saturation',
            'subtitle':'Complete five/seven residue combinations<br/>and exact enlargement indices',
            'description':'Hidden mixed-generator divisibility is recovered through complete rational fibres. Hermite/Smith forms retain coefficient semantics, while independent free coordinates certify actual subgroup indices.',
            'metrics':[('20','replayed worked packets'),('80','independent lattice cases'),('5,7','complete prime preimages')],
            'scope':'Exact rational subgroup preimages and witnessed bounded saturation, finite local root obstructions and actual free-lattice indices. Global Mordell rank and formal interpreter refinement remain separate.',
            'running':'Complete prime fibres, canonical coefficient lattices and joint closure',
        },


        'ellipticfiveseven':{
            'title':'Rational subgroup preimages at five and seven',
            'subtitle':'Hermite and Smith presentations<br/>and bounded prime saturation',
            'description':'Complete mixed-generator division, good-reduction obstructions and rational torsion connect prime fibers to exact subgroup enlargement.',
            'metrics':[('15','worked examples'),('400','maximum projective lines'),('5','stages recovering P from 35P')],
            'scope':'Complete bounded subgroup operations and coefficient lattices. Ambient rank, automatic termination and general interpreter refinement remain open.',
            'running':'Five/seven preimages, coefficient lattices and witnessed saturation',
        },
        'rationalpowerbridge':{
            'title':'Rational power charts and weighted determinants',
            'subtitle':'Original-coordinate branching covers<br/>and a genuinely unordered Gram identity',
            'description':'Denominator-aware integrality charts retain every local branch and certify exact populations and bounded solutions. Canonical row subsets remove the factorial overcount in weighted Cauchy–Binet.',
            'metrics':[('19','generic declarations audited'),('10','native worked packets'),('240','independent exact census cases')],
            'scope':'Typed chart transport and counts, complete literal bounded source tables, a general unordered identity and real positivity corollaries. Generic traversal and compiler refinement remain open.',
            'running':'Rational powers, complete branching covers and unordered minors',
        },

        'arithmeticcharts':{
            'title':'Arithmetic charts and singular blowups',
            'subtitle':'Rational power transport<br/>and unordered weighted determinants',
            'description':'Exact denominator charts retain signed source equations. Content-normalized blowups expose new smooth branches, meet shared-factor CRT covers and supply arithmetic determinant weights.',
            'metrics':[('3','connected mathematical extensions'),('18,368','signed source points cross-checked'),('171','kernel declarations audited')],
            'scope':'Generic equation and chart semantics, an arbitrary finite-index unordered determinant identity, and ten native worked programs. Universal traversal refinement remains an explicit frontier.',
            'running':'Integer-valued power equations, normalized branches and weighted subsets',
        },
        'atlasintersectionfactored':{
            'title':'Factored intersections and predicate covers',
            'subtitle':'Shared-prime projection<br/>and simultaneous source equations',
            'description':'Maximal prime-power filters retain every compatible singular branch; coprime assembly gives the least-common-multiple cover and exact populations in enormous rectangles.',
            'metrics':[('14','generic declarations audited'),('6','native worked intersections'),('120','independent LCM census cases')],
            'scope':'Typed conjunction covers, exact cardinalities and source-bound native replays. Generic traversal, addressing and compiler refinement remain explicit obligations.',
            'running':'Shared factors, complete conjunction covers and exact populations',
        },
        'residueintersection':{
            'title':'Shared-factor residue intersections',
            'subtitle':'Gcd fibers, generalized CRT<br/>and exact populations for polynomial systems',
            'description':'Compatible local roots reconstruct uniquely modulo the least common multiple. Distinct polynomial constraints and existing coprime products now compose without losing overlapping prime factors.',
            'metrics':[('54','focused and neighbour tests'),('3','generic Lean theorems'),('120','composite example period')],
            'scope':'Exact bounded Python fiber joins and populations, paper CRT completeness, and Lean projection, cardinality and Bezout reconstruction theorems. Canonical-lcm source refinement remains explicit.',
            'running':'Shared-factor atlases and simultaneous polynomial constraints',
        },
        'weilspectral':{
            'title':'Rational blocks of the Weil representation',
            'subtitle':'Primitive projectors at every level<br/>and exact spectral operator calculus',
            'description':'Recursive old-level embeddings, odd parity complements, dyadic clock/shift blocks and original-coordinate CRT tensors turn the orbit dimension theorem into explicit constituent dimensions.',
            'metrics':[('260','exact dense projectors'),('77','blocks at level 1000000'),('87','Lean declarations audited')],
            'scope':'All-level paper decomposition, eleven generic Lean lemmas and native Fourier/chirp examples at levels 3, 4, 8 and 9. All-level orbit upper bounds and recursive intertwining remain formalization targets.',
            'running':'Primitive Weil blocks, recursive dimensions and spectral calculus',
        },
        'weilmonomial':{
            'title':'Kernel-proved Heisenberg coordinates',
            'subtitle':'Literal matrix actions<br/>and the odd orbit-quotient bridge',
            'description':'Explicit analysis and synthesis construct the actual basis, derive both generator coefficient laws, and identify the odd-level commutant with functions on its orbit quotient.',
            'metrics':[('41','audited declarations'),('2','new general Lean modules'),('10','retained orbit tests passed')],
            'scope':'No assumed basis, rank or supplied spanning family. Arithmetic orbit classification, even sign-clock support reduction and independent-root field transport retain explicit obligations.',
            'running':'Heisenberg coefficients, monomial fixed spaces and the orbit quotient',
        },
        'weilorbit':{
            'title':'All-level Weil dimensions and symmetry',
            'subtitle':'Phase-labelled orbits<br/>and a commutative commutant algebra',
            'description':'The odd and dyadic dimension formulas on paper, a transpose-reflection proof of commutativity, and the resulting multiplicity-free complex decomposition.',
            'metrics':[('166','exact phase/reflection levels'),('12','general Lean declarations'),('63','prior exact dimensions matched')],
            'scope':'All-level paper theorems with explicit classical group premises. Lean proves gauge and symmetry implications; concrete monomial fixed spaces and orbit classification remain to be formalized.',
            'running':'Orbit dimensions, transpose symmetry and multiplicity-free decomposition',
        },
        'weildimension':{
            'title':'Kernel-proved CRT commutant dimensions',
            'subtitle':'Explicit coefficient spaces<br/>and cyclic character multiplicativity',
            'description':'The missing product-dimension argument is now a general Lean proof, with ordinary matrix commutants, derived cyclic separation packets and actual CRT coordinate identities.',
            'metrics':[('30','new general declarations'),('3','new Lean modules'),('47','bridge declarations audited')],
            'scope':'Common characteristic-zero field and CRT-compatible primitive characters, with an odd factor second. Independent-root field normalization and all-exponent local formulas remain separate.',
            'running':'Coefficient spaces, matrix commutants and cyclic CRT dimensions',
        },
        'weilcrt':{
            'title':'Exact Fourier/chirp commutants',
            'subtitle':'The CRT generator bridge<br/>and exact dimensions at 63 levels',
            'description':'General Gauss-sum recovery and typed generator separation in Lean, with exact integer commuting operators and finite-field rank minors replacing numerical tolerances.',
            'metrics':[('17','general Lean declarations'),('63','exact finite-level packets'),('457','reconciled Mordell cases')],
            'scope':'Paper proof of general multiplicativity, kernel-proved algebraic components and exact finite dimensions. All-exponent local formulas and the final Lean dimension assembly remain open.',
            'running':'Exact commutants, Gauss recovery and the CRT bridge',
        },
        'residueatlascrt':{
            'title':'Complete multi-prime residue products',
            'subtitle':'Every CRT combination<br/>with exact factored populations',
            'description':'Source-bound complete local atlases, bijective coordinate CRT and kernel-checked rectangle counts without enumerating the product-modulus square.',
            'metrics':[('12','general CRT declarations'),('6','native worked products'),('120','independent census cases')],
            'scope':'Coprime local products and complete declared rectangles. Generic traversal refinement and global arithmetic bounds retain their own obligations.',
            'running':'Complete CRT atlases and exact factored populations',
        },
        'integervalued':{
            'title':'Integer-valued rational polynomials',
            'subtitle':'Exact integral domains<br/>and denominator-aware arithmetic',
            'description':'Universal quotient divisors, complete residue charts, source-bound rational identities and a natural-index Gamma bridge with nonenumerating interval populations.',
            'metrics':[('189','generic and generated declarations audited'),('13','source-bound worked packets'),('19,350','independent signed-domain checks')],
            'scope':'Proved arithmetic on exact integral domains. Population execution, generic JSON/compiler refinement and global power-free density retain their separate obligations.',
            'running':'Exact denominators, integral domains and universal quotient divisors',
        },
        'residueatlas':{
            'title':'Complete prime-power residue atlases',
            'subtitle':'Every singular branch<br/>and exact populations in enormous rectangles',
            'description':'Both smooth chart directions, complete singular lifts, global modular exclusions and kernel-checked nonenumerating two-coordinate counts tied to the original source polynomial.',
            'metrics':[('16','general theorem declarations'),('7','complete worked atlases'),('120','independent source census cases')],
            'scope':'Complete declared prime-power depths and exact modular populations. Global height bounds, general addressing refinement and compiler semantics retain independent obligations.',
            'running':'Complete residue atlases and exact original-coordinate populations',
        },
        'fixeddivisor':{
            'title':'Universal divisibility and complete repeated-factor arithmetic',
            'subtitle':'Finite windows, exact progression obstructions<br/>and global power-free fibres',
            'description':'A degree-plus-one gcd controls universal integer divisibility without separability. Repeated k-fold factors reduce global k-free values to complete finite unit fibres.',
            'metrics':[('185','generic and generated declarations audited'),('2,700','independent local residue comparisons'),('8','complete global repeated-factor packets')],
            'scope':'Kernel-checked finite-window and repeated-factor mathematics with source-bound worked packets. Separable polynomial density and generic compiler refinement remain open.',
            'running':'Universal divisibility, integer-valued normalization and exact finite hits',
        },
        'boundedpatch':{
            'title':'Complete bounded residue patches',
            'subtitle':'Smooth first lifts<br/>and auxiliary relations for every bounded solution',
            'description':'Exact source equations, complete finite coverings and typed native certificates connecting auxiliary interpolation to every integer solution in a declared rectangle and residue class.',
            'metrics':[('7','general theorem declarations'),('6','complete worked packets'),('12','focused replay and rejection tests')],
            'scope':'Complete declared boxes and smooth first lifts. Global height bounds, integral saturation, singular branching and generic compiler semantics remain independent.',
            'running':'Complete bounded source coverage and auxiliary vanishing',
        },
        'residuedeterminant':{
            'title':'Integral kernels and residue determinants',
            'subtitle':'Exact auxiliary relations<br/>and bounded arithmetic certificates',
            'description':'A narrow independently compiled extraction from OpenAI mathematical sources: rational kernel spanning, weighted determinant divisibility and source-bound polynomial relations.',
            'metrics':[('14','general theorem declarations'),('12','exact worked packets'),('120','independent matrix comparisons')],
            'scope':'Bounded point sets and explicit determinant bounds. Integral lattice saturation, global height bounds and manuscript-wide verification retain separate obligations.',
            'running':'Integral kernels, local expansions and exact bounded vanishing',
        },
        'powerfree':{
            'title':'Finite local arithmetic at every prime',
            'subtitle':'Exact Bezout identities, prime-power roots<br/>and addressable avoidance domains',
            'description':'A finite kernel-checked criterion for all-prime local admissibility, fixed-divisor obstructions for every signed integer, exact singular root lifting and nonenumerating interval counts.',
            'metrics':[('132','reusable and generated declarations audited'),('64','independent polynomial census cases'),('512','independent prime-square root counts')],
            'scope':'Local power-free arithmetic on the pinned Lean 4.20 toolchain. No global density, generic JSON interpreter or arbitrary repeated-factor admissibility claim.',
            'running':'Finite local power-free arithmetic and exact avoidance domains',
        },
        'halvesrefinement':{
            'title':'The original elliptic interface is connected',
            'subtitle':'Actual group transport, literal outputs<br/>and complete signed quartic lifts',
            'description':'An explicit additive equivalence for generalized Weierstrass square completion, native equality with returned coordinate lists, and nonsquare or wrong-sign lift elimination.',
            'metrics':[('16','reusable theorem declarations audited'),('9','fully connected worked packets'),('3','previous interface gaps closed')],
            'scope':'Actual original-model halving and exact literal rational output semantics within certificate budgets. Generic JSON parser refinement, efficient Sturm proofs and global rank remain separate.',
            'running':'Original-model elliptic transport and complete literal halving fibres',
        },
        'bridges':{
            'title':'Elliptic bridges and bounded saturation',
            'subtitle':'Point laws, typed packets<br/>and explicit research boundaries',
            'description':'Kernel-checked generalized addition and binary multiplication, tripling identities, typed root and fibre semantics, bounded repeated prime preimages and real Legendre finite-part enclosures.',
            'metrics':[('5','new formal modules'),('6','worked saturation packets'),('5','real endpoint packets')],
            'scope':'Specified formal interfaces and bounded arithmetic. Global Mordell bounds, Matveev, full JSON/compiler semantics and arbitrary singular periods remain open.',
            'running':'Point-law refinement, bounded saturation and singular finite parts',
        },
        'nativehalves':{
            'title':'Complete native elliptic halving fibres',
            'subtitle':'Checked anchors, torsion cosets<br/>and root-free obstructions',
            'description':'Concrete rational doubling in Mathlib, complete actual-point halving fibres without height bounds, and quartic-root obstructions including branch targets.',
            'metrics':[('2','new reusable point-group theorems'),('6','worked native fibre packets'),('3','complementary certificate routes')],
            'scope':'Native completed-model point semantics. Original-model transport, literal output-list refinement and general nonsquare lifting remain open.',
            'running':'Native actual-point halving and the remaining arithmetic interfaces',
        },
        'subgroups':{
            'title':'Complete rational subgroup preimages',
            'subtitle':'Hidden division relations<br/>and exact witness saturation',
            'description':'All coefficient lines over F2 and F3, complete rational prime fibres, exact replacement generators and a witness subgroup saturated at both primes.',
            'metrics':[('10','worked prime-preimage packets'),('40','maximum projective coefficient lines'),('2 / 3','hidden relative indices recovered')],
            'scope':'Complete rational preimage generators for supplied subgroups with at most four sources. Prime saturation of a specified witness subgroup; ambient rank, other primes and global integral bounds remain open.',
            'running':'Rational subgroup preimages and hidden divisibility',
        },
        'tripling':{
            'title':'Complete rational elliptic division',
            'subtitle':'Tripling, torsion cosets<br/>and composite multiplication fibres',
            'description':'Exact generalized Weierstrass tripling, complete rational-root evidence, rational nine-torsion and staged division through multipliers up to thirty-six.',
            'metrics':[('19','worked scientific packets'),('14','supported multiplication scalars'),('9','rational kernel points demonstrated')],
            'scope':'Complete rational fibres in bounded exact Python with discovery-free replay. Existing Lean fibre foundations are preserved; no new interpreter proof, complete rank claim or global integral-point bound.',
            'running':'Complete rational tripling and compositional division',
        },
        'nativebridges':{
            'title':'Native bridges across exact mathematics',
            'subtitle':'Rational roots, nonenumerating populations<br/>and marked Picard–Lefschetz actions',
            'description':'Original-source rational root completeness, huge affine residue counts, general bilinear transvection laws and checked signed-cycle-word execution through genus four.',
            'metrics':[('12','reusable native theorem declarations'),('48','generated declarations audited'),('21','source-bound producer packets')],
            'scope':'Two reusable Lean modules and four public native certificate operations. The complete repository archive preserves the concurrent flavor advances and the prior research receipts.',
            'running':'Arithmetic, populations, marked topology and the remaining bridges',
        },
        'closures':{
            'title':'General identities and native certificates',
            'subtitle':'Cauchy–Binet, bounded source populations<br/>and marked Legendre generators',
            'description':'Arbitrary-dimensional weighted squared minors, kernel-checked distinct-image counts and numeric selections, conditional integral uniqueness, and replay-bound rational marked continuation.',
            'metrics':[('7','reusable theorem declarations audited'),('14','generated population declarations checked'),('2','general Lean modules added')],
            'scope':'Focused native proofs and bounded executable certificates. The complete tracked archive preserves the separate flavor merge and the historical research receipts.',
            'running':'General determinants, native populations and the remaining research program',
        },
        'frontier':{
            'title':'Connected non-flavor advances',
            'subtitle':'Native arithmetic proofs, bounded streams<br/>and certified marked monodromy',
            'description':'Complete native rational roots and elliptic two-torsion, compositional finite-domain certificates, noncoprime residue charts, variable-width factorial obstructions, rectangular determinants, exact graph metrics and rational analytic enclosures.',
            'metrics':[('42','audited public Lean declarations'),('277,345','exact SMT command slices compared'),('148','certified steps around a Legendre loop')],
            'scope':'New mathematical proofs and bounded executable extensions. Historic census proofs retain their own receipts; open research premises and unverified interpreter boundaries remain explicit.',
            'running':'Connected non-flavor proofs and the remaining research program',
        },
        'division':{
            'title':'Exact elliptic division in Lean',
            'subtitle':'Kernel cosets, halving quartics<br/>and complete rational-root transport',
            'description':'Reusable group fibre equivalences, explicit generalized Weierstrass normalization, nonexceptional doubling algebra and integer-to-rational root completeness, with a current repository frontier review.',
            'metrics':[('17','audited public Lean declarations'),('2','directions of complete root transport'),('4','degree of the exact halving polynomial')],
            'scope':'Mathematical Lean foundations with explicit hypotheses. Python root search, parsing, point-law refinement and independence interpretation remain separate obligations.',
            'running':'Formal division fibres and the current repository frontier',
        },
        'elliptic':{
            'title':'Exact elliptic witnesses',
            'subtitle':'Complete rational division fibres<br/>and replayable independence lower bounds',
            'description':'Generalized Weierstrass arithmetic, rational model transport, two-isogenies, certified rational halving fibres and an independently implemented bounded certificate checker.',
            'metrics':[('19','persistent mathematical object kinds'),('11','worked scientific packets'),('2','independent rational witnesses in the example')],
            'scope':'Complete rational halving fibres and witness-span lower bounds in bounded exact Python. No new Lean proof, complete Mordell-Weil basis, full saturation or global integer-point census.',
            'running':'Elliptic arithmetic, rational fibres and exact witness transport',
        },
        'literature':{
            'title':'Literature into executable curves',
            'subtitle':'Actual maps, marked kernels<br/>and certified differential arithmetic',
            'description':'Composed elliptic towers, formal isogeny reconstruction, Richelot correspondences, superelliptic reduction, tensor invariants, binomial periods, marked analytic bounds, root clusters, Frobenius and relative sunrise integrals.',
            'metrics':[('18','persistent mathematical object kinds'),('22','worked research receipts'),('32','degree of the three-factor isogeny')],
            'scope':'Exact identities and bounded analytic/p-adic certificates in specified classes. General correspondences, singular-endpoint continuation, arbitrary arithmetic stable models and differential Galois classifications remain open.',
            'running':'Geometry, differential algebra, marked topology and arithmetic',
        },
        'extensions':{
            'title':'Algebraic curve execution',
            'subtitle':'Differential fields, local geometry<br/>and actual quotient maps',
            'description':'Finite etale differential arithmetic, algebraic degeneration charts, resolved logarithmic resonances, explicit finite-action quotients and paired-cover Jacobian isogenies.',
            'metrics':[('15','persistent object kinds'),('8','verified symmetry quotients'),('4 / 8','paired-cover isogeny degrees')],
            'scope':'Exact polynomial and differential identities within explicit budgets. Paired actual double covers certify specific Jacobian isogenies. General stable reduction, marked integral kernels, arbitrary correspondences and rigorous analytic continuation remain open.',
            'running':'Differential extensions, local branches and geometric quotient sectors',
        },
        'research':{
            'title':'Projective curve research',
            'subtitle':'Local execution, simultaneous deformations<br/>and exact structural searches',
            'description':'Binary-form projective tangents, several-parameter flat connections, Laurent and logarithmic Frobenius execution, reciprocal elliptic quotients, continuous de Rham pairings and integral simplicial cycle maps.',
            'metrics':[('3','simultaneous parameters supported'),('2','reciprocal elliptic quotient maps'),('6','connected research extensions')],
            'scope':'Exact standard-library identities and finite formal execution within declared budgets. Integral maps require an explicit simplicial map. Differential projectors do not certify Jacobian factors or rational Betti structures. No new kernel proof or rigorous numerical continuation.',
            'running':'Projective geometry, local differential execution and marked topology',
        },
        'structure':{
            'title':'Geometry inside the polynomial',
            'subtitle':'Deformation, collision residues<br/>and hidden elliptic quotient systems',
            'description':'Exact explanations of coordinate motion, simultaneous root velocities, nodal period residues, translated reflection symmetry and two elliptic quotients of a genus-two sextic.',
            'metrics':[('17','simple collision roots analyzed'),('2 + 2','elliptic period blocks'),('183','recorded root geometries')],
            'scope':'Exact rational and squarefree-algebra identities on declared families. Root plots and marked period execution are numerical approximations. No new Lean theorem or worldwide priority claim.',
            'running':'Root motion, deformation geometry and quotient equations',
        },
        'families':{
            'title':'Curve family execution',
            'subtitle':'Polynomial structure, differential systems<br/>and marked period continuation',
            'description':'Exact hyperelliptic family connections, selected-observable operators, rational parameter-path exclusion, numerical marked periods and persistent arithmetic queries.',
            'metrics':[('5','compiled family definitions'),('4 to 1','isotrivial observable reduction'),('63','recorded period samples')],
            'scope':'Standard-library exact algebra on declared monic odd-degree families. Numerical roots, quadrature and ODE continuation retain their stated error scope. No new Lean theorem.',
        },
        'policies':{
            'title':'Exact decision policies',
            'subtitle':'Operating regions, collision geometry<br/>and adaptive diagnostics',
            'description':'Complete bounded calibration regions through vertex-oracle discovery, distinct cubic and monotone polynomial images, and globally optimal resettable diagnostic programs.',
            'metrics':[('15','coupled operating cells'),('231','lazy-window feasible settings'),('3','optimal diagnostic cost')],
            'scope':'Exact reusable policies on declared bounded models. Complete cubic collision geometry; positive-cost resettable minimax diagnostics. Python evidence, no new Lean theorem or physical derivation.',
        },
        'opencontent':{
            'title':'Open content',
            'subtitle':'Exact direct-use workflows<br/>and research diagnostics',
            'description':'Bounded integer design, globally cheapest experiments, algebraic graph sampling, nonlinear sequence execution, distinct populations, symbolic joins, compatible charts and a local object console.',
            'metrics':[('8','persistent object kinds'),('52','nonlinear families'),('512','family-partitioned tasks')],
            'scope':'Full source and evidence without an archive cap. Tested Python and measured C kernels; general mathematical proofs, global smooth geometry and physical derivations retain their stated open scope.',
        },
        'applications':{
            'title':'Executable applications',
            'subtitle':'Persistent objects, exact workflows<br/>and measured configuration design',
            'description':'Shared sequences, discrete calibration, conditional graph sampling, local geometry, combinatorial sizes, mathematical tasks and a persistent query service.',
            'metrics':[('6','persistent object kinds'),('256','grouped arithmetic tasks'),('28','measured kernel trials')],
            'scope':'Tested standard-library application integrations. The conventional kernel wins the demo; global geometry and physical derivations remain open.',
        },
        'population':{
            'title':'Exact populations',
            'subtitle':'Configurations, datasets<br/>and addressable mathematics',
            'description':'Finite exact configuration spaces, reversible global ranks, sampling without replacement, original-coordinate lookup and reproducible mathematical datasets.',
            'metrics':[('768','related arithmetic tasks'),('156','sourced unit domains'),('512','sourced index records')],
            'scope':'Standard-library application layer over existing complete arithmetic. Sampling and rank transport are independently tested; no new Lean proof or industrial performance claim is made.',
        },
        'polynomial':{
            'title':'Polynomial capacity',
            'subtitle':'Coordinates, integer domains<br/>and discrete dynamics',
            'description':'Automatic polynomial decomposition, complete nonlinear integer pullbacks, Boolean sign domains, global discrete optimization and a domain-aware Gamma interface.',
            'metrics':[('6,422','equations matched'),('141','new completions'),('3,080','global optima checked')],
            'scope':'Exact Python arithmetic and replayable evidence. Existing outer theorem provenance is preserved. This expansion does not add a Lean proof of the general Sturm solver or Python compiler.',
        },
        'semilinear':{
            'title':'Semilinear capacity',
            'subtitle':'Queryable equations<br/>and exact integer dynamics',
            'description':'Complete polynomial and modular domains, enormous-range counting and rank selection, signed power-curve charts, nonlinear integer fibres and every original-coordinate optimizer.',
            'metrics':[('262','finite-image cases closed'),('238','new complete answers'),('3,080','constrained optima checked')],
            'scope':'Exact Python evidence and independent reference checks. The prior Lean transport layer is preserved. This expansion adds no Lean proof of the general periodic-domain producer or whole compiler.',
        },
    }
    profile=editions[edition]
    output=Path(output);output.parent.mkdir(parents=True,exist_ok=True)
    temporary=output.parent/'math';temporary.mkdir(exist_ok=True)
    fonts=Path('/usr/share/fonts/truetype/dejavu')
    for name,file in [('Body','DejaVuSerif.ttf'),('BodyBold','DejaVuSerif-Bold.ttf'),
                      ('Label','DejaVuSans.ttf'),('LabelBold','DejaVuSans-Bold.ttf'),
                      ('Code','DejaVuSansMono.ttf')]:
        pdfmetrics.registerFont(TTFont(name,str(fonts/file)))
    pdfmetrics.registerFontFamily('Body',normal='Body',bold='BodyBold',italic='Body',boldItalic='BodyBold')
    navy=colors.HexColor('#173348');teal=colors.HexColor('#157A86')
    body=ParagraphStyle('body',fontName='Body',fontSize=10.2,leading=15.4,spaceAfter=9,textColor=navy)
    if edition in ('atlasintersectionfactored','fixeddivisor','integervalued','weilmonomial'):body.fontSize=9.9;body.leading=14.5;body.spaceAfter=8
    if edition=='rationalpowerbridge':body.fontSize=9.5;body.leading=13.8;body.spaceAfter=7
    if edition in ('primesubgroups','torsionpell'):body.fontSize=9.3;body.leading=12.8;body.spaceAfter=5;body.allowWidows=0;body.allowOrphans=0
    if edition=='integervalued':body.leading=14.1
    if edition=='bridges':body.allowWidows=0;body.allowOrphans=0
    if edition=='research':body.leading=14.8;body.spaceAfter=8
    heading=ParagraphStyle('heading',fontName='LabelBold',fontSize=14,leading=19,spaceBefore=18,spaceAfter=9,textColor=teal,keepWithNext=True)
    small=ParagraphStyle('small',fontName='Label',fontSize=9,leading=14,spaceAfter=10,textColor=navy)
    title=ParagraphStyle('title',fontName='LabelBold',fontSize=30,leading=37,textColor=navy,spaceAfter=20)
    code=ParagraphStyle('code',fontName='Code',fontSize=7.6,leading=11.5,backColor=colors.HexColor('#F0F4F6'),borderPadding=9,spaceBefore=7,spaceAfter=14)
    metric=ParagraphStyle('metric',fontName='LabelBold',fontSize=22,leading=30,textColor=teal,alignment=TA_CENTER)
    caption=ParagraphStyle('caption',fontName='Label',fontSize=9,leading=14,textColor=navy,alignment=TA_CENTER)
    story=[Spacer(1,37),Paragraph('PERFECTPOWER / TECHNICAL MONOGRAPH',small),Spacer(1,20),
           Paragraph(profile['title'],title),Paragraph(profile['subtitle'],ParagraphStyle('subtitle',parent=heading,fontSize=20,leading=28,textColor=navy)),
           Spacer(1,30),Paragraph(profile['description'],body),Spacer(1,22)]
    table=Table([[Paragraph(number,metric) for number,label in profile['metrics']],
                 [Paragraph(label,caption) for number,label in profile['metrics']]],colWidths=[160]*3)
    table.setStyle(TableStyle([('BACKGROUND',(0,0),(-1,-1),colors.HexColor('#F0F4F6')),('TOPPADDING',(0,0),(-1,0),12),('BOTTOMPADDING',(0,1),(-1,1),15)]))
    story+=[table,Spacer(1,27),Paragraph(profile['scope'],small),Spacer(1,18),Paragraph('Source, corpus receipts and reproduction commands accompany the repository snapshot.',small),PageBreak()]
    def inline(s):
        s=escape(s).replace('\u2013','-').replace('\u2014','-')
        if edition=='torsionpell':
            def inline_math(match):
                text=match.group(1)
                for old,new in [(r'\mathbb{Q}','ℚ'),(r'\Gamma','Γ'),(r'\ldots','…'),(r'\leq','≤'),(r'\sqrt{2}','√2'),('{,}',',')]:
                    text=text.replace(old,new)
                text=re.sub(r'\^\{([^}]+)\}',r'<super>\1</super>',text)
                text=re.sub(r'_\{([^}]+)\}',r'<sub>\1</sub>',text)
                text=re.sub(r'\^([0-9])',r'<super>\1</super>',text)
                text=re.sub(r'_([A-Za-z0-9])',r'<sub>\1</sub>',text)
                return text
            s=re.sub(r'\$([^$]+)\$',inline_math,s)
        s=re.sub(r'`([^`]+)`',r'<font name="Code" size="8.6">\1</font>',s)
        s=re.sub(r'\[([^\]]+)\]\(([^)]+)\)',r'\1 (\2)',s)
        return s
    lines=Path(source).read_text().splitlines();i=0;formula_count=0
    while i<len(lines):
        line=lines[i]
        if not line.strip():i+=1;continue
        if line.startswith('# '):i+=1;continue
        if line.startswith('## '):story.append(Paragraph(inline(line[3:]),heading));i+=1;continue
        if line.startswith('|'):
            table_rows=[]
            while i<len(lines) and lines[i].startswith('|'):
                cells=[c.strip() for c in lines[i].strip().strip('|').split('|')]
                if not all(re.fullmatch(r':?-+:?',c) for c in cells):table_rows.append(cells)
                i+=1
            width=len(table_rows[0]);table_style=ParagraphStyle('tablecell',parent=small,fontSize=8,leading=11,spaceAfter=0)
            grid=Table([[Paragraph(inline(c),table_style) for c in row] for row in table_rows],colWidths=[480/width]*width,repeatRows=1)
            grid.setStyle(TableStyle([('BACKGROUND',(0,0),(-1,0),colors.HexColor('#E3EEF0')),('VALIGN',(0,0),(-1,-1),'TOP'),('GRID',(0,0),(-1,-1),.3,colors.HexColor('#B6C7CE')),('TOPPADDING',(0,0),(-1,-1),7),('BOTTOMPADDING',(0,0),(-1,-1),7)]))
            story.extend([grid,Spacer(1,12)]);continue
        if line=='$$':
            j=i+1
            while lines[j]!='$$':j+=1
            formula=' '.join(lines[i+1:j]);formula_count+=1
            fig=plt.figure(figsize=(8,0.8));fig.text(.5,.5,'$'+formula+'$',ha='center',va='center',fontsize=16)
            path=temporary/f'equation_{formula_count}.png';fig.savefig(path,dpi=220,bbox_inches='tight',pad_inches=.08,transparent=True);plt.close(fig)
            image=Image(str(path));scale=min(475/image.imageWidth,1/2.5)
            image.drawWidth=image.imageWidth*scale;image.drawHeight=image.imageHeight*scale;image.hAlign='CENTER'
            story+=[Spacer(1,7),image,Spacer(1,13)];i=j+1;continue
        if line.startswith('```'):
            j=i+1;block=[]
            while j<len(lines) and not lines[j].startswith('```'):
                chunks=textwrap.wrap(lines[j],width=91,break_long_words=False,break_on_hyphens=False) or ['']
                block.extend((('  ' if k else '')+c+(' \\' if k<len(chunks)-1 else '')) for k,c in enumerate(chunks));j+=1
            rendered=Preformatted('\n'.join(block),code)
            story.append(KeepTogether([rendered]) if edition=='structure' else rendered);i=j+1;continue
        paragraph=[line];i+=1
        while i<len(lines) and lines[i].strip() and not lines[i].startswith(('#','```','$$')):
            paragraph.append(lines[i]);i+=1
        story.append(Paragraph(inline(' '.join(paragraph)),body))
    def furniture(canvas,doc):
        canvas.saveState();canvas.setStrokeColor(colors.HexColor('#D0DBE0'));canvas.setLineWidth(.5)
        canvas.line(57,49,538,49);canvas.setFont('Label',8);canvas.setFillColor(navy)
        canvas.drawString(57,34,'PERFECTPOWER  /  '+profile['title'].upper());canvas.drawRightString(538,34,str(doc.page))
        if doc.page>1:canvas.setFont('Label',8);canvas.drawString(57,807,profile.get('running','Exact domains, preserved integer images, complete ties'))
        canvas.restoreState()
    document=SimpleDocTemplate(str(output),pagesize=(595.28,841.89),rightMargin=57,leftMargin=57,topMargin=57,bottomMargin=66,
                               title=profile['title']+': '+re.sub('<br/>',' ',profile['subtitle']).lower(),author='PerfectPower')
    document.build(story,onFirstPage=furniture,onLaterPages=furniture)
    print(output)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--source',type=Path)
    parser.add_argument('--edition',choices=('mordelltwodescent','torsionpell','primesubgroups','ellipticfiveseven','rationalpowerbridge','arithmeticcharts','atlasintersectionfactored','residueintersection','weilspectral','polynomial','semilinear','population','applications','opencontent','policies','families','structure','research','extensions','literature','elliptic','division','frontier','closures','tripling','nativebridges','nativehalves','subgroups','halvesrefinement','bridges','residuedeterminant','powerfree','boundedpatch','residueatlas','residueatlascrt','weilcrt','weildimension','weilorbit','weilmonomial','fixeddivisor','integervalued'),default='polynomial')
    parser.add_argument('--output',type=Path,required=True);args=parser.parse_args()
    source=args.source or Path(__file__).resolve().parents[1]/'docs'/({'mordelltwodescent':'MORDELL_TWO_DESCENT_MONOGRAPH.md','torsionpell':'TORSION_INDEX_PELL7_MONOGRAPH.md','primesubgroups':'ELLIPTIC_PRIME_SUBGROUPS_MONOGRAPH.md','ellipticfiveseven':'ELLIPTIC_FIVE_SEVEN_MONOGRAPH.md','rationalpowerbridge':'ARITHMETIC_CHART_BRIDGE_MONOGRAPH.md','arithmeticcharts':'ARITHMETIC_CHART_PIPELINE_MONOGRAPH.md','atlasintersectionfactored':'RESIDUE_ATLAS_INTERSECTION_FACTORED_MONOGRAPH.md','residueintersection':'RESIDUE_ATLAS_INTERSECTION_MONOGRAPH.md','weilspectral':'WEIL_SPECTRAL_MONOGRAPH.md','weilmonomial':'WEIL_MONOMIAL_MONOGRAPH.md','weilorbit':'WEIL_LOCAL_DIMENSION_MONOGRAPH.md','weildimension':'WEIL_DIMENSION_MONOGRAPH.md','weilcrt':'WEIL_CRT_MONOGRAPH.md','integervalued':'INTEGER_VALUED_POLYNOMIAL_MONOGRAPH.md','residueatlascrt':'RESIDUE_ATLAS_CRT_MONOGRAPH.md','residueatlas':'RESIDUE_ATLAS_MONOGRAPH.md','boundedpatch':'BOUNDED_RESIDUE_PATCH_MONOGRAPH.md','residuedeterminant':'RESIDUE_DETERMINANT_MONOGRAPH.md','elliptic':'ELLIPTIC_WITNESSES_MONOGRAPH.md','literature':'LITERATURE_CURVE_EXECUTION_MONOGRAPH.md','population':'POPULATION_MONOGRAPH.md','applications':'APPLICATIONS_MONOGRAPH.md','opencontent':'OPEN_CONTENT_MONOGRAPH.md','policies':'DECISION_POLICIES_MONOGRAPH.md','families':'CURVE_FAMILIES_MONOGRAPH.md','structure':'CURVE_STRUCTURE_MONOGRAPH.md','research':'CURVE_RESEARCH_MONOGRAPH.md'}.get(args.edition,args.edition.upper()+'_CAPACITY_MONOGRAPH.md'))
    render(source,args.output,edition=args.edition)
