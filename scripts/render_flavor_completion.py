"""Create the reader PDF from the complete Markdown monograph and receipts."""
from pathlib import Path
from io import BytesIO
from xml.sax.saxutils import escape
import re
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Image, PageBreak, KeepTogether, LongTable, TableStyle
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.lib.colors import HexColor
from reportlab.lib.enums import TA_LEFT
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.lib.utils import ImageReader

ROOT=Path(__file__).resolve().parents[1]
SOURCE=ROOT/'docs/B5_FLAVOR_COMPLETION.md'
SOURCES=[SOURCE,ROOT/'docs/B5_FLAVOR_MEDIATOR.md',ROOT/'docs/M22_FLAVOR_FRAME.md',ROOT/'docs/M22_TRANSPORT_INTERACTIONS.md',ROOT/'docs/VALENTINER_INVARIANT_INTERACTIONS.md',ROOT/'docs/VALENTINER_CP_AND_GLOBAL_MODES.md',ROOT/'docs/FLAVOR_SEARCH_INPUT_AUDIT.md',ROOT/'docs/VALENTINER_SUSY_VACUA.md',ROOT/'docs/VALENTINER_JOINT_POTENTIAL.md',ROOT/'docs/FLAVOR_KINETIC_FREEDOM.md',ROOT/'docs/VALENTINER_ADJOINT_UV.md',ROOT/'docs/VALENTINER_CANONICAL_RESULTS.md',ROOT/'docs/VALENTINER_QUANTUM_COMPLETION.md',ROOT/'docs/VALENTINER_HERMITIAN_INTERACTIONS.md',ROOT/'docs/SOMMERFELD_CONSTANT_AND_66_DEGREES.md',ROOT/'docs/VALENTINER_NONET_JOINT_POTENTIAL.md',ROOT/'docs/VALENTINER_SOFT_MEDIATION_AND_LOOP_CLOSURE.md',ROOT/'docs/FLAVOR_EXACT_RUNNING_AND_SELECTION.md',ROOT/'docs/FLAVOR_COSMOLOGY_MONOGRAPH.md',ROOT/'docs/FLAVOR_FINITE_SPECTRAL_MATCHING.md',ROOT/'docs/FLAVOR_FUNCTIONAL_MASS_AND_OPERATOR_MIXING.md',ROOT/'docs/FLAVOR_SINGLET_MEDIATION_AND_OPERATOR_MODULES.md',ROOT/'docs/FLAVOR_SINGLET_QUANTUM_COMPLETION.md',ROOT/'docs/FLAVOR_SCALAR_FEEDBACK_AND_WEAK_CONTINUATION.md',ROOT/'docs/FLAVOR_FIXED_GAUGE_AND_GOLDSTONE_WARD.md',ROOT/'docs/FLAVOR_ANALYTIC_RADIAL_PROFILE.md',ROOT/'docs/VALENTINER_DIAGONAL_VACUUM_CENSUS.md',ROOT/'docs/VALENTINER_FRAME_SELECTION_AND_NONLINEAR_VACUA.md']
DEST=ROOT/'output/pdf/B5_Protected_Flavor_Monograph.pdf'

EQUATIONS={
 'Exact scalar poles and canonical residues':r'$F(z)=H-zK(z),\qquad Z(z)=-F^{\prime}(z)$',
 'Connecting the scalar metric to conditional CP walls':r'$\sigma_{\mathrm{EFT}}\leq\sigma_{\mathrm{UV}}\leq\sigma_{\mathrm{valley}}$',
 'The exact 66-degree algebraic relation':r'$\theta=11\pi/30,\qquad 1-2\cos(12\theta)=(3-\sqrt{5})/2$',
 'A photon theorem for the protected canonical action':r'$\sum_{i=1}^{6}\log(\mu/m_i)=6\log\mu-3\log(vym)$',
 'The independent gauge boundary and the mechanism requirement':r'$\mathcal{L}_{\gamma}=-\frac{k_0}{4}F_{\mu\nu}F^{\mu\nu},\qquad\alpha^{-1}=4\pi k_0$',
 'A low-degree invariant basis with an exact determinant':r'$\det\mathcal{W}=\chi^3,\qquad\chi=\operatorname{Im}\operatorname{Tr}(R^2T^2RT)$',
 'Exact finite spectra and physical currents':r'$h_i^2=\frac{(a^2-\ell_i^2)(m^2-\ell_i^2)}{\ell_i^2},\qquad M_i=\frac{am}{\ell_i}$',
 'An exact one-loop phase theorem':r'$G_{IK}G_{KI}\in\mathbb{R}\quad\Longrightarrow\quad\operatorname{Im}\operatorname{Tr}(D^{-1}\delta D)=0$',
 'A complete mass-only affine candidate calculation':r'$q^3 f(t)^2-d^2 g(t)^3=0,\qquad t=a_2/a_1$',
 'The canonical result':r'$\overline{\theta}_{\rm tree}=0,\qquad J=1.13669\times10^{-6}$',
 'Why the previous assignment needed a determinant audit':r'$\det D(v)=v^3\det M\det Y_0,\qquad \overline{\theta}_{\rm old}=-2.46264$',
 'A determinant protected by the interaction graph':r'$\det D(v)=(vy)^3\det M,\qquad WMW^{-1}=(WMW^{-1})^{\dagger}$',
 'Canonical mass scales and fixed mixing frames':r'$y_i(\eta)=\frac{y\eta}{\sqrt{\eta^2+\sigma_i^2}},\qquad P_i(\eta)=P_i(1)$',
 'Finite-scale pole normalization and physical currents':r'$V=N_u^{\dagger}N_d,\qquad Z_f=N_f^{\dagger}N_f,\qquad h_{ij}=Z_{ij}m_j/v$',
 'The precise protection boundary':r'$\Delta\overline{\theta}=3\arg(y_d+c\det L/\Lambda^3)$',
 'The central construction':r'$J=-2.67675\times10^{-5},\quad m_{\rm scalar,min}^2>9.5\times10^{-7}$',
 'Fields and justified contractions':r'$Y_f=-h_f(M_f^{-1}C_f)_u\,[I+(M_f^{-1}C_f)^{\dagger}(M_f^{-1}C_f)]^{-1/2}$',
 'The complete scalar operator boundary':r'$N_{\rm scalar}^{\rm renorm}=4+1+25=30$',
 'Five quartic channels with no arbitrary frame':r'$\operatorname{Sym}^2(8)=1+5+5+8+8+9,\quad N_{\rm CP\ even}=5$',
 'Controlled rank lifting':r'$D=\frac{\alpha F+30\,Q\circ\overline{F}}{\alpha^2-900},\quad \alpha=33+p$',
 'The source CP audit':r'$45^2=2025,\quad N_{\rm CP\ fixed}=289$',
 'Full mediator matching and a bounded potential':r'$V_{\rm stab}=10^{-10}(N_L+N_A+N_B)^6$',
 'Fixed-mass protection and practical conclusion':r'$\operatorname{Im}\det[H_u,H_d]=2J\,\Delta(H_u)\Delta(H_d)$',
 'Nine real polynomial covariants':r'$R=X^{\dagger}X,\quad S=X^{\dagger}ZZ^{\dagger}X,\quad \det\mathcal{M}=\tau^3$',
 'An invariant certificate of physical CP':r'$\operatorname{Im}\operatorname{Tr}(R^2S^2RS)=\Delta(R)\tau$',
 'Positive completion and finite degree':r'$B(\Phi)=(I+T(\Phi))^2+\eta I\geq\eta I$',
 'Fixed masses with full heavy matching':r'$B=Y_0^{\dagger}H_{\rm target}^{-1}Y_0-A^{\dagger}A,\qquad YY^{\dagger}=H_{\rm target}$',
 'A shared non-Abelian source label':r'$Z_8=Z-\frac{\operatorname{Tr}Z}{3}I,\quad V_{\rm eff}=-\frac{k^2}{M^2}\Vert Z_8\Vert^2$',
 'The exact joint operator census':r'$N_{\rm CP\ even}=7+1+41+7+207=263$',
 'Nonorthogonal local vacua and physical CP':r'$\operatorname{Im}(G_{12}G_{23}G_{31})=\frac{\sqrt{3}}{16},\qquad\det G=\frac{1}{8}$',
 'Why nonorthogonality changes the protection problem':r'$H\,\Delta q=-\nabla O,\qquad \operatorname{rank}\frac{\partial(|V_{us}|,|V_{cb}|,|V_{ub}|,J)}{\partial c}=4$',
 'Fully re-minimized finite deformations':r'$C_{\rm eff}=\frac{|V_{ub}|(1-|V_{ub}|^2)}{|V_{us}||V_{cb}|},\qquad C_{\rm eff}^2-3C_{\rm eff}+1=0$',
 'The group-aligned branch and all nine link masses':r'$r^3=-\frac{a}{32b+2c},\qquad m_1=|96b+6c|\,|r|^4,\quad m_8=|72b|\,|r|^4$',
 'What exact supersymmetry does to the sources':r'$\nabla F_6(\phi)=0\ \Longleftrightarrow\ \phi=0$',
 'A specified breaking extension with stable nonzero sources':r'$V_\phi=\kappa^2\|\nabla F_6\|^2-m^2\|\phi\|^2+2A\kappa\,\operatorname{Re} F_6$',
 'A complete obstruction for the orthogonal axis branch':r'$|V_{ij}|=0\quad\mathrm{or}\quad |V_{ij}|\geq\frac{\sqrt{5}-1}{4}\simeq0.309$',
 'The permitted interaction still moves the solved frame':r'$H\,\Delta q=-\nabla O,\qquad O=|\phi_{u1}^{\dagger}L\phi_{d1}|^2$',
 'Exact CP on the elementary field content':r'$X\overline{R(g)}X^{-1}=R(u(g)),\qquad X\overline{X}=I$',
 'Cross-sector sequestering and its exact operator boundary':r'$G_u\times G_d,\qquad \left|\phi_{ui}^{\dagger}\Lambda\phi_{dj}\right|^2\quad (\mathrm{degree}\ 6)$',
 'A representation-derived positive link interaction':r'$I_6(U)=\langle T,T\circ U\rangle,\qquad \operatorname{Re} I_6(U)\leq\|T\|^2=16$',
 'Physical CP established through quark invariants':r'$J\neq0,\qquad \operatorname{Im}\det[H_u,H_d]\neq0,\qquad J_{\rm CP}=-J$',
 'A global three-mode operator with explicit breaking':r'$\dim\ker M^2=3,\qquad \lambda_{\rm next}(M^2)=\frac{1}{2},\qquad N=44\,352$',

 'The unique sextic in the recovered basis':r'$F_6=x^6+y^6+z^6+A(x^4y^2+y^4z^2+z^4x^2)+B(x^2y^4+y^2z^4+z^2x^4)+Dx^2y^2z^2$',
 'Three light modes and canonical projectors':r'$K_f=I+A_f^{\dagger}A_f,\quad Y_f=-h_fA_fK_f^{-1/2},\quad |V_{ij}|^2=\operatorname{Tr}(P_i^uP_j^d)$',
 'The original exact carrier and energy winner':r'$V_{\rm lock}^{\prime}(x)=P(x)\,[2\lambda P^{\prime}(x)+\eta Q(x)]$',
 'A precise scalar-loop obstruction':r'$h(x)=(4-x^2)V^{\prime\prime}(x)-xV^{\prime}(x),\qquad \gcd(P,(h^2)^{\prime})=1$',
 'Finite scalar-loop displacements':r'$\Delta V=\frac{m^4}{64\pi^2}\left[\log\frac{m^2}{\mu^2}-\frac{3}{2}\right],\qquad \Delta\theta=-\frac{\Delta U^{\prime}}{U^{\prime\prime}}$',
 'A cubic supersymmetric constraint circuit':r'$z_n=z^n,\qquad \Phi_{60}(z)=z^{16}+z^{14}-z^{10}-z^8-z^6+z^2+1=0$',
 'A holomorphic golden-coefficient extension':r'$T=2-z^4-z^6+z^{14},\qquad T^2-3T+1=0$',
 'Full-circuit leading quantum calculation':r'$A=J^{\dagger}J,\qquad B=\sum_k\overline{F_k}\,H_k$',
 'A derived texture counterexample':r'$V_{\rm CKM}=U_u^{\dagger}U_d,\qquad U_f^{\dagger}Y_fY_f^{\dagger}U_f={\rm diag}(y_f^2)$',
 'Scale evolution as a separate matching test':r'$16\pi^2\,\frac{dY_u}{d\log\mu}=\left[\frac{3}{2}(H_u-H_d)+\alpha_u I\right]Y_u$',
 'The exact observable target':r'$C_{\rm eff}=\frac{w(1-w^2)}{uv}=\phi^{-2}$',
 'Canonical tree matching without a small-flavon expansion':r'$A=M^{-1}L,\qquad K=I+A^{\dagger}A,\qquad Y=-h A K^{-1/2}$',
 'A rational global certificate for the orientation obstruction':r'$E=\sum_i\alpha_i+\sum_j\beta_j+\sum_{ij}R_{ij}B_{ij}\geq E_{\rm permutation}$',
 'Exact scalar identity and the 42-cap component':r'$B^2=X+6I,\qquad B^3=4X+11B+6D$',
 'A canonical decorated transport':r'$\Omega=\frac{E G_2}{\sqrt{5}},\qquad \Omega^2=I,\qquad \Omega T=-T\Omega$',
 'What edge symmetry actually enforces':r'$\dim\operatorname{Hom}_{D_5}(3,3^t)=1,\qquad \dim\operatorname{Hom}_{D_5}(3,{3\prime}^t)=2$',
 'An explicit protected alignment interaction':r'$J_{v,s}=(-1)^s\Omega_v,\qquad P_\pm=\frac{I\pm J}{2}$',
 'Exact complex-triplet residual gap':r'$|V_{ij}|\in\{0\}\cup[0.0759431758\ldots,\,0.9566183482\ldots]\cup\{1\}$',
 'Partial residuals and the fixed-line obstruction':r'$|V_{ij}|^2\in\left\{0,\frac{3-\sqrt{5}}{8},\frac{1}{4},\frac{1}{2},\frac{3+\sqrt{5}}{8},1\right\}$'}


def equation_image(expression):
    fig=plt.figure(figsize=(7.0,.55))
    fig.text(.02,.44,expression,fontsize=12,va='center',color='#123d58')
    data=BytesIO(); fig.savefig(data,format='png',dpi=260,bbox_inches='tight',pad_inches=.05,transparent=True)
    plt.close(fig);data.seek(0)
    width,height=ImageReader(data).getSize()
    return Image(data,width=min(470,width*72/260),height=height*72/260)


def main():
    import argparse
    parser=argparse.ArgumentParser()
    parser.add_argument('--transport-paper',action='store_true')
    parser.add_argument('--invariant-paper',action='store_true')
    parser.add_argument('--joint-paper',action='store_true')
    parser.add_argument('--kinetic-paper',action='store_true')
    parser.add_argument('--adjoint-paper',action='store_true')
    parser.add_argument('--canonical-paper',action='store_true')
    parser.add_argument('--quantum-paper',action='store_true')
    parser.add_argument('--hermitian-paper',action='store_true')
    parser.add_argument('--electromagnetic-paper',action='store_true')
    parser.add_argument('--nonet-paper',action='store_true')
    parser.add_argument('--mediator-closure-paper',action='store_true')
    parser.add_argument('--frontier-paper',action='store_true')
    parser.add_argument('--spectral-paper',action='store_true')
    parser.add_argument('--functional-paper',action='store_true')
    parser.add_argument('--singlet-paper',action='store_true')
    parser.add_argument('--cp-paper',action='store_true')
    parser.add_argument('--susy-paper',action='store_true')
    parser.add_argument('--diagonal-paper',action='store_true')
    parser.add_argument('--selection-paper',action='store_true')
    args=parser.parse_args()
    standalone=args.selection_paper or args.diagonal_paper or args.transport_paper or args.invariant_paper or args.cp_paper or args.susy_paper or args.joint_paper or args.kinetic_paper or args.adjoint_paper or args.canonical_paper or args.quantum_paper or args.hermitian_paper or args.electromagnetic_paper or args.nonet_paper or args.mediator_closure_paper or args.frontier_paper or args.spectral_paper or args.functional_paper or args.singlet_paper
    destination=ROOT/'output/pdf/M22_Triplet_Transport_and_CKM_Obstructions.pdf' if standalone else DEST
    if args.invariant_paper:destination=ROOT/'output/pdf/Valentiner_Invariant_Interactions.pdf'
    if args.cp_paper:destination=ROOT/'output/pdf/Valentiner_CP_and_Global_Modes.pdf'
    if args.susy_paper:destination=ROOT/'output/pdf/Valentiner_SUSY_Vacua_and_CKM_Boundary.pdf'
    if args.adjoint_paper:destination=ROOT/'output/pdf/Valentiner_Rank_Lifting_and_Physical_CP.pdf'
    if args.quantum_paper:destination=ROOT/'output/pdf/Valentiner_Electroweak_Quantum_and_Spectra.pdf'
    if args.canonical_paper:destination=ROOT/'output/pdf/Valentiner_Canonical_Quarks_and_Strong_CP.pdf'
    if args.kinetic_paper:destination=ROOT/'output/pdf/CP_Even_Kinetic_Freedom_at_Fixed_Masses.pdf'
    if args.joint_paper:destination=ROOT/'output/pdf/Valentiner_Joint_Potential_and_Protection.pdf'
    if args.hermitian_paper:destination=ROOT/'output/pdf/Hermitian_Flavor_and_One_Loop_CP.pdf'
    if args.electromagnetic_paper:destination=ROOT/'output/pdf/Sommerfeld_Constant_and_66_Degrees.pdf'
    if args.nonet_paper:destination=ROOT/'output/pdf/Valentiner_Nonet_Joint_Potential_and_CKM_Geometry.pdf'
    if args.mediator_closure_paper:destination=ROOT/'output/pdf/Valentiner_Soft_Mediation_and_Scalar_Loop_Closure.pdf'
    if args.frontier_paper:destination=ROOT/'output/pdf/Flavor_Exact_Tensors_Running_and_Vacuum_Selection.pdf'
    if args.spectral_paper:destination=ROOT/'output/pdf/Flavor_Finite_Spectral_Matching_and_Phase_Protection.pdf'
    if args.functional_paper:destination=ROOT/'output/pdf/Flavor_Functional_Masses_and_Exact_Operator_Mixing.pdf'
    if args.singlet_paper:destination=ROOT/'output/pdf/Flavor_Singlet_Mediation_and_Protected_Operator_Modules.pdf'
    DEST.parent.mkdir(parents=True,exist_ok=True)
    fontroot=Path('/usr/share/fonts/truetype/dejavu')
    for name,filename in (('Body','DejaVuSerif.ttf'),('BodyBold','DejaVuSerif-Bold.ttf'),('Sans','DejaVuSans.ttf'),('SansBold','DejaVuSans-Bold.ttf')):
        pdfmetrics.registerFont(TTFont(name,str(fontroot/filename)))
    styles=getSampleStyleSheet()
    body=ParagraphStyle('ReaderBody',fontName='Body',fontSize=9.3 if args.functional_paper or args.singlet_paper else 9.5,leading=13.2 if args.functional_paper or args.singlet_paper else 14.0,spaceAfter=8,textColor=HexColor('#1d2933'))
    heading=ParagraphStyle('ReaderHeading',fontName='SansBold',fontSize=13.3,leading=17,spaceBefore=15,spaceAfter=9,textColor=HexColor('#123d58'),keepWithNext=True)
    title=ParagraphStyle('ReaderTitle',fontName='SansBold',fontSize=27,leading=34,textColor=HexColor('#123d58'),spaceAfter=20)
    subtitle=ParagraphStyle('ReaderSubtitle',fontName='Sans',fontSize=13.3,leading=20,textColor=HexColor('#43586b'),spaceAfter=15)
    story=[Spacer(1,68),Paragraph('Flavor interactions,<br/>physical CP and<br/>exact constraint geometry',title),
        Paragraph('Finite symmetries, canonical quark matching, soft mediation and coupled one-loop evolution',subtitle),
        Spacer(1,25),Paragraph('PerfectPower research monograph<br/>6 October 2026 (UTC)',subtitle),Spacer(1,25),
        Paragraph('A declared Hermitian-source action supports finite hierarchical matching and physical weak CP with termwise one-loop mass-phase protection. Locally stable branches, exact invariant constraints, CP operator counts and coupled one-loop evolution are executable. A resolved lower CP-conserving competitor now establishes the selection boundary for the retained minimal branch.',body),
        Paragraph('Exact representation and polynomial results are distinguished from numerical vacuum calculations. The constructed interactions protect their stated structures; the golden CKM coefficient and physical 66-degree phase remain unpredicted.',body),PageBreak()]
    if standalone:
        story=[Spacer(1,45),Paragraph('Triplet transport on<br/>M22 cap geometry',title),
            Paragraph('Exact transport obstructions, an orientation-cover alignment interaction and certified quark residual gaps',subtitle),
            Spacer(1,18),Paragraph('PerfectPower research draft / 5 October 2026',subtitle),
            Paragraph('Mathematical results with reproducible certificates. Publication novelty and the particle-physics interpretation require independent review. The nominated golden CKM coefficient and 66-degree phase are not derived.',body),PageBreak()]
    if args.invariant_paper:
        story=[Spacer(1,45),Paragraph('Valentiner invariant<br/>interactions',title),Paragraph('A fixed sextic tensor, three light families and an allowed-deformation test',subtitle),Spacer(1,20),Paragraph('PerfectPower research draft / 6 October 2026',subtitle),Paragraph('The invariant and matching results are exact. Local vacuum response is numerical. The golden CKM relation and physical CP phase remain underived.',body),PageBreak()]
    if args.cp_paper:
        story=[Spacer(1,45),Paragraph('Cross-sector links,<br/>physical CP and<br/>global cap modes',title),Paragraph('Exact elementary CP, representation-derived alignment and a complete conditional mass spectrum',subtitle),Spacer(1,20),Paragraph('PerfectPower research draft / 6 October 2026',subtitle),Paragraph('The product symmetry removes a quartic deformation. Higher-degree mixed interactions, physical vacuum selection and the global chiral completion remain open.',body),PageBreak()]
    if args.susy_paper:
        story=[Spacer(1,45),Paragraph('Supersymmetric links,<br/>stable source vacua and<br/>the CKM boundary',title),Paragraph('An isolated alignment branch, physical weak CP and an exact orthogonal-frame obstruction',subtitle),Spacer(1,20),Paragraph('PerfectPower research draft / 6 October 2026 (UTC)',subtitle),Paragraph('Joint local vacua are calculated without a nominated angle. The orthogonal axis branch fails the observed hierarchy. Global selection, operator protection and a golden CKM relation remain open.',body),PageBreak()]
    if args.joint_paper:
        story=[Spacer(1,45),Paragraph('The joint potential,<br/>nonorthogonal vacua and<br/>the protection test',title),Paragraph('263 allowed scalar contractions, physical weak CP and four independent observable directions',subtitle),Spacer(1,20),Paragraph('PerfectPower research draft / 6 October 2026 (UTC)',subtitle),Paragraph('Fully minimized nonorthogonal vacua escape the orthogonal-frame bound. Independent couplings still move all four mixing observables. Observed CKM values and the golden relation are not predicted.',body),PageBreak()]
    if args.kinetic_paper:
        story=[Spacer(1,45),Paragraph('CP-even kinetic freedom<br/>at fixed quark masses',title),Paragraph('Nine polynomial covariants, positive metrics and exact heavy-mediator matching',subtitle),Spacer(1,20),Paragraph('PerfectPower research draft / 6 October 2026 (UTC)',subtitle),Paragraph('A constructive operator-space theorem with fixed-spectrum countermetrics, a shared non-Abelian source label and a stable heavy-family branch.',body),PageBreak()]
    if args.adjoint_paper:
        story=[Spacer(1,45),Paragraph('Universal source couplings,<br/>three-family rank lifting<br/>and physical CP',title),Paragraph('A stable 70-field vacuum, complete mediator contractions and canonical quark matching',subtitle),Spacer(1,20),Paragraph('PerfectPower research draft / 6 October 2026 (UTC)',subtitle),Paragraph('A specified CP-even interaction produces six nonzero quark masses and physical weak CP without a target angle. The scalar slice is complete through degree four; an observed CKM fit and exact golden protection remain open.',body),PageBreak()]
    if args.canonical_paper:
        story=[Spacer(1,45),Paragraph('Canonical quarks,<br/>physical currents and<br/>strong CP',title),Paragraph('A representation-enforced Nelson–Barr assignment with a shared adjoint and fixed mixing frames',subtitle),Spacer(1,20),Paragraph('PerfectPower research draft / 6 October 2026 (UTC)',subtitle),Paragraph('Tree determinant protection and exact canonical matching at a specified flavor vacuum. Higher operators, quantum strong CP, observed flavor fits and golden protection remain separate requirements.',body),PageBreak()]
    if args.quantum_paper:
        story=[Spacer(1,45),Paragraph('Electroweak completion,<br/>one-loop strong CP<br/>and flavor spectra',title),Paragraph('A stable joint branch, 156 exact fermion covariants and constructive hierarchical matching',subtitle),Spacer(1,20),Paragraph('PerfectPower research draft / 6 October 2026 (UTC)',subtitle),Paragraph('Completed calculations with explicit action, coefficient inputs, precision checks and reproducible scientific receipts.',body),PageBreak()]
    if args.hermitian_paper:
        story=[Spacer(1,45),Paragraph('Hermitian flavor sources<br/>and exact one-loop<br/>mass-phase cancellation',title),Paragraph('A complete canonical fermion action, finite hierarchical matching and an exact covariant determinant',subtitle),Spacer(1,20),Paragraph('PerfectPower research draft / 6 October 2026 (UTC)',subtitle),Paragraph('Termwise one-loop protection with arbitrary real scalar mixing. Explicit source-center inputs, locally positive scalar EFT and a complete mass-only affine candidate calculation.',body),PageBreak()]
    if args.electromagnetic_paper:
        story=[Spacer(1,45),Paragraph('The Sommerfeld constant<br/>and the exact<br/>66-degree angle carrier',title),Paragraph('Electromagnetic spectral invariance, a determinant threshold sum rule and the gauge boundary',subtitle),Spacer(1,20),Paragraph('PerfectPower research draft / 6 October 2026 (UTC)',subtitle),Paragraph('An exact golden-coefficient identity and a continuous weak-phase orbit at fixed one-loop photon screening. Explicit separation of electromagnetic coupling inputs, scalar angles and physical CP.',body),PageBreak()]
    if args.nonet_paper:
        story=[Spacer(1,45),Paragraph('Complete nonet interactions<br/>and invariant<br/>CKM geometry',title),Paragraph('A bounded 70-coefficient action, stable physical CP and mass-preserving coupling response',subtitle),Spacer(1,20),Paragraph('PerfectPower research draft / 6 October 2026 (UTC)',subtitle),Paragraph('Exact operator counts and target equations, numerical isolated vacua and finite-deformation checks. The full allowed action retains four adjustable mixing directions.',body),PageBreak()]
    if args.mediator_closure_paper:
        story=[Spacer(1,45),Paragraph('Soft mediation,<br/>scalar-loop closure<br/>and protected flavor',title),Paragraph('A stable 48-scalar completion, exact CP operator census and representation-enforced coefficient relations',subtitle),Spacer(1,20),Paragraph('PerfectPower research draft / 6 October 2026 (UTC)',subtitle),Paragraph('Complete mediator and fixed-mass calculations with explicit Gaussian inputs. Scalar-loop closure and fermion protection are established within their stated scopes; golden flavor is not predicted.',body),PageBreak()]
    if args.frontier_paper:
        story=[Spacer(1,45),Paragraph('Exact flavor tensors,<br/>coupled running and<br/>mechanism selection',title),Paragraph('1,891 exact quartic products, finite-mass hierarchy exclusion and a CP-quality interaction',subtitle),Spacer(1,20),Paragraph('PerfectPower research draft / 6 October 2026 (UTC)',subtitle),Paragraph('A specified 92-parameter one-loop system, canonical scalar matching, finite-mass kinetic response and resolved vacuum comparisons. Exact certificates and numerical benchmark conclusions retain separate scopes.',body),PageBreak()]
    if args.spectral_paper:
        story=[Spacer(1,45),Paragraph('Finite scalar matching,<br/>higher determinant phases<br/>and sequestering',title),Paragraph('Exact Gaussian poles and residues, a neutral-scalar protection criterion and correlated wall metrics',subtitle),Spacer(1,20),Paragraph('PerfectPower research draft / 6 October 2026 (UTC)',subtitle),Paragraph('Finite UV matching and reproducible phase counterexamples with explicit loop-order scope. Includes an exact bridge to the merged conditional cosmology tools.',body),PageBreak()]
    if args.functional_paper:
        story=[Spacer(1,45),Paragraph('Functional heavy masses,<br/>hierarchical quarks and<br/>exact operator mixing',title),Paragraph('A single-source phase theorem, a positive finite hierarchy and the radiative correlation test',subtitle),Spacer(1,20),Paragraph('PerfectPower research draft / 6 October 2026 (UTC)',subtitle),Paragraph('Exact character and scalar-loop tensor identities with reproducible finite matching. Polynomial source inputs and a protected EFT slice are explicit; golden flavor and a complete UV completion are not predicted.',body),PageBreak()]
    if args.singlet_paper:
        story=[Spacer(1,45),Paragraph('Singlet-mediated masses,<br/>protected operator modules<br/>and frame interactions',title),Paragraph('A complete 49-scalar CP benchmark, exact mass-coefficient correlations and all rotated linear restrictions',subtitle),Spacer(1,20),Paragraph('PerfectPower research draft / 6 October 2026 (UTC)',subtitle),Paragraph('Representation-based fermion interactions, exact scalar insertion maps, Gaussian matching and finite canonical poles. A local physical CP vacuum is retained; the golden frame and global selection are not predicted.',body),PageBreak()]
    if args.diagonal_paper:
        destination=ROOT/'output/pdf/Valentiner_Diagonal_Vacuum_Census.pdf'
        story=[Spacer(1,45),Paragraph('Exact diagonal link vacua<br/>and full-field stability',title),Paragraph('109 diagonal vacua, algebraic mass certificates and a concrete alignment competitor',subtitle),Spacer(1,20),Paragraph('PerfectPower research / 8 October 2026 (UTC)',subtitle),Paragraph('A complete diagonal classification in the specified canonical link action. The original sextic tensor certifies transverse stability of a nonunitary competitor; a universal scalar mass supplies an exact first-order selection test.',body),PageBreak()]
    if args.selection_paper:
        destination=ROOT/'output/pdf/Valentiner_Frame_Selection_and_Nonlinear_Vacua.pdf'
        story=[Spacer(1,45),Paragraph('Global frame selection<br/>and nonlinear link vacua',title),Paragraph('A permitted soft selector, a global quartic theorem and exact off-diagonal orbit certificates',subtitle),Spacer(1,20),Paragraph('PerfectPower research / 8 October 2026 (UTC)',subtitle),Paragraph('The isolated link action admits a global unitary tensor-frame selection theorem. A complete certified finite-orbit census and massive-field relaxation expose the scale of its competing vacuum structure.',body),PageBreak()]
    selected_source=SOURCES[-1] if args.selection_paper else SOURCES[-2] if args.diagonal_paper else SOURCES[21] if args.singlet_paper else SOURCES[20] if args.functional_paper else SOURCES[19] if args.spectral_paper else SOURCES[17] if args.frontier_paper else SOURCES[16] if args.mediator_closure_paper else SOURCES[15] if args.nonet_paper else SOURCES[14] if args.electromagnetic_paper else SOURCES[13] if args.hermitian_paper else SOURCES[12] if args.quantum_paper else SOURCES[11] if args.canonical_paper else SOURCES[10] if args.adjoint_paper else SOURCES[9] if args.kinetic_paper else SOURCES[8] if args.joint_paper else SOURCES[7] if args.susy_paper else SOURCES[5] if args.cp_paper else SOURCES[4] if args.invariant_paper else SOURCES[3]
    text='\n\nCHAPTER_BREAK\n\n'.join(p.read_text() for p in ([selected_source] if standalone else SOURCES))
    chapter_titles=iter(['Shared mediators and the alignment boundary', 'Recovered M22 geometry and the flavor frame','Triplet transport and exact residual obstructions','Valentiner interactions and the protection boundary','Product-family CP and the global spectrum','Audit of the flavor search inputs','Supersymmetric vacua and the CKM boundary','The joint potential and the protection test','CP-even kinetic freedom at fixed quark masses','Universal sources, rank lifting and physical CP','Canonical quarks, currents and strong CP','Electroweak completion, quantum matching and attainable spectra','Hermitian sources and exact one-loop mass-phase cancellation','The Sommerfeld constant and the exact angle carrier','Complete nonet interactions and invariant CKM geometry','Soft mediation, scalar-loop closure and protected flavor','Exact flavor tensors, running and mechanism selection','Metastable tree decay and conditional CP walls','Finite scalar matching and the phase-protection criterion','Functional masses and exact cross-source operator mixing','Singlet-mediated masses and protected operator modules','Quantum-generated singlet interactions and canonical matching','Scalar quantum frame forces and a stable weak continuation','Fixed gauge feedback and the Goldstone Ward boundary','Analytic radial geometry and source response','Exact diagonal link vacua and full-field stability','Frame selection and nonlinear off-diagonal vacua'])
    for block in text.split('\n\n'):
        block=block.strip()
        if block=='CHAPTER_BREAK':
            story.append(PageBreak())
            chapter_label=next(chapter_titles)
            story.append(Paragraph(chapter_label,title))
            if chapter_label in ['Functional masses and exact cross-source operator mixing','Singlet-mediated masses and protected operator modules']:
                body=ParagraphStyle('FunctionalBody',parent=body,fontSize=9.3,leading=13.2)
            continue
        if not block or block.startswith('# '):continue
        if block.startswith('## '):
            label=block[3:].strip()
            story.append(Paragraph(escape(label),heading))
            if label in EQUATIONS:
                story.append(equation_image(EQUATIONS[label]));story.append(Spacer(1,5))
        elif block.startswith('\\[') and block.endswith('\\]'):
            story.append(equation_image('$'+block[2:-2].strip()+'$'));story.append(Spacer(1,6))
        elif block.startswith('!['):
            match=re.search(r'\]\(([^)]+)\)',block)
            path=(SOURCE.parent/match.group(1)).resolve()
            width,height=ImageReader(str(path)).getSize()
            story.append(Image(str(path),width=475,height=475*height/width));story.append(Spacer(1,10))
        elif block.startswith('|'):
            rows=[]
            cellstyle=ParagraphStyle('TableCell',parent=body,fontSize=7,leading=10,spaceAfter=0)
            for line in block.splitlines():
                cells=[t.strip().replace('`','') for t in line.strip().strip('|').split('|')]
                if all(set(t)<=set('-: ') for t in cells):continue
                rows.append([Paragraph(escape(t),cellstyle) for t in cells])
            table=LongTable(rows,colWidths=[150,137,190],repeatRows=1,hAlign='LEFT')
            table.setStyle(TableStyle([('VALIGN',(0,0),(-1,-1),'TOP'),('BACKGROUND',(0,0),(-1,0),HexColor('#e4edf3')),('LINEBELOW',(0,0),(-1,0),.6,HexColor('#506372')),('LINEBELOW',(0,1),(-1,-1),.25,HexColor('#c2ced7')),('LEFTPADDING',(0,0),(-1,-1),5),('RIGHTPADDING',(0,0),(-1,-1),5),('TOPPADDING',(0,0),(-1,-1),5),('BOTTOMPADDING',(0,0),(-1,-1),5)]))
            if len(rows)<=8:story.append(KeepTogether([table,Spacer(1,12)]))
            else:story.extend([table,Spacer(1,12)])
        else:
            content=escape(' '.join(block.splitlines()))
            story.append(Paragraph(content,body))
    def furniture(canvas,doc):
        canvas.saveState()
        canvas.setStrokeColor(HexColor('#c2ced7'));canvas.line(58,47,537,47)
        canvas.setFont('Sans',8);canvas.setFillColor(HexColor('#506372'))
        canvas.drawString(58,33,'PERFECTPOWER / FRAME SELECTION AND NONLINEAR VACUA' if args.selection_paper else 'PERFECTPOWER / DIAGONAL LINK VACUA' if args.diagonal_paper else 'PERFECTPOWER / SINGLET MEDIATION AND OPERATOR MODULES' if args.singlet_paper else 'PERFECTPOWER / FUNCTIONAL MASSES AND OPERATOR MIXING' if args.functional_paper else 'PERFECTPOWER / FINITE MATCHING AND PHASE PROTECTION' if args.spectral_paper else 'PERFECTPOWER / EXACT TENSORS AND MECHANISM SELECTION' if args.frontier_paper else 'PERFECTPOWER / SOFT MEDIATION AND SCALAR-LOOP CLOSURE' if args.mediator_closure_paper else 'PERFECTPOWER / NONET INTERACTIONS AND CKM GEOMETRY' if args.nonet_paper else 'PERFECTPOWER / SOMMERFELD CONSTANT AND EXACT ANGLES' if args.electromagnetic_paper else 'PERFECTPOWER / HERMITIAN FLAVOR AND ONE-LOOP CP' if args.hermitian_paper else 'PERFECTPOWER / ELECTROWEAK AND QUANTUM MATCHING' if args.quantum_paper else 'PERFECTPOWER / CANONICAL QUARKS AND STRONG CP' if args.canonical_paper else 'PERFECTPOWER / RANK LIFTING AND PHYSICAL CP' if args.adjoint_paper else 'PERFECTPOWER / CP-EVEN KINETIC FREEDOM' if args.kinetic_paper else 'PERFECTPOWER / JOINT POTENTIAL AND PROTECTION' if args.joint_paper else 'PERFECTPOWER / SUSY VACUA AND CKM BOUNDARY' if args.susy_paper else 'PERFECTPOWER / CP AND GLOBAL MODES' if args.cp_paper else 'PERFECTPOWER / VALENTINER INTERACTIONS' if args.invariant_paper else 'PERFECTPOWER / M22 TRIPLET TRANSPORT' if standalone else 'PERFECTPOWER / FLAVOR MECHANISMS')
        canvas.drawRightString(537,33,str(doc.page))
        if doc.page>1:
            canvas.setFont('Sans',7.5);canvas.drawString(58,806,'Exact equations, declared interactions, computed departures')
        canvas.restoreState()
    doc=SimpleDocTemplate(str(destination),pagesize=(595.28,841.89),leftMargin=58,rightMargin=58,topMargin=54,bottomMargin=62,
        title='Global frame selection and nonlinear link vacua' if args.selection_paper else 'Exact diagonal link vacua and full-field stability' if args.diagonal_paper else 'Singlet-mediated masses and protected operator modules' if args.singlet_paper else 'Functional heavy masses and exact cross-source operator mixing' if args.functional_paper else 'Finite scalar matching, higher determinant phases and sequestering' if args.spectral_paper else 'Exact flavor tensors, coupled running and mechanism selection' if args.frontier_paper else 'Soft mediation, scalar-loop closure and protected flavor' if args.mediator_closure_paper else 'Complete nonet interactions and invariant CKM geometry' if args.nonet_paper else 'The Sommerfeld constant and the exact 66-degree angle carrier' if args.electromagnetic_paper else 'Hermitian flavor sources and exact one-loop mass-phase cancellation' if args.hermitian_paper else 'Electroweak completion, one-loop strong CP and attainable spectra' if args.quantum_paper else 'Canonical quarks, physical currents and strong CP' if args.canonical_paper else 'Universal source couplings, three-family rank lifting and physical CP' if args.adjoint_paper else 'CP-even kinetic freedom at fixed quark masses' if args.kinetic_paper else 'The joint potential, nonorthogonal vacua and the protection test' if args.joint_paper else 'Supersymmetric links, stable source vacua and the CKM boundary' if args.susy_paper else 'Cross-sector links, physical CP and global cap modes' if args.cp_paper else 'Valentiner invariant interactions' if args.invariant_paper else 'Triplet transport on M22 cap geometry' if standalone else 'Flavor mechanisms, vacuum alignment and predictive limits',author='PerfectPower research')
    doc.build(story,onFirstPage=furniture,onLaterPages=furniture)
    # Store actual binary streams instead of a text-like ASCII85 PDF.
    import fitz
    document=fitz.open(destination);compressed=destination.with_suffix('.compressed.pdf')
    document.save(compressed,garbage=4,deflate=True,use_objstms=1);document.close();compressed.replace(destination)
    print(destination)


if __name__=='__main__':main()
