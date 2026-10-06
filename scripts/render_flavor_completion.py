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
SOURCES=[SOURCE,ROOT/'docs/B5_FLAVOR_MEDIATOR.md',ROOT/'docs/M22_FLAVOR_FRAME.md',ROOT/'docs/M22_TRANSPORT_INTERACTIONS.md',ROOT/'docs/VALENTINER_INVARIANT_INTERACTIONS.md',ROOT/'docs/VALENTINER_CP_AND_GLOBAL_MODES.md',ROOT/'docs/FLAVOR_SEARCH_INPUT_AUDIT.md',ROOT/'docs/VALENTINER_SUSY_VACUA.md']
DEST=ROOT/'output/pdf/B5_Protected_Flavor_Monograph.pdf'

EQUATIONS={
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
    parser.add_argument('--cp-paper',action='store_true')
    parser.add_argument('--susy-paper',action='store_true')
    args=parser.parse_args()
    standalone=args.transport_paper or args.invariant_paper or args.cp_paper or args.susy_paper
    destination=ROOT/'output/pdf/M22_Triplet_Transport_and_CKM_Obstructions.pdf' if standalone else DEST
    if args.invariant_paper:destination=ROOT/'output/pdf/Valentiner_Invariant_Interactions.pdf'
    if args.cp_paper:destination=ROOT/'output/pdf/Valentiner_CP_and_Global_Modes.pdf'
    if args.susy_paper:destination=ROOT/'output/pdf/Valentiner_SUSY_Vacua_and_CKM_Boundary.pdf'
    DEST.parent.mkdir(parents=True,exist_ok=True)
    fontroot=Path('/usr/share/fonts/truetype/dejavu')
    for name,filename in (('Body','DejaVuSerif.ttf'),('BodyBold','DejaVuSerif-Bold.ttf'),('Sans','DejaVuSans.ttf'),('SansBold','DejaVuSans-Bold.ttf')):
        pdfmetrics.registerFont(TTFont(name,str(fontroot/filename)))
    styles=getSampleStyleSheet()
    body=ParagraphStyle('ReaderBody',fontName='Body',fontSize=9.5,leading=14.0,spaceAfter=8,textColor=HexColor('#1d2933'))
    heading=ParagraphStyle('ReaderHeading',fontName='SansBold',fontSize=13.3,leading=17,spaceBefore=15,spaceAfter=9,textColor=HexColor('#123d58'),keepWithNext=True)
    title=ParagraphStyle('ReaderTitle',fontName='SansBold',fontSize=27,leading=34,textColor=HexColor('#123d58'),spaceAfter=20)
    subtitle=ParagraphStyle('ReaderSubtitle',fontName='Sans',fontSize=13.3,leading=20,textColor=HexColor('#43586b'),spaceAfter=15)
    story=[Spacer(1,68),Paragraph('Flavor mechanisms,<br/>vacuum alignment and<br/>predictive limits',title),
        Paragraph('Singlet dynamics, exact finite symmetries, canonical quark matching and the input audit',subtitle),
        Spacer(1,25),Paragraph('PerfectPower research monograph<br/>6 October 2026 (UTC)',subtitle),Spacer(1,25),
        Paragraph('The selected model admits controlled vacua near +/-66 degrees. Its initialized equations receive perturbative supersymmetric protection; its energy selection, physical coefficient readout and quark couplings remain separately specified interactions.',body),
        Paragraph('Exact rational results and numerical scenario results are distinguished throughout. The worked construction is conditional and does not claim an independently derived theory of flavor.',body),PageBreak()]
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
    selected_source=SOURCES[7] if args.susy_paper else SOURCES[5] if args.cp_paper else SOURCES[4] if args.invariant_paper else SOURCES[3]
    text='\n\nCHAPTER_BREAK\n\n'.join(p.read_text() for p in ([selected_source] if standalone else SOURCES))
    chapter_titles=iter(['Shared mediators and the alignment boundary', 'Recovered M22 geometry and the flavor frame','Triplet transport and exact residual obstructions','Valentiner interactions and the protection boundary','Product-family CP and the global spectrum','Audit of the flavor search inputs','Supersymmetric vacua and the CKM boundary'])
    for block in text.split('\n\n'):
        block=block.strip()
        if block=='CHAPTER_BREAK':
            story.append(PageBreak())
            story.append(Paragraph(next(chapter_titles),title))
            continue
        if not block or block.startswith('# '):continue
        if block.startswith('## '):
            label=block[3:].strip()
            story.append(Paragraph(escape(label),heading))
            if label in EQUATIONS:
                story.append(equation_image(EQUATIONS[label]));story.append(Spacer(1,5))
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
            story.extend([table,Spacer(1,12)])
        else:
            content=escape(' '.join(block.splitlines()))
            story.append(Paragraph(content,body))
    def furniture(canvas,doc):
        canvas.saveState()
        canvas.setStrokeColor(HexColor('#c2ced7'));canvas.line(58,47,537,47)
        canvas.setFont('Sans',8);canvas.setFillColor(HexColor('#506372'))
        canvas.drawString(58,33,'PERFECTPOWER / SUSY VACUA AND CKM BOUNDARY' if args.susy_paper else 'PERFECTPOWER / CP AND GLOBAL MODES' if args.cp_paper else 'PERFECTPOWER / VALENTINER INTERACTIONS' if args.invariant_paper else 'PERFECTPOWER / M22 TRIPLET TRANSPORT' if standalone else 'PERFECTPOWER / FLAVOR MECHANISMS')
        canvas.drawRightString(537,33,str(doc.page))
        if doc.page>1:
            canvas.setFont('Sans',7.5);canvas.drawString(58,806,'Exact equations, declared interactions, computed departures')
        canvas.restoreState()
    doc=SimpleDocTemplate(str(destination),pagesize=(595.28,841.89),leftMargin=58,rightMargin=58,topMargin=54,bottomMargin=62,
        title='Supersymmetric links, stable source vacua and the CKM boundary' if args.susy_paper else 'Cross-sector links, physical CP and global cap modes' if args.cp_paper else 'Valentiner invariant interactions' if args.invariant_paper else 'Triplet transport on M22 cap geometry' if standalone else 'Flavor mechanisms, vacuum alignment and predictive limits',author='PerfectPower research')
    doc.build(story,onFirstPage=furniture,onLaterPages=furniture)
    print(destination)


if __name__=='__main__':main()
