"""Create the reader PDF from the complete Markdown monograph and receipts."""
from pathlib import Path
from io import BytesIO
from xml.sax.saxutils import escape
import re
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Image, PageBreak, KeepTogether
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.lib.colors import HexColor
from reportlab.lib.enums import TA_LEFT
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.lib.utils import ImageReader

ROOT=Path(__file__).resolve().parents[1]
SOURCE=ROOT/'docs/B5_FLAVOR_COMPLETION.md'
DEST=ROOT/'output/pdf/B5_Protected_Flavor_Monograph.pdf'

EQUATIONS={
 'The original exact carrier and energy winner':r'$V_{\rm lock}^{\prime}(x)=P(x)\,[2\lambda P^{\prime}(x)+\eta Q(x)]$',
 'A precise scalar-loop obstruction':r'$h(x)=(4-x^2)V^{\prime\prime}(x)-xV^{\prime}(x),\qquad \gcd(P,(h^2)^{\prime})=1$',
 'Finite scalar-loop displacements':r'$\Delta V=\frac{m^4}{64\pi^2}\left[\log\frac{m^2}{\mu^2}-\frac{3}{2}\right],\qquad \Delta\theta=-\frac{\Delta U^{\prime}}{U^{\prime\prime}}$',
 'A cubic supersymmetric constraint circuit':r'$z_n=z^n,\qquad \Phi_{60}(z)=z^{16}+z^{14}-z^{10}-z^8-z^6+z^2+1=0$',
 'A holomorphic golden-coefficient extension':r'$T=2-z^4-z^6+z^{14},\qquad T^2-3T+1=0$',
 'Full-circuit leading quantum calculation':r'$A=J^{\dagger}J,\qquad B=\sum_k\overline{F_k}\,H_k$',
 'A derived texture counterexample':r'$V_{\rm CKM}=U_u^{\dagger}U_d,\qquad U_f^{\dagger}Y_fY_f^{\dagger}U_f={\rm diag}(y_f^2)$',
 'Scale evolution as a separate matching test':r'$16\pi^2\,\frac{dY_u}{d\log\mu}=\left[\frac{3}{2}(H_u-H_d)+\alpha_u I\right]Y_u$'}


def equation_image(expression):
    fig=plt.figure(figsize=(7.0,.55))
    fig.text(.02,.44,expression,fontsize=12,va='center',color='#123d58')
    data=BytesIO(); fig.savefig(data,format='png',dpi=260,bbox_inches='tight',pad_inches=.05,transparent=True)
    plt.close(fig);data.seek(0)
    width,height=ImageReader(data).getSize()
    return Image(data,width=min(470,width*72/260),height=height*72/260)


def main():
    DEST.parent.mkdir(parents=True,exist_ok=True)
    fontroot=Path('/usr/share/fonts/truetype/dejavu')
    for name,filename in (('Body','DejaVuSerif.ttf'),('BodyBold','DejaVuSerif-Bold.ttf'),('Sans','DejaVuSans.ttf'),('SansBold','DejaVuSans-Bold.ttf')):
        pdfmetrics.registerFont(TTFont(name,str(fontroot/filename)))
    styles=getSampleStyleSheet()
    body=ParagraphStyle('ReaderBody',fontName='Body',fontSize=9.7,leading=14.4,spaceAfter=9,textColor=HexColor('#1d2933'))
    heading=ParagraphStyle('ReaderHeading',fontName='SansBold',fontSize=13.3,leading=17,spaceBefore=15,spaceAfter=9,textColor=HexColor('#123d58'),keepWithNext=True)
    title=ParagraphStyle('ReaderTitle',fontName='SansBold',fontSize=27,leading=34,textColor=HexColor('#123d58'),spaceAfter=20)
    subtitle=ParagraphStyle('ReaderSubtitle',fontName='Sans',fontSize=13.3,leading=20,textColor=HexColor('#43586b'),spaceAfter=15)
    story=[Spacer(1,68),Paragraph('Protected equations,<br/>selected vacua and a<br/>quark-operator obstruction',title),
        Paragraph('An explicit 34-field singlet construction, complete declared operator spaces and leading quantum corrections',subtitle),
        Spacer(1,25),Paragraph('PerfectPower research monograph<br/>5 October 2026',subtitle),Spacer(1,25),
        Paragraph('The selected model admits controlled vacua near +/-66 degrees. Its initialized equations receive perturbative supersymmetric protection; its energy selection, physical coefficient readout and quark couplings remain separately specified interactions.',body),
        Paragraph('Exact rational results and numerical scenario results are distinguished throughout. The worked construction is conditional and does not claim an independently derived theory of flavor.',body),PageBreak()]
    text=SOURCE.read_text()
    for block in text.split('\n\n'):
        block=block.strip()
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
        else:
            content=escape(' '.join(block.splitlines()))
            story.append(Paragraph(content,body))
    def furniture(canvas,doc):
        canvas.saveState()
        canvas.setStrokeColor(HexColor('#c2ced7'));canvas.line(58,47,537,47)
        canvas.setFont('Sans',8);canvas.setFillColor(HexColor('#506372'))
        canvas.drawString(58,33,'PERFECTPOWER / PROTECTED FLAVOR CONSTRUCTION')
        canvas.drawRightString(537,33,str(doc.page))
        if doc.page>1:
            canvas.setFont('Sans',7.5);canvas.drawString(58,806,'Exact equations, declared interactions, computed departures')
        canvas.restoreState()
    doc=SimpleDocTemplate(str(DEST),pagesize=(595.28,841.89),leftMargin=58,rightMargin=58,topMargin=54,bottomMargin=62,
        title='Protected equations, selected vacua and a quark-operator obstruction',author='PerfectPower research')
    doc.build(story,onFirstPage=furniture,onLaterPages=furniture)
    print(DEST)


if __name__=='__main__':main()
