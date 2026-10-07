"""Render the standalone quantum singlet paper from its complete source."""
from pathlib import Path
from xml.sax.saxutils import escape
from reportlab.platypus import SimpleDocTemplate,Paragraph,Spacer
from reportlab.lib.styles import ParagraphStyle
from reportlab.lib.colors import HexColor
ROOT=Path(__file__).resolve().parents[1]

def main():
    destination=ROOT/'output/pdf/Flavor_Scalar_Feedback_and_Weak_Continuation.pdf'
    title=ParagraphStyle('Title',fontName='Helvetica-Bold',fontSize=21,leading=25,textColor=HexColor('#123d56'),spaceAfter=16)
    heading=ParagraphStyle('Heading',fontName='Helvetica-Bold',fontSize=12,leading=15,textColor=HexColor('#123d56'),spaceBefore=13,spaceAfter=7,keepWithNext=True)
    body=ParagraphStyle('Body',fontName='Times-Roman',fontSize=9.5,leading=12.2,spaceAfter=6)
    story=[]
    for block in (ROOT/'docs/FLAVOR_SCALAR_FEEDBACK_AND_WEAK_CONTINUATION.md').read_text().split('\n\n'):
        if block.startswith('# '):story.extend([Paragraph(escape(block[2:]),title),Paragraph('PerfectPower research / 7 October 2026 / Full scalar frame forces and controlled local quantum branch',body),Spacer(1,8)])
        elif block.startswith('## '):story.append(Paragraph(escape(block[3:]),heading))
        else:story.append(Paragraph(escape(' '.join(block.splitlines())),body))
    def furniture(canvas,doc):
        canvas.setFont('Helvetica',8);canvas.setFillColor(HexColor('#506372'))
        canvas.drawString(52,28,'PERFECTPOWER / SCALAR FEEDBACK AND WEAK CONTINUATION');canvas.drawRightString(543,28,str(doc.page))
    SimpleDocTemplate(str(destination),pagesize=(595.28,841.89),leftMargin=52,rightMargin=52,topMargin=45,bottomMargin=47,title='Scalar quantum feedback and weak continuation',author='PerfectPower research').build(story,onFirstPage=furniture,onLaterPages=furniture)
    print(destination)

if __name__=='__main__':main()
