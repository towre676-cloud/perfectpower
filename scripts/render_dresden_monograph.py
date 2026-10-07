"""Optional reportlab renderer; not a core runtime dependency."""
from pathlib import Path
from html import escape
import re
from reportlab.pdfgen import canvas
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.lib import colors
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont

ROOT=Path(__file__).resolve().parents[1]
FONT=Path('/usr/share/fonts/truetype/dejavu')
pdfmetrics.registerFont(TTFont('DresdenBody',str(FONT/'DejaVuSans.ttf')))
pdfmetrics.registerFont(TTFont('DresdenBold',str(FONT/'DejaVuSans-Bold.ttf')))
styles=getSampleStyleSheet()
styles.add(ParagraphStyle('DresdenBody',fontName='DresdenBody',fontSize=9.4,leading=14.5,spaceAfter=10,allowWidows=0,allowOrphans=0,textColor=colors.HexColor('#203040')))
styles.add(ParagraphStyle('DresdenTitle',fontName='DresdenBold',fontSize=23,leading=28,spaceAfter=18,textColor=colors.HexColor('#123a4b')))
styles.add(ParagraphStyle('DresdenHeading',fontName='DresdenBold',fontSize=13,leading=18,spaceBefore=14,spaceAfter=8,textColor=colors.HexColor('#123a4b'),keepWithNext=True))
story=[]
for block in (ROOT/'docs/DRESDEN_NUMERICAL_MONOGRAPH.md').read_text().split('\n\n'):
    if not block.strip():continue
    style='DresdenTitle' if block.startswith('# ') else 'DresdenHeading' if block.startswith('## ') else 'DresdenBody'
    text=escape(re.sub(r'^#+ ','',block.strip()).replace('`',''))
    story.append(Paragraph(text,styles[style]))

def footer(c,doc):
    c.setStrokeColor(colors.HexColor('#b4c4c9'));c.line(46,42,549,42)
    c.setFont('DresdenBody',8);c.setFillColor(colors.HexColor('#526773'))
    c.drawString(46,28,'PerfectPower | Dresden numerical research | 7 October 2026')
    c.drawRightString(549,28,str(doc.page))

class FixedCanvas(canvas.Canvas):
    def __init__(self,*args,**kwargs):
        kwargs['invariant']=1
        super().__init__(*args,**kwargs)

out=ROOT/'docs/DRESDEN_NUMERICAL_MONOGRAPH.pdf'
SimpleDocTemplate(str(out),pagesize=(595,842),rightMargin=46,leftMargin=46,topMargin=44,bottomMargin=57,
                  title='Dresden numerical research with PerfectPower',author='PerfectPower').build(story,onFirstPage=footer,onLaterPages=footer,canvasmaker=FixedCanvas)
print(out)
