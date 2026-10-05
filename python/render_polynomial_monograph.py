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
                                Image, Preformatted, Table, TableStyle)


def render(source,output,*,edition='polynomial'):
    editions={
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
        s=re.sub(r'`([^`]+)`',r'<font name="Code" size="8.6">\1</font>',s)
        s=re.sub(r'\[([^\]]+)\]\(([^)]+)\)',r'\1 (\2)',s)
        return s
    lines=Path(source).read_text().splitlines();i=0;formula_count=0
    while i<len(lines):
        line=lines[i]
        if not line.strip():i+=1;continue
        if line.startswith('# '):i+=1;continue
        if line.startswith('## '):story.append(Paragraph(inline(line[3:]),heading));i+=1;continue
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
            story.append(Preformatted('\n'.join(block),code));i=j+1;continue
        paragraph=[line];i+=1
        while i<len(lines) and lines[i].strip() and not lines[i].startswith(('#','```','$$')):
            paragraph.append(lines[i]);i+=1
        story.append(Paragraph(inline(' '.join(paragraph)),body))
    def furniture(canvas,doc):
        canvas.saveState();canvas.setStrokeColor(colors.HexColor('#D0DBE0'));canvas.setLineWidth(.5)
        canvas.line(57,49,538,49);canvas.setFont('Label',8);canvas.setFillColor(navy)
        canvas.drawString(57,34,'PERFECTPOWER  /  '+profile['title'].upper());canvas.drawRightString(538,34,str(doc.page))
        if doc.page>1:canvas.setFont('Label',8);canvas.drawString(57,807,'Exact domains, preserved integer images, complete ties')
        canvas.restoreState()
    document=SimpleDocTemplate(str(output),pagesize=(595.28,841.89),rightMargin=57,leftMargin=57,topMargin=57,bottomMargin=66,
                               title=profile['title']+': '+re.sub('<br/>',' ',profile['subtitle']).lower(),author='PerfectPower')
    document.build(story,onFirstPage=furniture,onLaterPages=furniture)
    print(output)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--source',type=Path)
    parser.add_argument('--edition',choices=('polynomial','semilinear'),default='polynomial')
    parser.add_argument('--output',type=Path,required=True);args=parser.parse_args()
    source=args.source or Path(__file__).resolve().parents[1]/'docs'/(args.edition.upper()+'_CAPACITY_MONOGRAPH.md')
    render(source,args.output,edition=args.edition)
