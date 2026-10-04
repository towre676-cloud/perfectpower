"""Render the positive-geometry reader with reportlab (packaging dependency only)."""
import argparse
import html
import json
import re
import textwrap
from pathlib import Path
from reportlab.lib import colors
from reportlab.lib.enums import TA_LEFT
from reportlab.lib.styles import ParagraphStyle
from reportlab.lib.pagesizes import A4
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.platypus import (SimpleDocTemplate, Paragraph, Spacer, PageBreak,
    Preformatted, Table, TableStyle, KeepTogether)
from reportlab.graphics.shapes import Drawing, Polygon, Line, Circle, String


def render(output):
    root=Path(__file__).resolve().parents[1]
    source=root/'docs/POSITIVE_GEOMETRY_MONOGRAPH.md'
    stats=json.loads((root/'receipts/positive_geometry/summary.json').read_text())
    fonts=Path('/usr/share/fonts/truetype/dejavu')
    for name,file in [('Reader','DejaVuSerif.ttf'),('ReaderBold','DejaVuSerif-Bold.ttf'),
                      ('Console','DejaVuSansMono.ttf'),('Display','DejaVuSans.ttf'),('DisplayBold','DejaVuSans-Bold.ttf')]:
        pdfmetrics.registerFont(TTFont(name,str(fonts/file)))
    pdfmetrics.registerFontFamily('Reader',normal='Reader',bold='ReaderBold',italic='Reader',boldItalic='ReaderBold')
    navy=colors.HexColor('#17324a');teal=colors.HexColor('#007e87')
    body=ParagraphStyle('Body',fontName='Reader',fontSize=10.1,leading=15.1,spaceAfter=9,
                        textColor=navy,splitLongWords=True)
    title=ParagraphStyle('Title',fontName='DisplayBold',fontSize=29,leading=35,textColor=navy,spaceAfter=22)
    h2=ParagraphStyle('Chapter',fontName='DisplayBold',fontSize=16,leading=21,spaceBefore=18,spaceAfter=12,
                      textColor=teal,keepWithNext=True)
    code=ParagraphStyle('Equation',fontName='Console',fontSize=8.1,leading=12,spaceBefore=7,spaceAfter=13,
                        backColor=colors.HexColor('#eef3f6'),borderPadding=9,textColor=navy)
    small=ParagraphStyle('Small',fontName='Display',fontSize=9,leading=13,textColor=navy)
    output=Path(output);output.parent.mkdir(parents=True,exist_ok=True)
    doc=SimpleDocTemplate(str(output),pagesize=A4,rightMargin=49,leftMargin=49,topMargin=48,bottomMargin=48,
                         title='Branch degenerations, positive geometry, and exact monodromy witnesses',
                         author='PerfectPower research program')
    story=[Paragraph('PERFECTPOWER / MATHEMATICAL READER',small),Spacer(1,21),
           Paragraph('Branch degenerations,<br/>positive geometry,<br/>and exact monodromy witnesses',title),
           Paragraph('Euler and Descartes curvature, associahedral collisions, cyclic graph polytopes, period contracts and integer curvature orbits.',body),
           Spacer(1,14)]
    rows=[['Collision strata',f"{stats['labelled_collision_strata']:,}"],
          ['Connection patterns / bases',f"{stats['distinct_collision_patterns']} / {stats['connection_bases']}"],
          ['Associahedron faces',f"{stats['associahedron_faces']:,}"],
          ['Existing quartic topology rows',f"{stats['quartic_source_rows']:,}"],
          ['Bounded curvature power tests',f"{stats['bounded_power_tests']:,}"]]
    table=Table(rows,colWidths=[325,165],hAlign='LEFT')
    table.setStyle(TableStyle([('FONTNAME',(0,0),(-1,-1),'Display'),('FONTSIZE',(0,0),(-1,-1),10),
        ('TEXTCOLOR',(0,0),(-1,-1),navy),('BOTTOMPADDING',(0,0),(-1,-1),9),('TOPPADDING',(0,0),(-1,-1),9),
        ('LINEBELOW',(0,0),(-1,-1),0.5,colors.HexColor('#cdd9e0')),('BACKGROUND',(0,0),(-1,-1),colors.HexColor('#f3f6f8'))]))
    story+=[table,Spacer(1,26)]
    d=Drawing(490,155)
    d.add(Polygon([25,25,145,25,85,125],fillColor=colors.HexColor('#d9eff0'),strokeColor=teal,strokeWidth=1.4))
    for x,y,label in ((25,25,'ab: 4'),(145,25,'ac: 2'),(85,125,'bc: 2')):
        d.add(Circle(x,y,3,fillColor=teal,strokeColor=teal))
        d.add(String(x-18,y-17,label,fontName='Display',fontSize=9,fillColor=navy))
    d.add(String(190,113,'Q = 4ab + 2ac + 2bc',fontName='Console',fontSize=12,fillColor=navy))
    d.add(String(190,85,'A transport determinant becomes a triangle.',fontName='Display',fontSize=10,fillColor=navy))
    d.add(String(190,63,'Its canonical form pulls back to',fontName='Display',fontSize=10,fillColor=navy))
    d.add(String(190,42,'da wedge db / (a*b).',fontName='Console',fontSize=11,fillColor=teal))
    story+=[d,Spacer(1,8),Paragraph('Release: 4 October 2026. New executable results are exact Python computations. Separate Lean formalization is supplied with explicit definitions and fixtures.',small),PageBreak()]
    lines=source.read_text().splitlines();paragraph=[];block=[];in_block=False
    def flush():
        if paragraph:
            text=html.escape(' '.join(paragraph))
            text=re.sub(r'`([^`]+)`',r'<font name="Console">\1</font>',text)
            story.append(Paragraph(text,body));paragraph.clear()
    for line in lines:
        if line.startswith('```'):
            flush()
            if in_block:
                wrapped=[]
                for row in block:
                    wrapped.extend(textwrap.wrap(row,width=91,replace_whitespace=False,drop_whitespace=False) or [''])
                story.append(Preformatted('\n'.join(wrapped),code));block=[]
            in_block=not in_block
        elif in_block:block.append(line)
        elif line.startswith('# '):continue
        elif line.startswith('## '):
            flush()
            if line[3:] == 'References':
                story.append(PageBreak())
            story.append(Paragraph(html.escape(line[3:]),h2))
        elif not line.strip():flush()
        else:paragraph.append(line.strip())
    flush()
    def footer(canvas,doc):
        canvas.saveState();w,h=A4
        canvas.setStrokeColor(colors.HexColor('#cdd9e0'));canvas.line(49,36,w-49,36)
        canvas.setFont('Display',8);canvas.setFillColor(navy)
        canvas.drawString(49,23,'PerfectPower | Positive geometry and branching')
        canvas.drawRightString(w-49,23,str(doc.page));canvas.restoreState()
    doc.build(story,onFirstPage=footer,onLaterPages=footer)
    return str(output)


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',default='output/pdf/PerfectPower_Positive_Geometry_Monograph.pdf')
    print(render(p.parse_args().output))
