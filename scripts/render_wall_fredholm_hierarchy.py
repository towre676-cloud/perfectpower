"""Render the Fredholm monograph with mathematical displays and its figure."""
from pathlib import Path
from xml.sax.saxutils import escape
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from reportlab.platypus import SimpleDocTemplate,Paragraph,Spacer,Image
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.lib.enums import TA_JUSTIFY
from reportlab.lib.pagesizes import A4
from reportlab.lib.utils import ImageReader
root=Path(__file__).resolve().parents[1]
out=root/'output/pdf/Polynomial_Wall_Fredholm_Hierarchy.pdf'
tmp=root/'tmp/pdfs/fredholm-equations';tmp.mkdir(parents=True,exist_ok=True)
styles=getSampleStyleSheet();body=styles['BodyText']
body.fontName,body.fontSize,body.leading='Times-Roman',10,13
body.alignment,body.spaceAfter=TA_JUSTIFY,7
body.allowWidows=body.allowOrphans=0
styles['Title'].fontName='Helvetica-Bold';styles['Title'].fontSize=20;styles['Title'].leading=24
lead=ParagraphStyle('EquationLead',parent=body,keepWithNext=True)
story=[];counter=0
blocks=(root/'docs/WALL_FREDHOLM_HIERARCHY_MONOGRAPH.md').read_text().split('\n\n')
for index,block in enumerate(blocks):
    if not block.strip():continue
    if block.startswith('$$'):
        counter+=1;figure=plt.figure(figsize=(9,1));figure.text(.02,.35,'$'+block.strip()[2:-2]+'$',fontsize=14)
        path=tmp/f'equation-{counter}.png';figure.savefig(path,dpi=200,bbox_inches='tight',pad_inches=.06);plt.close(figure)
        iw,ih=ImageReader(str(path)).getSize();width=min(499,iw*72/200)
        story.extend([Image(str(path),width=width,height=width*ih/iw),Spacer(1,8)])
    else:
        style=styles['Title'] if block.startswith('# ') else lead if index+1<len(blocks) and blocks[index+1].startswith('$$') else body
        story.append(Paragraph(escape(block.removeprefix('# ').replace('\n',' ')),style))
    if index==1:
        picture=root/'receipts/flavor_cosmology/wall_fredholm_hierarchy.png';iw,ih=ImageReader(str(picture)).getSize()
        story.extend([Image(str(picture),width=499,height=499*ih/iw),Spacer(1,10)])
def furniture(canvas,doc):
    canvas.setFont('Helvetica',7.5)
    canvas.drawString(48,25,'PERFECTPOWER | Polynomial responses and formal radiation cancellation')
    canvas.drawRightString(A4[0]-48,25,str(doc.page))
SimpleDocTemplate(str(out),pagesize=A4,leftMargin=48,rightMargin=48,topMargin=42,bottomMargin=42,
                  invariant=1,title='Polynomial wall Fredholm hierarchy',author='Perfectpower').build(story,onFirstPage=furniture,onLaterPages=furniture)
print(out)
