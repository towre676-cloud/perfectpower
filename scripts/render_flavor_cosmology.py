"""Render the repository cosmology monograph deterministically."""
from pathlib import Path
from xml.sax.saxutils import escape
from reportlab.platypus import SimpleDocTemplate,Paragraph,Spacer,Image
from reportlab.lib.styles import getSampleStyleSheet
from reportlab.lib.enums import TA_JUSTIFY
from reportlab.lib import colors
from reportlab.lib.pagesizes import A4
from reportlab.lib.utils import ImageReader

root = Path(__file__).resolve().parents[1]
out = root/"output/pdf/Flavor_Cosmology_and_Tree_Decay.pdf"
out.parent.mkdir(parents=True,exist_ok=True)
styles = getSampleStyleSheet()
styles["BodyText"].fontName = "Times-Roman"
styles["BodyText"].fontSize = 10.2
styles["BodyText"].leading = 13.6
styles["BodyText"].alignment = TA_JUSTIFY
styles["BodyText"].spaceAfter = 8
styles["BodyText"].allowWidows = 0
styles["BodyText"].allowOrphans = 0
parts = (root/"docs/FLAVOR_COSMOLOGY_MONOGRAPH.md").read_text().split("\n\n")
story = []
for i,part in enumerate(parts):
    if not part.strip():
        continue
    style = styles["Title"] if part.startswith("# ") else styles["BodyText"]
    story.append(Paragraph(escape(part.removeprefix("# ").replace("\n"," ")),style))
    if i == 1:
        image = root/"receipts/flavor_cosmology/wall_stability.png"
        if not image.exists():image=root/"receipts/flavor_cosmology/dimensionful_walls.png"
        if not image.exists():image=root/"receipts/flavor_cosmology/tree_decay.png"
        iw,ih=ImageReader(str(image)).getSize()
        story.append(Image(str(image),width=465,height=465*ih/iw))
        story.append(Spacer(1,9))
def footer(canvas,doc):
    canvas.setFont("Times-Roman",8)
    canvas.setFillColor(colors.grey)
    canvas.drawString(45,25,"Perfectpower | coupled walls, exact thermal vacua and polynomial flavor bounds")
    canvas.drawRightString(A4[0]-45,25,str(doc.page))
SimpleDocTemplate(str(out),pagesize=A4,rightMargin=45,leftMargin=45,
                  topMargin=45,bottomMargin=43,invariant=1,
                  title="Coupled wall stability, exact thermal vacua and polynomial flavor bounds",
                  author="Perfectpower research repository").build(story,onFirstPage=footer,onLaterPages=footer)
