"""Render the retuned wall monograph with deterministic PDF metadata."""
from pathlib import Path
from xml.sax.saxutils import escape
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Image
from reportlab.lib.styles import getSampleStyleSheet
from reportlab.lib.enums import TA_JUSTIFY
from reportlab.lib.pagesizes import A4
from reportlab.lib.utils import ImageReader

root = Path(__file__).resolve().parents[1]
out = root / "output/pdf/Retuned_Wall_Radiation_Nodes.pdf"
out.parent.mkdir(parents=True, exist_ok=True)
styles = getSampleStyleSheet()
body = styles["BodyText"]
body.fontName, body.fontSize, body.leading = "Times-Roman", 10.2, 13.6
body.alignment, body.spaceAfter = TA_JUSTIFY, 8
body.allowWidows = body.allowOrphans = 0
story = []
for i, part in enumerate((root / "docs/WALL_EMBEDDED_STATES_MONOGRAPH.md").read_text().split("\n\n")):
    if not part.strip():
        continue
    style = styles["Title"] if part.startswith("# ") else body
    story.append(Paragraph(escape(part.removeprefix("# ").replace("\n", " ")), style))
    if i == 1:
        picture = root / "receipts/flavor_cosmology/wall_embedded_states.png"
        iw, ih = ImageReader(str(picture)).getSize()
        story.extend([Image(str(picture), width=500, height=500*ih/iw), Spacer(1, 9)])

def footer(canvas, doc):
    canvas.setFont("Times-Roman", 8)
    canvas.drawString(45, 25, "Perfectpower | retuned radiation nodes and finite-radius candidates")
    canvas.drawRightString(A4[0]-45, 25, str(doc.page))

SimpleDocTemplate(str(out), pagesize=A4, rightMargin=45, leftMargin=45,
                  topMargin=42, bottomMargin=42, invariant=1,
                  title="Retuned polynomial radiation nodes", author="Perfectpower").build(
                      story, onFirstPage=footer, onLaterPages=footer)
print(out)
