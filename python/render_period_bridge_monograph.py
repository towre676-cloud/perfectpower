"""Build the mathematical reader: ReportLab cover and typeset TeX body.

Packaging dependencies: reportlab, pypdf, pandoc, and XeLaTeX. The exact
mathematical engine itself uses only the Python standard library.
"""
import argparse
import json
from pathlib import Path
import subprocess
import tempfile

from reportlab.lib import colors
from reportlab.lib.pagesizes import A4
from reportlab.lib.styles import ParagraphStyle
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle
from pypdf import PdfReader, PdfWriter

ROOT = Path(__file__).resolve().parents[1]


def render(output):
    output = Path(output).resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    summary = json.loads((ROOT/'receipts/period_bridge/summary.json').read_text())
    for name, file in [('Reader', 'DejaVuSerif.ttf'), ('Display', 'DejaVuSans.ttf'),
                       ('DisplayBold', 'DejaVuSans-Bold.ttf')]:
        pdfmetrics.registerFont(TTFont(name, '/usr/share/fonts/truetype/dejavu/'+file))
    navy, teal = colors.HexColor('#17324a'), colors.HexColor('#176b69')
    body = ParagraphStyle('Body', fontName='Reader', fontSize=11, leading=17, textColor=navy, spaceAfter=13)
    title = ParagraphStyle('Title', fontName='DisplayBold', fontSize=31, leading=38, textColor=navy, spaceAfter=22)
    small = ParagraphStyle('Small', fontName='Display', fontSize=9, leading=14, textColor=teal)
    with tempfile.TemporaryDirectory(prefix='period-reader-') as directory:
        temp = Path(directory)
        cover = temp/'cover.pdf'
        doc = SimpleDocTemplate(str(cover), pagesize=A4, leftMargin=49, rightMargin=49, topMargin=55, bottomMargin=45)
        story = [Paragraph('PERFECTPOWER / EXACT MATHEMATICAL READER', small), Spacer(1, 42),
                 Paragraph('Integral families,<br/>cyclotomic filters,<br/>and an E8 bridge', title),
                 Paragraph('A Raghava-centered construction connecting harmonic cancellation, rational phase geometry, and explicit root-lattice operators.', body), Spacer(1, 24)]
        rows = [['Raghava two-order identities', str(summary['counts']['raghava_two_order_identities'])],
                ['Exact Raghava receipts replayed', str(summary['counts']['exact_raghava_receipts_replayed'])],
                ['Primitive phases reduced', '240 to two terms'],
                ['Explicit E8 roots / Coxeter order', '240 / 30'],
                ['248-dimensional spectral model', 'Exact zero at weight two']]
        table = Table(rows, colWidths=[282, 214])
        table.setStyle(TableStyle([('FONTNAME', (0,0), (-1,-1), 'Display'), ('FONTSIZE', (0,0), (-1,-1), 10),
                                   ('TEXTCOLOR', (0,0), (-1,-1), navy), ('BOTTOMPADDING', (0,0), (-1,-1), 13),
                                   ('TOPPADDING', (0,0), (-1,-1), 13), ('LINEBELOW', (0,0), (-1,-1), .5, colors.HexColor('#cdd9e0'))]))
        story += [table, Spacer(1, 27), Paragraph('16 October 2026', small),
                  Paragraph('Exact finite arithmetic and cited analytic derivations. Independent numerical checks are labeled separately. The proposed higher-category colimit is not established by this release.', body)]
        doc.build(story)
        header = temp/'header.tex'
        header.write_text(r'''\usepackage{amsmath,amssymb,mathtools}
\usepackage{xcolor,fancyhdr,titlesec}
\definecolor{ink}{HTML}{17324A}
\definecolor{accent}{HTML}{176B69}
\color{ink}
\setlength{\emergencystretch}{3em}
\allowdisplaybreaks
\titleformat{\section}{\Large\sffamily\bfseries\color{accent}}{}{0em}{}
\pagestyle{fancy}
\fancyhf{}
\fancyhead[L]{\small\sffamily PerfectPower / Integral families}
\fancyfoot[R]{\small\sffamily\thepage}
\setlength{\headheight}{16pt}
\setcounter{page}{2}
''')
        source = (ROOT/'docs/PERIOD_BRIDGE_MONOGRAPH.md').read_text()
        # The cover carries the main title; retain all mathematical body text.
        source = source.split('\n', 1)[1]
        source = source.replace('## Primary sources and attribution', '\\newpage\n\n## Primary sources and attribution')
        source = source.replace('Consequently\n\n\\[', 'Consequently\\nopagebreak\n\n\\[')
        md = temp/'body.md'; md.write_text(source)
        body_pdf = temp/'body.pdf'
        subprocess.run(['pandoc', str(md), '--from=markdown+tex_math_single_backslash', '--shift-heading-level-by=-1', '--pdf-engine=xelatex',
                        '-V', 'documentclass=article', '-V', 'fontsize=10pt', '-V', 'papersize=a4',
                        '-V', 'geometry:margin=21mm', '-V', 'mainfont=DejaVu Serif',
                        '-V', 'sansfont=DejaVu Sans', '-V', 'monofont=DejaVu Sans Mono',
                        '-V', 'colorlinks=true', '-V', 'linkcolor=accent', '-V', 'urlcolor=accent',
                        '--include-in-header='+str(header), '-o', str(body_pdf)], check=True)
        writer = PdfWriter()
        writer.append(PdfReader(cover)); writer.append(PdfReader(body_pdf))
        writer.add_metadata({'/Title':'Exact integral families, cyclotomic filters, and an E8 spectral bridge',
                             '/Author':'PerfectPower research program', '/Subject':'Raghava-centered exact integral engine'})
        with output.open('wb') as stream: writer.write(stream)
    return str(output)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', default='output/pdf/PerfectPower_Period_Bridge_Monograph.pdf')
    print(render(parser.parse_args().output))
