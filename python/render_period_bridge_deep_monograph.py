"""Render the deep integral reader with a ReportLab cover and XeLaTeX body.

The mathematical engine needs only stdlib.  This publication renderer needs
reportlab, pypdf, pandoc and xelatex.  It uses a fixed publication epoch so
the same source, renderer and toolchain can reproduce the document metadata.
Use pdftoppm for the separate required visual review after rendering.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import os
from pathlib import Path
import re
import shutil
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
PUBLICATION_EPOCH = int(datetime(2026, 10, 17, tzinfo=timezone.utc).timestamp())


def render(source, output):
    source, output = Path(source).resolve(), Path(output).resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    for command in ('pandoc', 'xelatex'):
        if not shutil.which(command):
            raise RuntimeError(command + ' is required to typeset the mathematical reader')
    for name, file in [('Reader', 'DejaVuSerif.ttf'), ('Display', 'DejaVuSans.ttf'),
                       ('DisplayBold', 'DejaVuSans-Bold.ttf')]:
        pdfmetrics.registerFont(TTFont(name, '/usr/share/fonts/truetype/dejavu/' + file))

    navy, teal, pale = (colors.HexColor(value) for value in ('#17324a', '#176b69', '#d9e6e9'))
    body_style = ParagraphStyle('CoverBody', fontName='Reader', fontSize=10.5,
                               leading=16, textColor=navy, spaceAfter=13)
    title_style = ParagraphStyle('CoverTitle', fontName='DisplayBold', fontSize=31,
                                leading=38, textColor=navy, spaceAfter=22)
    small = ParagraphStyle('CoverSmall', fontName='Display', fontSize=8.5,
                           leading=13, textColor=teal)
    cell = ParagraphStyle('Cell', fontName='Display', fontSize=9.2, leading=13, textColor=navy)

    def cover_footer(canvas, doc):
        canvas.setStrokeColor(teal)
        canvas.setLineWidth(1)
        canvas.line(49, 49, A4[0] - 49, 49)
        canvas.setFont('Display', 8)
        canvas.setFillColor(teal)
        canvas.drawString(49, 35, 'PERFECTPOWER  /  MATHEMATICAL RESEARCH SERIES')
        canvas.drawRightString(A4[0] - 49, 35, '1')

    with tempfile.TemporaryDirectory(prefix='deep-integral-reader-') as directory:
        temp = Path(directory)
        cover = temp / 'cover.pdf'
        document = SimpleDocTemplate(str(cover), pagesize=A4, leftMargin=49, rightMargin=49,
                                     topMargin=49, bottomMargin=65, invariant=1)
        story = [Paragraph('EXACT FAMILIES  /  OPERATORS  /  OBSERVATIONS', small), Spacer(1, 35),
                 Paragraph('Raghava generators,<br/>cyclotomic descent,<br/>and Coxeter spectra', title_style),
                 Paragraph('A complete mathematical reader connecting inverse-binomial harmonic sums, '
                           'finite character spectra, an actual E8 adjoint lift, and tunable Mellin zeros.', body_style),
                 Spacer(1, 18)]
        rows = [
            ('Raghava generating records', '130 families through weight 131'),
            ('Earlier selected-order identities', 'All 120 retained exactly'),
            ('Artifact conductor bridge', '384 / 264 / 240, with exact roles'),
            ('Actual E8 adjoint operator', '248 dimensions; zero at weight two'),
            ('Actual operator and induction bridge', 'Integral lattice map; refinement preserves the zero'),
            ('Coxeter classification and tuner', 'Every crystallographic type; B/C design rule'),
        ]
        table = Table([[Paragraph(a, cell), Paragraph(b, cell)] for a, b in rows], colWidths=[237, 260])
        table.setStyle(TableStyle([
            ('VALIGN', (0, 0), (-1, -1), 'TOP'), ('LEFTPADDING', (0, 0), (-1, -1), 0),
            ('RIGHTPADDING', (0, 0), (-1, -1), 9), ('TOPPADDING', (0, 0), (-1, -1), 9),
            ('BOTTOMPADDING', (0, 0), (-1, -1), 10),
            ('LINEBELOW', (0, 0), (-1, -1), 0.5, pale),
        ]))
        story += [table, Spacer(1, 23), Paragraph('17 October 2026 (UTC)', small), Spacer(1, 8),
                  Paragraph('Exact finite arithmetic, rational error bounds, and cited analytic and Lie-theoretic '
                            'derivations. Historical execution records are distinguished from freshly rerun checks. '
                            'Classical provenance and the scope of each construction remain explicit.', body_style)]
        document.build(story, onFirstPage=cover_footer, onLaterPages=cover_footer)
        if len(PdfReader(cover).pages) != 1:
            raise RuntimeError('the publication cover must fit one page')

        header = temp / 'header.tex'
        header.write_text(r'''\usepackage{amsmath,amssymb,mathtools}
\usepackage{xcolor,fancyhdr,titlesec,microtype,needspace}
\definecolor{ink}{HTML}{17324A}
\definecolor{accent}{HTML}{176B69}
\color{ink}
\setlength{\emergencystretch}{4em}
\allowdisplaybreaks[2]
\setlength{\parskip}{5pt plus 1pt}
\setlength{\parindent}{0pt}
\titleformat{\section}{\Large\sffamily\bfseries\color{accent}}{}{0em}{}
\titleformat{\subsection}{\large\sffamily\bfseries\color{accent}}{}{0em}{}
\titlespacing*{\section}{0pt}{21pt}{11pt}
\titlespacing*{\subsection}{0pt}{15pt}{8pt}
\pagestyle{fancy}
\fancyhf{}
\fancyhead[L]{\small\sffamily PerfectPower / Deep integral bridges}
\fancyfoot[R]{\small\sffamily\thepage}
\setlength{\headheight}{16pt}
\setcounter{page}{2}
\widowpenalty=10000
\clubpenalty=10000
\let\OriginalTableOfContents\tableofcontents
\renewcommand{\tableofcontents}{\OriginalTableOfContents\clearpage}
''')
        text = source.read_text()
        # The cover carries the document title.  TeX renders the actual body.
        text = text.split('\n', 1)[1]
        # References should begin cleanly, and URL strings need line breaks.
        text = text.replace('## Primary references and attribution',
                            '\\newpage\n\n## Primary references and attribution')
        body_md = temp / 'body.md'
        body_md.write_text(text)
        tex = temp / 'body.tex'
        environment = dict(os.environ, SOURCE_DATE_EPOCH=str(PUBLICATION_EPOCH),
                           FORCE_SOURCE_DATE='1', TZ='UTC')
        command = [
            'pandoc', str(body_md), '--standalone', '--from=markdown+tex_math_single_backslash',
            '--shift-heading-level-by=-1', '--toc', '--toc-depth=2',
            '-V', 'documentclass=article', '-V', 'fontsize=10pt', '-V', 'papersize=a4',
            '-V', 'geometry:top=22mm,bottom=21mm,left=21mm,right=21mm',
            '-V', 'mainfont=DejaVu Serif', '-V', 'sansfont=DejaVu Sans',
            '-V', 'monofont=DejaVu Sans Mono', '-V', 'monofontoptions=Scale=0.9', '-V', 'colorlinks=true',
            '-V', 'linkcolor=accent', '-V', 'urlcolor=accent',
            '--include-in-header=' + str(header), '-o', str(tex),
        ]
        subprocess.run(command, check=True, env=environment, capture_output=True, text=True)
        # Retain the TeX log through all passes so overfull material can be
        # diagnosed, rather than silently accepting a clipped equation.
        for _ in range(3):
            completed = subprocess.run(['xelatex', '-halt-on-error', '-interaction=nonstopmode', 'body.tex'],
                                       cwd=temp, env=environment, capture_output=True, text=True)
            if completed.returncode:
                raise RuntimeError('XeLaTeX failed:\n' + completed.stdout[-12000:])
        log = (temp / 'body.log').read_text(errors='replace')
        overflow = [float(value) for value in re.findall(r'Overfull \\hbox \(([0-9.]+)pt too wide\)', log)]
        missing = re.findall(r'Missing character:.*', log)
        if missing:
            raise RuntimeError('unsupported glyphs:\n' + '\n'.join(missing))
        if overflow:
            diagnostics = '\n'.join(line for line in log.splitlines()
                                    if 'Overfull' in line or 'at lines' in line)
            print('TeX overflow diagnostics:\n' + diagnostics)
        if overflow and max(overflow) > 5:
            # The adjacent source line numbers are important for repair.
            debug = ROOT / 'tmp/pdfs' / (output.stem + '_layout_debug.tex')
            debug.parent.mkdir(parents=True, exist_ok=True)
            debug.write_text(tex.read_text())
            debug.with_suffix('.log').write_text(log)
            raise RuntimeError('a mathematical display or table exceeds the text width; see ' + str(debug))

        writer = PdfWriter()
        writer.append(PdfReader(cover))
        writer.append(PdfReader(temp / 'body.pdf'))
        writer.add_metadata({
            '/Title': 'Deep integral bridges: Raghava generators, cyclotomic descent, and Coxeter spectra',
            '/Author': 'PerfectPower research program',
            '/Subject': 'Exact integral families, actual E8 adjoint lifts, complete observations, Coxeter Mellin zeros',
            '/CreationDate': 'D:20261017000000Z', '/ModDate': 'D:20261017000000Z',
        })
        with output.open('wb') as stream:
            writer.write(stream)
    pages = len(PdfReader(output).pages)
    digest = hashlib.sha256(output.read_bytes()).hexdigest()
    print('Rendered ' + str(pages) + ' pages; SHA-256 ' + digest)
    return str(output)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', default=str(ROOT / 'docs/PERIOD_BRIDGE_DEEP_MONOGRAPH.md'))
    parser.add_argument('--output', default=str(ROOT / 'docs/PERIOD_BRIDGE_DEEP_MONOGRAPH.pdf'))
    args = parser.parse_args()
    print(render(args.source, args.output))
