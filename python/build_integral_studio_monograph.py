#!/usr/bin/env python3
"""Append the integral-studio mathematical supplement without rebuilding old pages.

Run with the Codex primary Python runtime (reportlab/matplotlib/pypdf installed),
or with a Python environment containing those three packages. The first 38 pages
of --base are preserved, including existing named destinations and outlines.
All new integer claims are recomputed before authoring. The PDF's classical
analytic arguments are written proofs, not a Lean build claim.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
from hashlib import sha256
from io import BytesIO
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'python'))


def golden_certificate():
    from perfectpower.e8_periods import coxeter_matrix, identity, matmul, matrix_power, matvec
    C, I = coxeter_matrix(), identity()
    C6, C24 = matrix_power(C, 6), matrix_power(C, 24)
    G = tuple(tuple(I[i][j]+C6[i][j]+C24[i][j] for j in range(8)) for i in range(8))
    G2 = matmul(G, G)
    assert all(G2[i][j] == G[i][j]+I[i][j] for i in range(8) for j in range(8))
    assert matmul(C, G) == matmul(G, C)
    assert matrix_power(C, 30) == I
    inverse = tuple(tuple(G[i][j]-I[i][j] for j in range(8)) for i in range(8))
    assert matmul(G, inverse) == I == matmul(inverse, G)
    v = tuple(int(i == 7) for i in range(8))
    columns = [v]
    for _ in range(3):
        columns.append(matvec(C, columns[-1]))
    columns += [matvec(G, col) for col in columns[:4]]
    M = tuple(tuple(columns[j][i] for j in range(8)) for i in range(8))
    A = [[Fraction(a) for a in row] for row in M]
    determinant = Fraction(1)
    for j in range(8):
        pivot_row = next(i for i in range(j, 8) if A[i][j])
        if pivot_row != j:
            A[j], A[pivot_row] = A[pivot_row], A[j]
            determinant = -determinant
        pivot = A[j][j]
        determinant *= pivot
        for i in range(j+1, 8):
            factor = A[i][j]/pivot
            for k in range(j, 8):
                A[i][k] -= factor*A[j][k]
    assert determinant == -1
    return {'coxeter_order_check': True, 'golden_equation': True,
            'commutes_with_coxeter': True, 'inverse_is_G_minus_I': True,
            'golden_basis_determinant': str(determinant),
            'golden_operator': G, 'golden_basis': M}


def build_appendix(path: Path, certificate: dict, start_page=39):
    import matplotlib
    matplotlib.use('Agg')
    from matplotlib.mathtext import math_to_image
    from matplotlib.font_manager import FontProperties
    from reportlab.pdfgen.canvas import Canvas
    from reportlab.lib.colors import HexColor
    from reportlab.lib.utils import ImageReader
    from reportlab.pdfbase import pdfmetrics
    from reportlab.pdfbase.ttfonts import TTFont
    from reportlab.platypus import Paragraph, Table, TableStyle
    from reportlab.lib.styles import ParagraphStyle

    fontdir = Path('/usr/share/fonts/truetype/dejavu')
    pdfmetrics.registerFont(TTFont('StudioSerif', str(fontdir/'DejaVuSerif.ttf')))
    pdfmetrics.registerFont(TTFont('StudioSerifBold', str(fontdir/'DejaVuSerif-Bold.ttf')))
    pdfmetrics.registerFont(TTFont('StudioSans', str(fontdir/'DejaVuSans.ttf')))
    pdfmetrics.registerFont(TTFont('StudioSansBold', str(fontdir/'DejaVuSans-Bold.ttf')))
    from reportlab.pdfbase.pdfmetrics import registerFontFamily
    registerFontFamily('StudioSerif',normal='StudioSerif',bold='StudioSerifBold',italic='StudioSerif',boldItalic='StudioSerifBold')
    registerFontFamily('StudioSans',normal='StudioSans',bold='StudioSansBold',italic='StudioSans',boldItalic='StudioSansBold')
    W, H = 595.276, 841.89
    M, width = 49, W-98
    navy, teal, gold = '#142c39', '#177e82', '#ba8848'
    c = Canvas(str(path), pagesize=(W,H), pageCompression=1)
    c.setTitle('The golden integral studio - mathematical supplement')
    c.setAuthor('PerfectPower research')
    c.setSubject('Exact Gram energy, cyclotomic logarithms, Bernoulli selectors and the golden E8 action')
    styles = {
        'body':ParagraphStyle('body',fontName='StudioSerif',fontSize=10.35,leading=15.2,textColor=HexColor(navy),spaceAfter=9),
        'small':ParagraphStyle('small',fontName='StudioSans',fontSize=8.5,leading=12,textColor=HexColor(navy),spaceAfter=7),
        'lead':ParagraphStyle('lead',fontName='StudioSerif',fontSize=12.2,leading=17.5,textColor=HexColor(navy),spaceAfter=13),
        'label':ParagraphStyle('label',fontName='StudioSansBold',fontSize=9,leading=13,textColor=HexColor(teal),spaceAfter=8),
    }
    y=0; count=0
    def page(title,subtitle):
        nonlocal y,count
        if count: c.showPage()
        count += 1
        c.setFillColor(HexColor(navy)); c.rect(0,H-10,W,10,fill=1,stroke=0)
        c.setFillColor(HexColor(teal));c.setFont('StudioSansBold',8.1)
        c.drawString(M,H-35,'PERFECTPOWER / THE GOLDEN INTEGRAL STUDIO')
        c.setFillColor(HexColor('#74838a'));c.setFont('StudioSans',7.6)
        c.drawRightString(W-M,H-35,'MATHEMATICAL SUPPLEMENT')
        c.setStrokeColor(HexColor('#c7d8d8'));c.line(M,45,W-M,45)
        c.setFont('StudioSans',7.5);c.setFillColor(HexColor('#61747d'))
        c.drawString(M,30,'17 OCTOBER 2026 / EXACT OBJECTS, EXPLICIT PROOF SCOPE')
        c.drawRightString(W-M,30,str(start_page+count-1))
        c.setFillColor(HexColor(navy));c.setFont('StudioSerifBold',25)
        c.drawString(M,H-78,title)
        c.setFont('StudioSans',9);c.setFillColor(HexColor(teal))
        c.drawString(M,H-99,subtitle)
        y=H-122
    def text(s,kind='body'):
        nonlocal y
        p=Paragraph(s,styles[kind]);_,h=p.wrap(width,1000)
        if y-h<58:raise RuntimeError(f'Page {count} overflow by {58-y+h:.1f} points: {s[:75]}')
        p.drawOn(c,M,y-h);y-=h+styles[kind].spaceAfter
    def eq(s,size=16,highlight=False):
        nonlocal y
        buf=BytesIO()
        matplotlib.rcParams['mathtext.fontset']='stix'
        matplotlib.rcParams['savefig.transparent']=True
        math_to_image('$'+s+'$',buf,prop=FontProperties(size=size),dpi=300,format='png',color=navy)
        buf.seek(0); img=ImageReader(buf);iw,ih=img.getSize()
        dw=iw*72/300;dh=ih*72/300
        scale=min(1,(width-20)/dw)
        dw*=scale;dh*=scale
        pad=13 if highlight else 7
        if y-dh-2*pad<58:raise RuntimeError(f'Page {count} equation overflow: {s[:75]}')
        if highlight:
            c.setFillColor(HexColor('#edf5f3'));c.roundRect(M,y-dh-2*pad,width,dh+2*pad,5,fill=1,stroke=0)
        c.drawImage(img,M+(width-dw)/2,y-dh-pad,dw,dh,mask='auto')
        y-=dh+2*pad+7
    def table(data,colwidths=None,font=9.1):
        nonlocal y
        cells=[[Paragraph(str(v),ParagraphStyle('cell',fontName='StudioSans',fontSize=font,leading=font+4,textColor=HexColor(navy))) for v in row] for row in data]
        t=Table(cells,colWidths=colwidths or [width/len(data[0])]*len(data[0]))
        t.setStyle(TableStyle([('BACKGROUND',(0,0),(-1,0),HexColor('#e7f0ee')),('VALIGN',(0,0),(-1,-1),'MIDDLE'),('LINEBELOW',(0,0),(-1,0),.7,HexColor(teal)),('LINEBELOW',(0,1),(-1,-1),.3,HexColor('#d9e3e3')),('TOPPADDING',(0,0),(-1,-1),6),('BOTTOMPADDING',(0,0),(-1,-1),6)]))
        _,h=t.wrap(width,1000)
        if y-h<58:raise RuntimeError(f'Page {count} table overflow')
        t.drawOn(c,M,y-h);y-=h+13

    page('One integral, four directions','THE OBJECT / A SINGLE EXACT QUADRATIC ENERGY')
    text('An integral studio should make a defined mathematical object easier to inspect. Here every parameter, projected root, logarithmic sector, and energy surface is tied to one four-parameter integral. The previous 38 pages of this reader are preserved unchanged.','lead')
    eq(r'\varphi=\frac{1+\sqrt{5}}{2},\qquad u=\frac{\pi^2}{4}-(\arcsin x)^2',15)
    eq(r'Q_+=4x^2-2\varphi^{-1}x-\varphi^2,\qquad Q_-=4x^2+2\varphi x-\varphi^{-2}',14)
    eq(r'A=\log|Q_+Q_-|,\quad K=\log|Q_+/Q_-|,\quad P=u^2,\quad R=u^2(u+\pi^2/2)',13.4)
    eq(r'\mathcal{E}(a,b,c,d)=\int_{-1}^{1}\frac{[aA+bK+cP+dR]^2}{\sqrt{1-x^2}}\,dx',18,True)
    text('The arcsine is its principal real branch. Internal logarithmic singularities are ordinary improper integrals. With x = cos θ, the measure becomes dθ and u becomes θ(π - θ), for 0 ≤ θ ≤ π. This removes the endpoint weight exactly. Squared logarithms are integrable at all four interior roots.')
    eq(r'f=(A,K,P,R),\qquad H_{ij}=\int_0^\pi f_i f_j\,d\theta,\qquad\mathcal{E}=\mathbf{t}^{\mathsf{T}}H\mathbf{t}',14.7)
    text('The matrix H is an exact Gram matrix. In the expanded energy an off-diagonal entry occurs twice: for example, the coefficient of ac is 2H<sub>AP</sub>. Individual challenge integrals can therefore be recovered as mixed coefficients, rather than introduced as independent examples.')
    text('The instrument exposes three linked observations: the squared response and accumulated area; the actual Coxeter spectrum and projected E8 roots; and a two-parameter section of this positive quadratic energy. Automatic motion changes the same parameters as the manual controls.','small')

    page('The complete closed form','THE ANSWER / TEN INDEPENDENT GRAM ENTRIES')
    text('The quadratic character χ₅ takes values 0, 1, -1, -1, 1 on residue classes 0, 1, 2, 3, 4 modulo five. Its Dirichlet series is L(s, χ₅) = Σ χ₅(n)/nˢ. All ten entries are:')
    entries=[('Entry','Exact value'),('H<sub>AA</sub>','8π³ / 45'),('H<sub>AK</sub>','-4π³ / 75'),('H<sub>KK</sub>','8π³ / 15'),('H<sub>AP</sub>','832π ζ(5) / 1125'),('H<sub>AR</sub>','157976π ζ(7) / 28125'),('H<sub>KP</sub>','41π √5 L(5, χ₅) / 54'),('H<sub>KR</sub>','1825π √5 L(7, χ₅) / 324'),('H<sub>PP</sub>','π⁹ / 630'),('H<sub>PR</sub>','4π¹¹ / 3465'),('H<sub>RR</sub>','101π¹³ / 120120')]
    table(entries,[width*.25,width*.75],10)
    text('<b>Positive definiteness has a structural proof.</b> If aA + bK + cP + dR vanishes almost everywhere, the singular coefficients at the roots of Q₊ and Q₋ must vanish. They are a + b and a - b, so a = b = 0. The remaining expression P[c + d(u + π²/2)] vanishes on an interval, forcing c = d = 0. No independence conjecture for special constants is involved.')
    eq(r'\langle A,3A+10K\rangle=3H_{AA}+10H_{AK}=0',16,True)
    text('Since 3A + 10K = log|Q₊¹³/Q₋⁷| away from the finite roots, the exponents 13 and 7 in the orthogonality challenge are fixed by this matrix. The log-square challenge is simply the parameter state (0, 1, 0, 0).','small')

    page('A selector for every odd weight','BERNOULLI SYMMETRY / ZETA AND DIRICHLET L-VALUES')
    text('Define Pₘ as a polynomial in u by the identity below. The symmetry B₂ₘ(1 - t) = B₂ₘ(t) guarantees that it is a polynomial in t(1 - t). Every polynomial invariant under reflection about 1/2 has that form.')
    eq(r'P_m(\pi^2t(1-t))=(-1)^m\pi^{2m}[B_{2m}(t)-B_{2m}(0)]',15)
    eq(r'P_1=u,\qquad P_2=u^2=P,\qquad P_3=u^2(u+\pi^2/2)=R',15)
    text('The classical Bernoulli Fourier expansion yields a cosine series containing only even angular frequencies. Write dₘ = (2m)! / 2²ᵐ⁻¹. Then')
    eq(r'P_m(\theta(\pi-\theta))=d_m\left[\zeta(2m)-\sum_{n\geq1}\frac{\cos(2n\theta)}{n^{2m}}\right]',15)
    text('Taking the scalar product with the product logarithm or with the ratio logarithm gives two parallel families. The Fourier and arithmetic derivation is supplied on the next page.')
    eq(r'\langle A,P_m\rangle=\frac{(2m)!\pi}{2^{2m+1}}(1-3^{-2m})(1-5^{-2m})\zeta(2m+1)',15.2,True)
    eq(r'\langle K,P_m\rangle=\frac{(2m)!\pi\sqrt{5}}{2^{2m+1}}(1+3^{-2m})L(2m+1,\chi_5)',15.2,True)
    text('The cases m = 2 and m = 3 are exactly H<sub>AP</sub>, H<sub>AR</sub>, H<sub>KP</sub>, and H<sub>KR</sub>. The extra π²/2 in R cancels the lower-weight contribution. It is prescribed by the Bernoulli polynomial, rather than fitted to a desired numerical answer.')
    text('The family selects every odd zeta value from the product sector and every odd χ₅ Dirichlet L-value from the ratio sector. It also connects directly to the earlier inverse-binomial moment chapter: the same symmetric Bernoulli data reorganizes the finite Coxeter phases.','small')

    page('The arithmetic inside the quartic','CYCLOTOMIC FACTORIZATION / A FOURIER PROOF')
    text('Let C be the actual integral E8 Coxeter matrix and L = 2I + C + C⁻¹. For z = exp(iθ), the quartic is a spectral determinant:')
    eq(r'z^4Q(\cos\theta)=\Phi_{30}(z),\quad \det(I-zC)=\Phi_{30}(z)',15)
    eq(r'\det((2x+2)I-L)=Q(x)^2',17)
    text('The square records the equality of the L-eigenvalues at conjugate Coxeter phases. Let c<sub>N</sub>(n) denote the Ramanujan sum over primitive N-th roots. Factoring Φ₃₀, and splitting its phase exponents by χ₅, gives')
    eq(r'A(\cos\theta)=-\sum_{n\geq1}\frac{c_{30}(n)}{n}\cos(n\theta)',15)
    eq(r'K(\cos\theta)=-\sum_{n\geq1}\frac{\sqrt{5}\chi_5(n)c_6(n)}{n}\cos(n\theta)',15)
    text('The positive sector has representatives 1 and 11; the negative sector has 7 and 13. The quadratic Gauss sum modulo five is √5, and Chinese remainder factorization supplies c₆. These conventions fix the sign of the mixed entries.')
    text('<b>Boundary justification.</b> First damp every unit-circle root radially by 0 &lt; r &lt; 1. The Fourier series then converges absolutely. Its coefficients converge in ℓ², so its boundary values converge in L²(0, π). Finite sums of log|2 sin((θ - α)/2)| have precisely that limit. Parseval and scalar products with polynomial weights pass to the limit in L², avoiding a pointwise interchange at a root.')
    eq(r'\sum_{n\geq1}\frac{c_{30}(2n)}{n^s}=(1-3^{1-s})(1-5^{1-s})\zeta(s)',14.5)
    eq(r'\sum_{n\geq1}\frac{\sqrt{5}\chi_5(2n)c_6(2n)}{n^s}=\sqrt{5}(1+3^{1-s})L(s,\chi_5)',14.5)
    text('Indeed c₃₀(2n) = c₁₅(n), whereas χ₅(2) = χ₅(3) = -1 and c₆(2n) = -1 + 3[3 divides n]. Pairing these two Dirichlet series with the even-frequency selector contributes dₘπ/4 and proves both families.','small')

    page('Why the squared logarithm is clean','PARSEVAL / THE LOGARITHMIC AND POLYNOMIAL BLOCKS')
    text('For every positive integer frequency, cos(nθ) has squared norm π/2. For a prime p, c<sub>p</sub>(n)² = 1 + p(p - 2)[p divides n]. Thus')
    eq(r'\sum_{n\geq1}\frac{c_{30}(n)^2}{n^2}=\frac{32}{15}\zeta(2),\qquad \sum_{n\geq1}\frac{5\chi_5(n)^2c_6(n)^2}{n^2}=\frac{32}{5}\zeta(2)',14.5)
    text('Multiplying by π/2 gives H<sub>AA</sub> = 8π³/45 and H<sub>KK</sub> = 8π³/15. For the mixed entry, c₅ = -1 away from multiples of five, while χ₅ vanishes on those multiples and c₆² = 1 + 3[3 divides n]. Consequently')
    eq(r'H_{AK}=-\frac{\pi\sqrt{5}}{3}L(2,\chi_5)=-\frac{4\pi^3}{75}',17,True)
    text('The last equality can be obtained directly: B₂(1/5) = B₂(4/5) = 1/150 and B₂(2/5) = B₂(3/5) = -11/150. Their character-weighted sum is 4/25. The B₂ Fourier series and Gauss sum then give L(2, χ₅) = 4π²/(25√5).')
    text('For the remaining block put t = θ/π and v = t(1 - t). Then P = π⁴v² and R = π⁶v²(v + 1/2). The elementary beta integral proves')
    eq(r'H_{PP}=\pi^9B(5,5)=\frac{\pi^9}{630}',15)
    eq(r'H_{PR}=\pi^{11}[B(6,6)+\frac{1}{2}B(5,5)]=\frac{4\pi^{11}}{3465}',15)
    eq(r'H_{RR}=\pi^{13}[B(7,7)+B(6,6)+\frac{1}{4}B(5,5)]=\frac{101\pi^{13}}{120120}',15)
    text('These six entries, together with the four selector entries, finish the proof of the complete master energy. The same arithmetic filter explains the pure π³ result, the mixed odd constants, and the exact orthogonality.','small')

    page('The golden action is integral','E8 LATTICE / FOUR COORDINATES OVER THE GOLDEN INTEGERS')
    text('The golden sector split is encoded by an actual integer matrix. Define G from the same Coxeter operator; do not confuse it with the Gram matrix H.')
    eq(r'G=I+C^6+C^{24},\qquad G^2=G+I,\qquad GC=CG,\qquad G^{-1}=G-I',15,True)
    text('At primitive exponent r the eigenvalue is 1 + 2cos(2πr/5): it equals φ in the χ₅ = +1 sector and -φ⁻¹ in the χ₅ = -1 sector. The normalized real grading J = (2G - I)/√5 satisfies J² = I. Its projectors (I ± J)/2 select the two sectors; these projectors are not integral lattice maps.')
    text('Let v be the eighth simple-root coordinate vector. Exact elimination gives det M = -1 for the eight columns below. No denominator or hidden lattice index is present.')
    eq(r'M=(v,Cv,C^2v,C^3v,Gv,GCv,GC^2v,GC^3v),\qquad\det M=-1',14)
    matrix=[['0','0','0','0','0','0','-1','1'],['0','0','0','0','-1','0','0','0'],['0','0','0','0','0','-1','0','1'],['0','0','0','0','-1','0','0','1'],['0','0','0','1','0','0','0','1'],['0','0','1','0','0','0','0','1'],['0','1','0','0','0','0','0','1'],['1','0','0','0','0','0','0','1']]
    # Matrix with deliberately quiet typography and no misleading header row.
    t=Table(matrix,colWidths=[25]*8)
    t.setStyle(TableStyle([('FONTNAME',(0,0),(-1,-1),'StudioSans'),('FONTSIZE',(0,0),(-1,-1),9),('ALIGN',(0,0),(-1,-1),'CENTER'),('TOPPADDING',(0,0),(-1,-1),3),('BOTTOMPADDING',(0,0),(-1,-1),3),('BACKGROUND',(0,0),(-1,-1),HexColor('#f2f6f5'))]))
    _,h=t.wrap(width,1000);t.drawOn(c,M+(width-200)/2,y-h);y-=h+14
    text('Let a + bφ act as aI + bG. The displayed Z-basis proves that the lattice is a free Z[φ]-module of rank four, with module basis v, Cv, C²v, C³v. The same quadratic relation gives Gⁿ = FₙG + Fₙ₋₁I for n ≥ 1: Fibonacci recurrence governs these integer operations exactly.')
    text('G preserves the integral lattice and commutes with C, but it is not an isometry of the positive E8 metric: an eigenvalue φ expands lengths. This module structure alone does not prove an H4 identification or a physical golden-ratio model. The builder recomputes the identities and determinant using exact integers and fractions.','small')

    page('Geometry with a defined meaning','SPECTRAL PROJECTIONS / ENERGY SECTIONS / NORMALIZATION')
    text('The spectral scene uses the 240 actual E8 roots and the actual Coxeter action. Their finite point set is distinct from the eight-dimensional reflection representation and the 240-dimensional root permutation representation. A camera view does not identify those objects.','lead')
    eq(r'\Pi_r=\frac{2}{30}\sum_{k=0}^{29}\cos(2\pi rk/30)C^k',19,True)
    text('For a primitive exponent r, this is the real rank-two spectral projector onto the conjugate phase pair. It is orthogonal for the Cartan metric because C preserves that metric. In simple-root coordinates it need not be symmetric for the ordinary coordinate dot product. An orthonormal basis of its image gives actual Coxeter-plane coordinates.')
    text('A displayed three-dimensional root scene combines explicitly selected projected coordinates. Its gold and teal coloring records the normalized grading J. Perspective and visual motion serve inspection; they do not change the exact rank or introduce a third dimension into a rank-two spectral plane.')
    eq(r'\mathcal{E}(\mathbf{t})=\mathbf{t}^{\mathsf{T}}H\mathbf{t},\qquad N_{ij}=\frac{H_{ij}}{\sqrt{H_{ii}H_{jj}}}',17)
    text('Every two-parameter section is a positive quadratic surface with the other coordinates held fixed. Completing the square determines its center; diagonalization determines its positive curvature and elliptical level sets. The normalized Gram matrix N has unit diagonal, so controls can compare basis functions despite their different powers of π. The parameter conversion must use the same normalization.')
    text('The AP, AR, KP, and KR challenges are obtained from the appropriate mixed coefficients. The pure log-square state uses K alone, while 3A + 10K gives the exact logarithmic orthogonality direction. An automatic tour must change the same parameters and recompute the same observations as a manual adjustment.')
    eq(r'\int_{\mathbb{R}^4}e^{-\mathbf{t}^{\mathsf{T}}H\mathbf{t}/2}\,d\mathbf{t}=\frac{(2\pi)^2}{\sqrt{\det H}}',17)
    text('This last identity is the ordinary Gaussian volume associated with a positive Gram form. It supplies a precise connection to Gaussian geometry, without claiming a physical partition function, a fitted statistical model, or an unidentified equivalence to another repository.','small')

    page('Independent numerical observation','ROOT-SPLIT QUADRATURE / ROUNDED NUMBERS / FAITHFUL PLOTS')
    text('The closed Gram formula is evaluated in browser floating-point arithmetic. Its exact labels carry symbolic coefficients, while displayed decimals are rounded approximations. A numerical agreement supports implementation; the written Fourier proof establishes the exact identity.','lead')
    eq(r'\theta=\frac{\pi}{15},\ \frac{7\pi}{15},\ \frac{11\pi}{15},\ \frac{13\pi}{15}',19)
    text('These are the four internal zeros. Independent integration works in θ and splits the interval at each zero. On a subinterval [l, r], an endpoint map removes direct sampling at singular logarithms:')
    eq(r'\theta=l+(r-l)q(s),\qquad q(s)=\frac{s^4}{s^4+(1-s)^4}',18,True)
    text('Near an endpoint the transformed squared-logarithm term is of order s³(log s)². Its integral is finite, and an endpoint-free Gauss-Legendre rule samples only finite values. Comparing two rule orders supplies an empirical discrepancy indicator, not a rigorous error enclosure. A mixed parameter vector exercises all ten Gram entries simultaneously.')
    text('Near a zero, a line chart may cap its drawing height to keep the rest visible. That is a display operation only. The integration path must retain the improper integral and must never reuse clipped graph samples as its numerical density. The accumulated energy is monotone because the squared response is nonnegative; the unsquared response may change sign.')
    text('Exporting an observation should retain the parameters, normalization, exact matrix labels, numerical matrix, quadrature method and order, spectral exponent, and software source identity. A reproducible view records a mathematical state, rather than only a camera angle.')
    text('<b>Finite arithmetic and analysis stay separate.</b> The golden matrix checks use exact integer multiplication and exact fraction elimination. The quadrature compares a direct integral with the closed formula. Neither procedure extends the inherited Lean kernel proof boundary to Fourier convergence or special-function evaluations.')
    text('The interface can show the density in x or θ, but the displayed Jacobian must correspond to the chosen variable. In particular, the θ density is [aA + bK + cP + dR]², whereas the x density includes the factor (1 - x²)⁻¹ᐟ².','small')

    page('What has been established','PROOF SCOPE / REPRODUCIBILITY / CLASSICAL PROVENANCE')
    text('The result is one exact quadratic integral with a complete, positive-definite Gram matrix, two all-order odd-constant selector families, a cyclotomic spectral determinant, and an integral golden action on the actual E8 lattice. Each mathematical layer has a stated proof mechanism.','lead')
    table([('Layer','Evidence and scope'),('Existing finite formal core','102 audited Lean theorems: 61 Coxeter bridge, 15 phase-fiber, 26 first-moment induction.'),('New integral identities','Written Fourier, Parseval, Bernoulli, Gauss-sum and beta-integral derivations; independent numerical comparisons.'),('Golden lattice action','Exact integer identities and a unimodular basis of determinant -1, recomputed by this builder.'),('Browser observations','Floating-point matrix evaluation, explicit root-split quadrature, finite plotting and spectral projection.')],[width*.30,width*.70],9.2)
    text('The new logarithmic identities, boundary-value argument, golden-module calculation, and quadrature are not new Lean theorems. Sharing an underlying matrix with a formalized chapter does not transfer proof status to new analytic claims. The 102-theorem result retains the exact finite scope stated in the earlier reader.')
    text('<b>Reproduction.</b> The full derivation is retained in docs/INTEGRAL_STUDIO_MONOGRAPH.md. The script python/build_integral_studio_monograph.py verifies the golden certificate, renders this supplement, preserves the first 38 pages and their destinations, and appends these pages. Exact Gram labels and numerical implementation are documented separately in INTEGRAL_STUDIO_MATHEMATICS.md.')
    text('<b>Classical sources.</b> NIST DLMF §24.8 supplies Bernoulli Fourier series, §25.15 gives Dirichlet L-function conventions, and §5.12 gives beta integrals. Raghava, <i>Arcsine kernels, inverse-binomial harmonic sums, and classical hypergeometric transformations</i>, arXiv:2607.09904v2, supplies the motivating kernel and moment framework attributed in the earlier reader.')
    text('https://dlmf.nist.gov/24.8<br/>https://dlmf.nist.gov/25.15<br/>https://dlmf.nist.gov/5.12<br/>https://arxiv.org/html/2607.09904v2','small')
    text('The matrix conventions and actual root coordinates are those of e8_periods.py and CoxeterPhaseBridge.lean. This synthesis does not require a claim of historical novelty, an H4 identification, or a physical interpretation. Its strength is that all displayed connections have explicit objects and maps.','small')
    c.save()
    return count


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--base',type=Path,default=ROOT/'docs/PERIOD_BRIDGE_DEEP_MONOGRAPH.pdf')
    p.add_argument('--output',type=Path,default=ROOT/'docs/PERIOD_BRIDGE_DEEP_MONOGRAPH.pdf')
    p.add_argument('--download',type=Path)
    p.add_argument('--base-pages',type=int,default=38)
    args=p.parse_args()
    from pypdf import PdfReader, PdfWriter
    tempdir=ROOT/'tmp/pdfs/integral-studio'
    tempdir.mkdir(parents=True,exist_ok=True)
    certificate=golden_certificate()
    (tempdir/'golden-certificate.json').write_text(json.dumps(certificate,indent=2)+'\n')
    appendix=tempdir/'integral-studio-appendix.pdf'
    appendix_pages=build_appendix(appendix,certificate,args.base_pages+1)
    base_reader=PdfReader(args.base)
    if len(base_reader.pages)<args.base_pages:
        raise ValueError('base is shorter than the retained original page count')
    original_hashes=[sha256(page.get_contents().get_data()).hexdigest() for page in base_reader.pages[:args.base_pages]]
    original_destinations=set(base_reader.named_destinations)
    writer=PdfWriter()
    writer.append(base_reader,pages=(0,args.base_pages),import_outline=True)
    writer.append(PdfReader(appendix),outline_item='The golden integral studio')
    writer.add_metadata({'/Title':'PerfectPower deep integral bridges and the golden integral studio',
                         '/Author':'PerfectPower research',
                         '/Subject':'Preserved 38-page reader with exact integral-studio supplement',
                         '/IntegralStudioBasePages':str(args.base_pages),
                         '/IntegralStudioAppendixPages':str(appendix_pages)})
    staged=tempdir/'combined-monograph.pdf'
    with staged.open('wb') as f:writer.write(f)
    final=PdfReader(staged)
    assert len(final.pages)==args.base_pages+appendix_pages
    actual_hashes=[sha256(page.get_contents().get_data()).hexdigest() for page in final.pages[:args.base_pages]]
    assert actual_hashes==original_hashes,'original page content streams changed'
    assert original_destinations.issubset(final.named_destinations),'an original named destination was dropped'
    out_bytes=staged.read_bytes()
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_bytes(out_bytes)
    if args.download:
        args.download.parent.mkdir(parents=True,exist_ok=True)
        args.download.write_bytes(out_bytes)
    report={'base_pages_preserved':args.base_pages,'appendix_pages':appendix_pages,
            'total_pages':len(final.pages),'original_page_streams_identical':True,
            'original_named_destinations_preserved':len(original_destinations),
            'golden_basis_determinant':certificate['golden_basis_determinant'],
            'sha256':sha256(out_bytes).hexdigest(),'bytes':len(out_bytes)}
    (tempdir/'validation.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
