"""Published coordinates are discovery inputs; exact certificates are evidence.

Decode only the two Sage numeric constructors present in the pinned source.
Neither the source's basis assertion nor integral completeness is imported.
"""
import copy
import hashlib
import io
import pickle
import zlib
from fractions import Fraction
from math import isqrt
from .elliptic_arithmetic import EllipticCurve, encode_point
from .elliptic_certificate_verifier import verify_independence
from .mordell_cover_charts import projective_cover_lift

SOURCE_URL = 'https://www.math.u-bordeaux.fr/~bmatschke/data/mwMordell10000.sobj'
SOURCE_PAGE = 'https://www.math.u-bordeaux.fr/~bmatschke/data/'
SOURCE_SHA256 = '23692c1f7d63fd94cab3a1231fadbba83a08755a0c370e20e191a4d8b8686c2d'
SOURCE_AUTHORS = ['Rafael von Känel', 'Benjamin Matschke']
SOURCE_LICENSE = 'CC BY-NC 3.0'


def _integer(text):
    if type(text) is not str or not 1 <= len(text) <= 2400:
        raise ValueError('bounded Sage base-32 integer required')
    return int(text, 32)


def _rational(text):
    if type(text) is not str or len(text) > 4801:
        raise ValueError('bounded Sage rational required')
    a, sep, b = text.partition('/')
    return Fraction(_integer(a), _integer(b) if sep else 1)


class _NumericReader(pickle.Unpickler):
    def find_class(self, module, name):
        if (module, name) == ('sage.rings.integer', 'make_integer'):
            return _integer
        if (module, name) == ('sage.rings.rational', 'make_rational'):
            return _rational
        raise ValueError('unsupported serialized constructor')

    def persistent_load(self, pid):
        raise ValueError('persistent serialized references are forbidden')


def read_published_candidates(blob):
    """Read a hash-pinned source without Sage or arbitrary pickle imports."""
    if type(blob) is not bytes or len(blob) > 2 * 1024**2:
        raise ValueError('bounded source bytes required')
    if hashlib.sha256(blob).hexdigest() != SOURCE_SHA256:
        raise ValueError('published source checksum mismatch')
    decoder = zlib.decompressobj()
    raw = decoder.decompress(blob, 8 * 1024**2 + 1)
    if len(raw) > 8 * 1024**2 or not decoder.eof or decoder.unused_data:
        raise ValueError('invalid or oversized compressed source')
    stream = io.BytesIO(raw)
    rows = _NumericReader(stream, encoding='ascii').load()
    if stream.read() or type(rows) is not list or len(rows) > 20000:
        raise ValueError('bounded complete source sequence required')
    result = {}
    for row in rows:
        if type(row) is not tuple or len(row) != 2:
            raise ValueError('coefficient and coordinate list required')
        k, points = row
        if type(k) is not int or not 0 < abs(k) <= 10000 or k in result:
            raise ValueError('distinct bounded nonzero coefficient required')
        if type(points) is not list or len(points) > 4:
            raise ValueError('bounded source point list required')
        E = EllipticCurve([0, k])
        result[k] = [encode_point(E.checked(point)) for point in points]
        if any(point is None for point in result[k]):
            raise ValueError('finite source points required')
    return result


def source_provenance():
    return dict(source_url=SOURCE_URL, source_page=SOURCE_PAGE,
                source_sha256=SOURCE_SHA256, authors=SOURCE_AUTHORS[:],
                source_license=SOURCE_LICENSE, source_basis_claim_adopted=False,
                integral_completeness_claimed=False)


def recover_cover_preimages(descent, point):
    """Discover rational roots, then check each original weighted-cover lift.

    SymPy is used for positive discovery only. An empty return is not an
    assertion that the point has no rational cover preimage.
    """
    import sympy as S
    E = EllipticCurve([0, descent['k']])
    x, _ = E.checked(point)
    t = S.Symbol('t')
    result = []
    for index, cover in enumerate(descent['covers']):
        f = cover['quartic']
        nx = cover['x_numerator']
        equation = sum((S.Rational(nx[j]) - S.Rational(x.numerator,x.denominator)*S.Rational(f[j]))*t**j for j in range(5))
        for root in S.polys.polytools.ground_roots(equation,t):
            u, v = int(S.numer(root)), int(S.denom(root))
            value = sum(int(a)*u**j*v**(4-j) for j,a in enumerate(f))
            if value <= 0:
                continue
            w = isqrt(value)
            if w*w != value:
                continue
            for signed in (w, -w):
                coordinates = [u,v,signed]
                lift = projective_cover_lift(descent['k'],cover,coordinates)
                if lift['mordell_point'] == point:
                    result.append(dict(cover_index=index,
                                       coordinates=coordinates,
                                       projective_height=max(abs(u),v),
                                       mordell_point=point))
    return result


def augment_published_witnesses(descent, points):
    """Attach exact points and independently verified rank lower evidence."""
    if descent.get('schema') != 'pp-mordell-two-descent/1':
        raise ValueError('Mordell descent packet required')
    if not isinstance(points,(list,tuple)) or len(points) > 64:
        raise ValueError('bounded finite candidate list required')
    result = copy.deepcopy(descent)
    E = EllipticCurve([0, result['k']])
    if E.specification != result['curve']:
        raise ValueError('original Mordell model mismatch')
    retained = [encode_point(E.checked(p)) for p in result['points']]
    accepted = []
    for point in points:
        canonical = encode_point(E.checked(point))
        if canonical is None or canonical != point:
            raise ValueError('canonical finite candidate required')
        if canonical not in retained:
            retained.append(canonical)
        accepted.append(canonical)
    if len(retained) > 64:
        raise ValueError('at most 64 retained witnesses')
    certificate = E.independence(retained, prime_bound=500, halving_limit=0)
    lower = certificate['rank_lower_bound']
    if not result['witness_rank_lower_bound'] <= lower <= result['rank_upper_bound']:
        raise ArithmeticError('inconsistent retained rank bounds')
    if not verify_independence(certificate):
        raise ArithmeticError('independent certificate verification failed')
    result.update(points=retained, independence=certificate,
                  witness_rank_lower_bound=lower,
                  rank_determined=lower == result['rank_upper_bound'])
    records = result.setdefault('published_point_witnesses', [])
    for point in accepted:
        record = dict(point=point, **source_provenance())
        if record not in records:
            records.append(record)
    return result
