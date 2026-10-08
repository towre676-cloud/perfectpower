"""Hermite bases and Smith inclusions for a prime-preimage coefficient lattice.

For the RREF relation space R in F_p^r, L=Z^r+(1/p)R is a lattice
of formal coefficients. Dependencies among the actual curve points need
not be known: the lattice index is NOT asserted to be a group index.
Rows are basis vectors. Our upper row Hermite convention reduces entries
above a pivot modulo the positive diagonal entry in that pivot's column.
"""
from .integer_lifting import smith_certificate, verify_smith, _multiply


def matrices(prime, basis, width):
    if type(prime) is not int or prime not in (2, 3, 5, 7, 11, 13):
        raise ValueError('prime 2, 3, 5, 7, 11 or 13 required')
    if type(width) is not int or not 0 <= width <= 4:
        raise ValueError('width zero through four required')
    if type(basis) is not list or len(basis) > width:
        raise ValueError('RREF rows required')
    pivots = []
    for row in basis:
        if type(row) is not list or len(row) != width or any(type(x) is not int or not 0 <= x < prime for x in row):
            raise ValueError('literal residue row required')
        pivot = next((j for j, x in enumerate(row) if x), None)
        if pivot is None or row[pivot] != 1 or (pivots and pivot <= pivots[-1]):
            raise ValueError('ordered unit pivots required')
        pivots.append(pivot)
    if any(row[j] != int(i == k) for i, row in enumerate(basis) for k, j in enumerate(pivots)):
        raise ValueError('reduced pivot columns required')
    hermite = [[prime * int(i == j) for j in range(width)] for i in range(width)]
    inclusion = [[int(i == j) for j in range(width)] for i in range(width)]
    for row, pivot in zip(basis, pivots):
        hermite[pivot] = list(row)
        inclusion[pivot] = [prime * int(pivot == j) - (row[j] if j != pivot else 0) for j in range(width)]
    return hermite, inclusion


def coefficient_presentation(prime, basis, width):
    h, inclusion = matrices(prime, basis, width)
    return dict(schema='pp-prime-preimage-coefficient-lattice/1', prime=prime,
                width=width, relation_basis=basis, denominator=prime,
                hermite_numerator_rows=h, source_inclusion_rows=inclusion,
                numerator_smith=smith_certificate(h) if width else None,
                inclusion_smith=smith_certificate(inclusion) if width else None,
                coefficient_index=prime**len(basis),
                group_index_claimed=False)


def verify_coefficient_presentation(cert, prime, basis, width):
    """Check Hermite shape, source inclusion, and unimodular Smith transcripts."""
    try:
        from .elliptic_certificate_verifier import fields
        fields(cert, 'schema prime width relation_basis denominator hermite_numerator_rows source_inclusion_rows numerator_smith inclusion_smith coefficient_index group_index_claimed')
        if cert['schema'] != 'pp-prime-preimage-coefficient-lattice/1' or cert['group_index_claimed'] is not False:
            return False
        for key, expected in (('prime', prime), ('width', width), ('denominator', prime), ('coefficient_index', prime**len(basis))):
            if type(cert[key]) is not int or cert[key] != expected:
                return False
        # Validate every nested residue before comparing (bool aliases int).
        h, inclusion = matrices(cert['prime'], cert['relation_basis'], cert['width'])
        if cert['relation_basis'] != basis:
            return False
        for key, expected in (('hermite_numerator_rows', h), ('source_inclusion_rows', inclusion)):
            rows = cert[key]
            if type(rows) is not list or any(type(row) is not list or any(type(x) is not int for x in row) for row in rows) or rows != expected:
                return False
        if not width:
            return cert['numerator_smith'] is None and cert['inclusion_smith'] is None
        if _multiply(inclusion, h) != [[prime * int(i == j) for j in range(width)] for i in range(width)]:
            return False
        if any(h[i][j] != 0 for i in range(width) for j in range(i)):
            return False
        if any(not 0 <= h[i][j] < h[j][j] for i in range(width) for j in range(i + 1, width)):
            return False
        d = len(basis)
        for key, matrix, factors in (
            ('numerator_smith', h, [1]*d + [prime]*(width-d)),
            ('inclusion_smith', inclusion, [1]*(width-d) + [prime]*d)):
            proof = cert[key]
            if not verify_smith(proof) or proof['matrix'] != matrix or proof['smith_factors'] != factors:
                return False
        return True
    except (ValueError, TypeError, KeyError, IndexError, ArithmeticError):
        return False
