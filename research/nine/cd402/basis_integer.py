"""Integer-only kernel reconstruction; no discovery or optimization library."""
from fractions import Fraction
from math import gcd, lcm


def nullvector(matrix, ncols):
    """A primitive integer vector for a rank-(ncols-1) rational kernel.

    Fraction-free Bareiss elimination is merely a way to propose weights.
    The caller MUST check nonnegativity and the complete residual reserve.
    """
    if not ncols:
        raise ValueError('empty multiplier vector')
    A = [list(row) for row in matrix if any(row)]
    if any(len(row) != ncols for row in A):
        raise ValueError('ragged matrix')
    r = 0
    previous = 1
    pivots = []
    for col in range(ncols):
        possible = [i for i in range(r, len(A)) if A[i][col]]
        if not possible:
            continue
        p = min(possible, key=lambda i: abs(A[i][col]))
        A[r], A[p] = A[p], A[r]
        pivot = A[r][col]
        for i in range(r + 1, len(A)):
            entry = A[i][col]
            for j in range(col + 1, ncols):
                num = pivot * A[i][j] - entry * A[r][j]
                value, rem = divmod(num, previous)
                if rem:
                    raise ArithmeticError('nonexact Bareiss division')
                A[i][j] = value
            A[i][col] = 0
        pivots.append(col)
        previous = pivot
        r += 1
        if r == len(A):
            break
    if len(pivots) != ncols - 1:
        raise ValueError('kernel is not one-dimensional')
    free = next(j for j in range(ncols) if j not in pivots)
    v = [Fraction(0) for _ in range(ncols)]
    v[free] = Fraction(1)
    for i in range(len(pivots) - 1, -1, -1):
        j = pivots[i]
        v[j] = -sum((A[i][k] * v[k] for k in range(j + 1, ncols)), Fraction(0)) / A[i][j]
    scale = lcm(*(x.denominator for x in v))
    w = [int(x * scale) for x in v]
    divisor = gcd(*w)
    if not divisor:
        raise ValueError('zero kernel')
    w = [x // divisor for x in w]
    if max(w) <= 0:
        w = [-x for x in w]
    return w


def reconstruct(rows, chosen, columns=None):
    if not chosen or len(chosen) != len(set(chosen)):
        raise ValueError('repeated/empty rows')
    if any(not isinstance(i, int) or isinstance(i, bool) or not 0 <= i < len(rows) for i in chosen):
        raise ValueError('bad row')
    used = [rows[i] for i in chosen]
    active = sorted({j for c, b in used for j in c})
    if columns is None:
        columns = active
    if len(columns) != len(set(columns)) or any(j not in active for j in columns):
        raise ValueError('bad variable equations')
    return nullvector([[c.get(j, 0) for c, b in used] for j in columns], len(chosen))


def reserve(rows, chosen, weights):
    if len(chosen) != len(weights) or min(weights) < 0 or max(weights) == 0:
        raise ValueError('bad multipliers')
    res = {}
    rhs = 0
    for i, w in zip(chosen, weights):
        c, b = rows[i]
        rhs += w * b
        for j, a in c.items():
            res[j] = res.get(j, 0) + w * a
    v = -rhs - 4 * sum(abs(a) for a in res.values())
    if v <= 0:
        raise ValueError('nonpositive exact reserve')
    return v
