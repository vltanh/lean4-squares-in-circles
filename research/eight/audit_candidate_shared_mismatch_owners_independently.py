"""Independent fixed-rational audit of the shared-mismatch owner theorem.

This program imports no author proof code.  It builds the seven nominal
projections from their explicit geometric formulas, forms the circle dual,
and recovers degree-four Bernstein coefficients by interpolation at five
rational points.  The author's coefficient-conversion formula is not used.
An isolated byte-identical author replay is an additional provenance check.
"""
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from math import comb
from pathlib import Path
import json
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
NAMES = {
    'manuscript': 'HAND_CANDIDATE_MIXED_OWNERS_WITH_TOTAL_MISMATCH.md',
    'definitions': 'HAND_CANDIDATE_MIXED_OWNERS_AND_TILT.md',
    'checker': 'verify_candidate_shared_mismatch_owner_duals.py',
    'data': 'candidate_mixed_owner_shared_mismatch_hand_data.json',
    'author_report': 'candidate_mixed_owner_shared_mismatch_hand_arithmetic.json',
}
OUTPUT = HERE / 'candidate_shared_mismatch_owners_independent_audit.json'
Q = F(9789, 2500)
EPSILON = F(1, 1000)
ALIGNED_LOSS = F(1001, 1000)
ALIGNED = (0, 2, 3, 4, 5)
D = (F(1), F(0), F(1))


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def plus(*polys):
    n = max(map(len, polys), default=0)
    return tuple(sum((p[k] if k < len(p) else F(0)) for p in polys)
                 for k in range(n))


def times_scalar(p, s):
    return tuple(s*x for x in p)


def product_poly(p, q):
    return tuple(sum(p[i]*q[k-i] for i in range(len(p))
                     if 0 <= k-i < len(q))
                 for k in range(len(p)+len(q)-1))


def value(p, x):
    ans = F(0)
    for c in reversed(p):
        ans = ans*x+c
    return ans


def solve(matrix, rhs):
    """Rational Gauss-Jordan elimination, independent of conversion formulas."""
    a = [list(row)+[v] for row, v in zip(matrix, rhs)]
    n = len(rhs)
    for j in range(n):
        pivot = next(i for i in range(j, n) if a[i][j])
        a[j], a[pivot] = a[pivot], a[j]
        d = a[j][j]
        a[j] = [x/d for x in a[j]]
        for i in range(n):
            if i != j:
                d = a[i][j]
                a[i] = [x-d*y for x, y in zip(a[i], a[j])]
    return [a[i][-1] for i in range(n)]


SAMPLE = [F(j, 4) for j in range(5)]
BERNSTEIN_MATRIX = [[comb(4, i)*x**i*(1-x)**(4-i)
                     for i in range(5)] for x in SAMPLE]


def force_numerators(owners):
    """Explicit 14-coordinate geometric projection table.

    A term (coordinate, constant, sine, cosine) denotes
    x_coordinate * (constant + sine*sin(t) + cosine*cos(t)).
    Coordinate indices 0..6 are a_H..a_E, 7..13 are b_H..b_E.
    """
    assert owners[0] == owners[2] == owners[4] == 1
    assert owners[3] == owners[5] == 3
    ga = {
        1: [(8, -1, 0, 0), (2, 0, 0, 1), (9, 0, -1, 0)],
        2: [(1, 0, -1, 0), (8, 0, 0, -1), (2, 1, 0, 0)],
        3: [(1, 0, 0, 1), (8, 0, -1, 0), (9, -1, 0, 0)],
        4: [(1, 1, 0, 0), (2, 0, -1, 0), (9, 0, 0, -1)],
    }
    eh = {
        1: [(13, -1, 0, 0), (0, 0, 0, 1), (7, 0, 1, 0)],
        2: [(6, 0, 1, 0), (13, 0, 0, -1), (0, 1, 0, 0)],
        3: [(6, 0, 0, 1), (13, 0, 1, 0), (7, -1, 0, 0)],
        4: [(6, 1, 0, 0), (0, 0, 1, 0), (7, 0, 0, -1)],
    }
    terms = [
        [(7, 1, 0, 0), (8, 1, 0, 0)], ga[owners[1]],
        [(9, 1, 0, 0), (10, 1, 0, 0)],
        [(3, 1, 0, 0), (11, -1, 0, 0)],
        [(11, 1, 0, 0), (12, 1, 0, 0)],
        [(5, 1, 0, 0), (13, 1, 0, 0)], eh[owners[6]],
    ]
    rows = []
    for line in terms:
        result = [(F(0),)*3 for _ in range(14)]
        for coordinate, constant, sine, cosine in line:
            numerator = (F(constant+cosine), F(2*sine), F(constant-cosine))
            result[coordinate] = plus(result[coordinate], numerator)
        rows.append(result)
    return rows


def independently_rebuild(row):
    assert all(type(n) is int and n >= 0 for n in row['lambda'])
    assert all(type(n) is int and n > 0 for n in row['mu'])
    assert len(row['lambda']) == len(row['mu']) == 7
    lambdas = [F(n, 10**8) for n in row['lambda']]
    mus = [F(n, 10**8) for n in row['mu']]
    kappas = [F(0)]*35
    used = set()
    for index, n in row['cone']:
        assert type(index) is int and 0 <= index < 35 and index not in used
        assert type(n) is int and n > 0
        used.add(index)
        kappas[index] = F(n, 10**8)
    forces = force_numerators(row['owners'])
    C = [plus(*(times_scalar(forces[i][j], lambdas[i]) for i in range(7)))
         for j in range(14)]
    cone_rhs = F(0)
    ratios = [(F(1, 2), F(1)), (F(1, 20), F(4, 5)),
              (F(0), F(1)), (F(0), F(1)), (F(1, 20), F(4, 5)),
              (F(1, 2), F(1)), (F(0), F(1))]
    for i, (low_ratio, high_ratio) in enumerate(ratios):
        low, high, lower_ratio, upper_ratio, bcap = kappas[5*i:5*i+5]
        floor = F(7, 12) if i in (1, 4) else F(447, 800)
        ceiling = F(349, 250) if i in (1, 4) else F(283, 200)
        ca = low-high-low_ratio*lower_ratio+high_ratio*upper_ratio
        cb = lower_ratio-upper_ratio-bcap
        C[i] = plus(C[i], times_scalar(D, ca))
        C[7+i] = plus(C[7+i], times_scalar(D, cb))
        cone_rhs += floor*low-ceiling*high-F(9, 10)*bcap
    loss = EPSILON*(ALIGNED_LOSS*max(lambdas[i] for i in ALIGNED)+2*lambdas[6])
    lo, hi = F(row['lo']), F(row['hi'])
    assert lo < hi and (hi <= 0 or lo >= 0)
    width = (F(1), F(1 if lo >= 0 else -1), F(0))
    L = plus(times_scalar(D, cone_rhs-loss),
             times_scalar(D, sum(lambdas[i] for i in ALIGNED)),
             times_scalar(width, lambdas[1]+lambdas[6]),
             *(times_scalar(c, F(1, 2)) for c in C))
    P = plus(product_poly(D, L),
             times_scalar(product_poly(D, D), -Q*sum(mus)),
             *(times_scalar(plus(product_poly(C[i], C[i]),
                                 product_poly(C[7+i], C[7+i])), -1/(4*mus[i]))
               for i in range(7)))
    assert len(P) == 5
    evaluations = [value(P, lo+(hi-lo)*x) for x in SAMPLE]
    bernstein = solve(BERNSTEIN_MATRIX, evaluations)
    # Reconstruct the polynomial independently in the global z-coordinate.
    reconstructed = (F(0),)*5
    for i, coefficient in enumerate(bernstein):
        piece = (F(1),)
        for _ in range(i):
            piece = product_poly(piece, (-lo, F(1)))
        for _ in range(4-i):
            piece = product_poly(piece, (hi, -F(1)))
        reconstructed = plus(reconstructed,
                             times_scalar(piece, coefficient*comb(4, i)/(hi-lo)**4))
    assert reconstructed == P
    lower = row['bernstein_lower_numerators']
    assert len(lower) == 5 and all(type(n) is int and n > 0 for n in lower)
    assert all(b >= F(n, 10**12) for b, n in zip(bernstein, lower))
    return min(lower)


def scalar_premises():
    eps_cusp = F(1, 500)
    assert ALIGNED_LOSS > 1+eps_cusp/4+eps_cusp**2/12
    assert EPSILON <= eps_cusp
    assert F(3, 8)-F(3, 8)**3/3 > F(7, 20)
    assert F(141, 100)**2 < 2
    assert F(1, 2)+F(141, 100)/24 == F(447, 800)
    assert (F(283, 200)+F(1, 2))**2+F(1, 4) > Q
    assert 2*(F(9, 10)+F(1, 2))**2 > Q
    assert F(4, 5)*F(7, 12) < F(1, 2)
    assert (F(349, 250)+F(1, 2))**2+(F(349, 5000)+F(1, 2))**2 > Q
    assert Q < 4 and EPSILON < F(3, 200) < F(2, 5)


def main():
    before = {name: digest(HERE/name) for name in NAMES.values()}
    data = json.loads((HERE/NAMES['data']).read_text())
    author = json.loads((HERE/NAMES['author_report']).read_text())
    assert data['mode'] == 'mixed' and data['Q'] == str(Q)
    assert data['epsilon'] == str(EPSILON) and data['aligned_loss'] == str(ALIGNED_LOSS)
    assert data['shared_total_error'] is True and data['unresolved'] == []
    assert data['degree'] == 4 and data['denominator'] == 10**8
    assert data['bernstein_denominator'] == 10**12
    patterns = {(1, g, 1, 3, 1, 3, h) for g, h in product(range(1, 5), repeat=2)
                if (g, h) != (1, 2)}
    assert len(patterns) == 15
    cover = {p: [] for p in patterns}
    minima = {p: 10**100 for p in patterns}
    seen = set()
    for row in data['rows']:
        p = tuple(row['owners'])
        lo, hi = F(row['lo']), F(row['hi'])
        key = (p, lo, hi)
        assert p in patterns and key not in seen
        seen.add(key)
        minima[p] = min(minima[p], independently_rebuild(row))
        cover[p].append((lo, hi))
    summary = []
    for p in sorted(patterns):
        endpoint = -F(3, 8)
        for lo, hi in sorted(cover[p]):
            assert lo == endpoint
            endpoint = hi
        assert endpoint == F(3, 8)
        summary.append({'owners': list(p), 'closed_cells': len(cover[p]),
                        'minimum_numerator': minima[p]})
    scalar_premises()
    assert len(seen) == 729 and min(minima.values()) == 231527
    assert author['input_sha256'] == before[NAMES['data']]
    assert author['checker_sha256'] == before[NAMES['checker']]
    assert author['owner_patterns'] == 15 and author['quartics'] == len(seen)
    assert author['bernstein_coefficients'] == 5*len(seen)
    assert author['pattern_summary'] == summary
    with tempfile.TemporaryDirectory(prefix='independent_shared_owner_replay_') as tmp:
        root = Path(tmp)
        for key in ('checker', 'data'):
            shutil.copy2(HERE/NAMES[key], root/NAMES[key])
        run = subprocess.run([sys.executable, str(root/NAMES['checker'])],
                             cwd=root, capture_output=True, text=True, check=True)
        assert not run.stderr
        assert (root/NAMES['author_report']).read_bytes() == (HERE/NAMES['author_report']).read_bytes()
    after = {name: digest(HERE/name) for name in NAMES.values()}
    assert after == before
    result = {
        'status': 'PASS_INDEPENDENT_SHARED_MISMATCH_OWNER_PROOF_AND_FIXED_ARITHMETIC',
        'Q': str(Q), 'epsilon': str(EPSILON), 'aligned_loss': str(ALIGNED_LOSS),
        'sha256': before,
        'independent_checker_sha256': digest(Path(__file__)),
        'independent_projection_table': 'explicit nominal geometric formulas; no author imports',
        'coefficient_method': 'rational five-point Bernstein interpolation and global polynomial reconstruction',
        'owner_patterns': 15, 'quartics': len(seen), 'bernstein_coefficients': 5*len(seen),
        'minimum_printed_coefficient': str(F(min(minima.values()), 10**12)),
        'closed_pattern_cover': 'exactly [-3/8,3/8] for every forbidden mixed pattern',
        'author_replay': 'byte-identical in an isolated flat directory; no stderr',
        'unchanged_inputs': True, 'pattern_summary': summary,
    }
    OUTPUT.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ('sha256', 'pattern_summary')}, indent=2))


if __name__ == '__main__':
    main()
