"""Verify the rational tables printed in DIAGONAL_SIDE_EXCLUSION.md."""
from fractions import Fraction as F
from pathlib import Path

M = 1_000_000
R = F(79, 40)
source = Path(__file__).with_name('DIAGONAL_SIDE_EXCLUSION.md').read_text()

def table(header):
    lines = source[source.index(header):].splitlines()[2:]
    result = []
    for line in lines:
        if not line.startswith('|'):
            break
        result.append([F(x.strip()) for x in line.strip('|').split('|')])
    return result

parameters = table('| Row | a | b | zeta | D | E |')
roots = table('| Row | s_a | s_b | s_zeta | s_D | s_E |')
bounds = table('| Row | n_zeta | m_zeta | n_D | u_zeta | n_E |')
assert len(parameters) == len(roots) == len(bounds) == 16
rm, rp = F(1414213, M), F(1414214, M)
assert rm * rm < 2 < rp * rp
previous = F(7, 20)
for index, (par, rad, bnd) in enumerate(zip(parameters, roots, bounds), 1):
    row, a, b, zeta, di, ei = par
    assert row == rad[0] == bnd[0] == index
    assert a == previous and a < b <= 1
    previous = b
    d, de = di / M, ei / M
    assert 0 <= zeta <= d < 1 and 0 <= de <= d
    sa, sb, sz, sd, se = [x / M for x in rad[1:]]
    nz, mz, nd, uz, ne = [x / M for x in bnd[1:]]
    low = lambda root: root - F(1, M)
    tau = lambda f: (1 - f * a) / (1 - f)
    for upper, square in [(sa, 1+a*a), (sb, 1+b*b),
                          (sz, 1+tau(zeta)**2),
                          (sd, 1+tau(d)**2), (se, 1+tau(de)**2)]:
        assert low(upper)**2 < square <= upper**2
    assert d >= 1 - (rm-b)/sb
    assert de >= 1 - (rm-F(17,20)*b)/sb
    assert (tau(d)-a)/(low(sa)*low(sd)) < F(1,2)
    def bn(f, root):
        return rp + (1+a)/low(sa) - R*(1+a*tau(f))/(sa*root)
    bt = (1-a)/low(sa) * (R/((1-zeta)*low(sz))-1)
    assert nz >= bn(zeta, sz) and mz >= bt
    assert nd >= bn(d, sd) and ne >= bn(de, se)
    assert uz >= 1 + ((1-zeta)*sb-rm)/b
    assert F(7,10) < nz <= nd < F(93,100)
    assert 0 < mz < F(9,20) and ne < F(91,100) and uz > 0
    if zeta:
        assert (1+nz)**2 * (1+(mz/nz)**2) < R*R-F(1,200)
    assert (1+nd)**2 + (uz+mz)**2 < R*R-F(1,200)
    print(f'row {index}: PASS')
assert previous == 1

# The four upper tau bounds imported from the proximity table.
for b, root_upper, tau_upper in [
    (F(2,5), F(107704,100000), F(26,25)),
    (F(1,2), F(111804,100000), F(9,8)),
    (F(3,5), F(116620,100000), F(47,40)),
    (F(2,3), F(120186,100000), F(121,100)),
]:
    assert root_upper**2 >= 1+b*b
    assert b + (1-b)*root_upper/(F(141421,100000)-b) < tau_upper

# The five-range improvement -T < 7/20 when R < 2.
for a, tau_upper, e_upper, v_lower in [
    (F(1,3),F(26,25),F(93,200),F(63,100)),
    (F(2,5),F(9,8),F(9,20),F(11,20)),
    (F(1,2),F(47,40),F(197,500),F(11,25)),
    (F(3,5),F(121,100),F(1,3),F(1,3)),
    (F(2,3),F(5,4),F(31,100),F(27,100)),
]:
    e_squared = (tau_upper-a)**2 / ((1+tau_upper**2)*(1+a*a))
    v_squared = (1-a)**2/(1+a*a)
    assert e_squared < e_upper**2 and v_squared > v_lower**2
    assert 2*e_upper-v_lower <= F(7,20)
assert (F(191,100)**2 + F(1,4)) < R*R
print('PASS: 16 printed rows, root brackets, margins, and auxiliary bounds')
