#!/usr/bin/env python3
"""Exact rational companion to the all-sign small-angle row hand terminal.

This checks constants, sign reserves, support expansions, and every slope
in the scalar minimization. The continuous geometry and path-variation
argument are proved in ALL_SIGN_SMALL_ANGLE_THREE_LINK_ROW_HAND_TERMINAL.md.
No interval-box cover or whole-mask closure is asserted by this script.
"""

from fractions import Fraction as F
import json


checks = []


def exact(name, actual, expected):
    actual, expected = F(actual), F(expected)
    assert actual == expected, (name, actual, expected)
    checks.append({"name": name, "relation": "=", "value": str(actual)})


def positive(name, value):
    value = F(value)
    assert value > 0, (name, value)
    checks.append({"name": name, "relation": ">0", "value": str(value)})


def nonnegative(name, value):
    value = F(value)
    assert value >= 0, (name, value)
    checks.append({"name": name, "relation": ">=0", "value": str(value)})


Q, a, B, k, T, rho = F(1105, 256), F(46), F(27, 2), F(207, 16), F(211, 4), F(91, 60)
b, U = F(1, 50), F(1, 12)
z, delta = 1 - b*b, b/(2 - b*b)
c = (1 - b - 3*b*b - 4*b*b*b)/2
P, C, J = (a + k)/2, (a - k)/2, B + k/2
lam = 5*k/(8*z)
eplus, eminus = B - k/2 - J*delta, k/2 - J*delta
p = C + P*delta - k*c
q = eminus + C - P*delta - lam
epsilon = q - p - a*U/z

exact("z", z, F(2499, 2500))
exact("delta", delta, F(50, 4999))
exact("pair signed-variation coefficient c", c, F(61173, 125000))
exact("main support alpha coefficient P", P, F(943, 32))
exact("main support signed coefficient C", C, F(529, 32))
exact("shoulder aggregate alpha coefficient J", J, F(639, 32))
exact("owner horizontal-drift coefficient lambda", lam, F(215625, 26656))
exact("positive shoulder coefficient eplus", eplus, F(1092825, 159968))
exact("negative shoulder coefficient eminus", eminus, F(1002843, 159968))
exact("endpoint negative payment p", p, F(104924920311, 9998000000))
exact("endpoint positive payment q", q, F(1921027237, 133253344))
exact("final positive reserve epsilon", epsilon, F(6513193240933, 74955006000000))

# Center and owned-axis estimates.
exact("strict center-radius squared reserve", rho*rho + rho + F(1, 2) - Q, F(31, 57600))
positive("alpha lower bound z", z)
positive("alpha-difference bound b/z <= 2b", 2*b - b/z)
positive("frame dot-product positive lower bound", 1 - 2*b*b*(1 + 4*b*b))
exact("signed determinant coefficient", z - 2*b*b, 1 - 3*b*b)
exact("owned-axis support coefficient", ((1 - 3*b*b) - b*(1 + 4*b*b))/2, c)
positive("owned-axis support variation positive", c)
positive("aligned-width minimum valid on beta range", 1 - b)
exact("halfwidth upper bound", (1 + b)/2, F(51, 100))

# Three unit-center gaps and endpoint horizontal bands.
exact("row square-root lower-bound reserve", 1 - U*U - F(239, 240)**2, F(79, 57600))
exact("row horizontal-span rational lower bound", 2 + F(239, 240), F(719, 240))
exact("endpoint horizontal-coordinate lower bound", F(719, 240) - rho, F(71, 48))
exact("endpoint outward edge lower bound", F(71, 48) - F(51, 100), F(1163, 1200))
C0 = (T - a*F(1163, 1200))/B
exact("shoulder edge band C0", C0, F(4901, 8100))
exact("endpoint horizontal-pair upper band", rho - F(3, 2) + C0, F(1259, 2025))
exact("horizontal-pair upper-band reserve", F(5, 8) - F(1259, 2025), F(53, 16200))
positive("horizontal-pair order reserve", F(71, 48) - C0 - F(51, 100))

# Every separator sign and both ownership choices are covered by these bounds.
exact("main-row steep projection upper bound", 2*b*rho + U, F(18, 125))
positive("main-row steep-axis rejection reserve", 1 - (2*b*rho + U))
positive("main-row reversed shallow-axis rejection reserve", 1 - b*U)
positive("endpoint-pair shallow-axis rejection reserve", 1 - F(5, 8) - 2*b*rho)
positive("endpoint-pair downward-axis rejection reserve", 1 - b*F(5, 8))

# Fixed support vectors: signs and exactly expanded alpha/beta coefficients.
positive("main support shallow dot sign", a*z - k*b)
positive("main support steep dot sign", k*z - a*b)
positive("shoulder support shallow dot sign", B*z - k*b)
positive("shoulder support steep dot sign", k*z - B*b)
exact("main vector squared norm", a*a + k*k, 23*23*Q)
exact("shoulder vector squared norm", B*B + k*k, 9*9*Q)
exact("total vector length coefficient", 2*23 + 2*9, 64)

# Direct absolute-support expansion in each guaranteed sign sector.
# Each tuple consists of (alpha coefficient, beta coefficient).
support_A = ((a + k)/2, (k - a)/2)
support_D = ((a + k)/2, (a - k)/2)
support_E = ((B + k)/2, (B - k)/2)
support_G = ((B + k)/2, (k - B)/2)
for name, actual, expected in [
    ("A alpha support", support_A[0], P),
    ("A signed support", support_A[1], -C),
    ("D alpha support", support_D[0], P),
    ("D signed support", support_D[1], C),
    ("E aggregate alpha after short chain", support_E[0] + B/2, J),
    ("G aggregate alpha after short chain", support_G[0] + B/2, J),
    ("E positive beta before alpha loss", support_E[1] + B/2, B - k/2),
    ("E negative beta before alpha loss", -support_E[1] + B/2, k/2),
    ("G reflected positive beta before alpha loss", -support_G[1] + B/2, B - k/2),
    ("G reflected negative beta before alpha loss", support_G[1] + B/2, k/2),
]:
    exact(name, actual, expected)
exact("complete constant in circle support", 3*a + 2*B + 2*k + (a + B + 2*k), 64*Q)

# The four possible scalar sectors on either side of x=0 are all affine.
# These entries are the positive costs away from the minimizing breakpoint.
scalar_slopes = {
    "x_nonnegative_y_negative_cost": k*c + eminus - lam,
    "x_nonnegative_zero_to_x_cost": eplus - k*c,
    "x_nonnegative_beyond_x_cost": k*c + eplus,
    "x_nonpositive_below_x_cost": k*c + eminus - lam,
    "x_nonpositive_x_to_zero_cost": k*c - eminus,
    "x_nonpositive_y_positive_cost": k*c + eplus,
}
for name, slope in scalar_slopes.items():
    positive(name, slope)
exact("minimum at y=0 for positive x", k*c - C - P*delta, -p)
exact("minimum at y=x for negative x", eminus - lam + C - P*delta, q)
positive("p positive", p)
positive("q exceeds p", q - p)
nonnegative("path coefficient ac at least q", a*c - q)
c1, c2 = (q - p)/2, (q + p)/2
exact("positive x representation f(x)", c1 - c2, -p)
exact("negative x representation f(x)", c1 + c2, q)
nonnegative("path remaining coefficient", a*c - c2 - c1)
positive("final near-row reserve", epsilon)
positive("F equality coefficient", B*(1 - delta))
positive("E/G positive-beta equality coefficient", k*c + eplus)
positive("E/G negative-beta equality coefficient", k*c + eminus - lam)

report = {
    "status": "PASS",
    "scope": "Exact arithmetic companion only; all-sign seven-original hand terminal; no mask closure claimed.",
    "guards": {
        "row_total_vertical_variation": str(U),
        "all_seven_abs_signed_beta": str(b),
        "short_chain": "EF and FG actual horizontal projection separation",
        "endpoint_height_orders": "E above A and G above D, or both reflected below",
    },
    "check_count": len(checks),
    "checks": checks,
}
print(json.dumps(report, indent=2, sort_keys=True))
