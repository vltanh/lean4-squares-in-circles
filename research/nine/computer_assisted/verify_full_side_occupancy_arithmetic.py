"""Exact arithmetic audit for the full (2,1,2) actual-four hand caller.

All geometric covering arguments are in the two companion manuscripts.
This independently reconstructs the polynomial rather than importing a
producer. Standard-library Fraction arithmetic only; no Lean or CI.
"""
from fractions import Fraction as F
import json


def mul(p, q):
    out = [F(0)] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        for j, y in enumerate(q):
            out[i+j] += x*y
    return out


def derivative(p):
    return [i*p[i] for i in range(1, len(p))]


def evaluate(p, x):
    return sum(c*x**i for i, c in enumerate(p))


left = [1440000*x for x in mul([4, 4, 1], [1, 0, 1])]
right = mul([1, 2, 1], mul([2147, 166], [2147, 166]))
poly = [a-b for a, b in zip(left, right)]
assert poly == [1150391, -4172022, 1137227, 4992084, 1412444]
second = derivative(derivative(poly))
assert second == [2274454, 29952504, 16949328]
assert all(x > 0 for x in second)
anchor = F(3, 7)
assert evaluate(poly, anchor) == F(28507100, 2401)
assert evaluate(derivative(poly), anchor) == -F(610980, 343)

A = F(503, 480)
c = F(221, 600)
e = F(7, 16)-c
zeta = F(2211, 4000)
J = F(23, 150)
A0 = 1-F(139, 120)+F(15, 31)-F(1, 128)
B0 = F(83, 620)
cL, cR = A0-F(1, 10), B0-F(1, 10)

assert A-F(2147, 2400) == J
assert A-zeta == F(2971, 6000)
assert A0 == F(18911, 59520)
assert cL == F(12959, 59520)
assert cR == F(21, 620)
assert F(1, 60)+J == F(17, 100)
assert F(4, 15)+J == F(21, 50)
assert -F(139, 120)+F(97, 100) == -F(113, 600)
assert -F(113, 600)+F(4, 5) == F(367, 600)
assert -F(139, 120)+F(59, 60) == -F(7, 40)
assert -F(113, 600)+F(5, 6) == F(129, 200)
assert F(109, 930) == -F(7, 20)+F(869, 1860)

checks = {
    "quartic_curvature": second[0]-2000000,
    "quartic_anchor_value": evaluate(poly, anchor)-10000,
    "quartic_anchor_derivative": 2000-abs(evaluate(derivative(poly), anchor)),
    "positive_squaring_target": F(2147, 2400),
    "endpoint_axis_order": F(1, 2)-e*F(3, 2),
    "zero_center_root_comparison": F(1, 4)-e*e-(A-zeta)**2,
    "zero_center_low_band": F(47, 80)-zeta,
    "zero_center_disk_gap": F(11, 36)-zeta*zeta,
    "near_main_margin": F(15, 31)-F(5, 48)-F(3, 8),
    "zero_lower_band": F(7, 16)-F(113, 600),
    "zero_proxy_top_above_section": A0-F(3, 10),
    "high_shoulder_above_three_fifths": F(367, 600)-F(3, 5),
    "opposite_main_orders": F(6, 5)-F(31, 30),
    "central_between_positive_root": F(1, 4)-F(1, 900)-F(49, 100)**2,
    "central_between_gap": F(30, 31)+F(49, 100)-F(31, 30),
    "middle_central_floor": F(109, 930)-F(1, 10),
    "equal_bottom_central_below_impossible": F(3, 5)+F(97, 100)-F(91, 60),
    "central_zero_order": -F(7, 40)+F(19, 48),
    "equal_bottom_center_above_section": F(129, 200)-F(3, 10),
    "equal_bottom_center_above_zeros": F(129, 200)-F(7, 16),
    "equal_bottom_section_gap": F(2, 5)-2*J,
    "equal_bottom_section_bottom": F(3, 10)-F(5, 48),
    "equal_bottom_exterior_margin": F(49, 60)-F(47, 60),
    "mixed_left_top_margin": cL-F(1, 6),
    "mixed_right_location_root": 2*cR-F(1, 16),
    "mixed_central_zero_order": 1-(zeta+F(4, 15))**2-(F(7, 16)-B0)**2,
    "mixed_left_active": F(1, 2)-F(21, 50),
    "mixed_shared_frame": 4*cL*cR-F(17, 100)**2,
    "low_side_proxy_top_above_edge": cL-J,
    "low_side_proxy_top_below_one_third": F(1, 3)-cL,
    "low_side_single_axis_quadratic": cL-F(2401, 11250),
    "low_side_high_center_band": F(1, 4)-(F(3, 5)-c)**2-(A-F(49, 80))**2,
    "low_side_high_band_order": 1-F(49, 80)**2-F(31, 40)**2,
    "low_side_high_band_vertical_gap": 1-F(49, 80)**2-F(3, 4)**2,
    "low_side_high_band_floor": F(23, 48)-F(1, 10),
    "extended_low_side_clearance_loss": F(9, 1000)-F(247, 1860)**2/2,
    "extended_low_side_single_axis": F(10069, 46500)-F(2401, 11250),
    "extended_low_side_center_band": F(2, 5)-F(29, 120),
    "extended_low_side_inward_axis": F(10069, 46500)-F(1, 6),
    "extended_low_side_horizontal_axis": F(10069, 46500)-J,
}
assert checks["mixed_shared_frame"] == F(45993, 76880000)
assert all(value > 0 for value in checks.values())

print(json.dumps({
    "result": "PASS",
    "quartic_coefficients_ascending": [str(x) for x in poly],
    "positive_reserves": {name: str(value) for name, value in checks.items()},
}, indent=2))
