"""Exact arithmetic replay of the mixed full-side lower-central hand proof.

Python standard library only. No numerical optimization, interval sampling,
Lean, or CI. The geometric coverage argument is in the companion manuscript.
"""
from fractions import Fraction as F
import json

Q = F(1105, 256)
rho = F(91, 60)
A, c = F(503, 480), F(221, 600)
d = F(11, 30)

checks = {
    "radius_squared": F(133, 64)**2 - Q,
    "horizontal_proxy_margin": d - (F(17, 20) - F(15, 31)),
    "vertical_proxy_margin": 1 - (F(133, 64) - F(3, 5) - F(15, 31)),
    "orientation_b_range": F(21, 29) - F(5, 7),
    "orientation_root_range": F(5, 7)**2 - F(1, 2),
    "first_axis_quadratic": F(1, 2) - d - F(105, 788),
    "second_axis_large_a": F(3, 8) - d,
    "second_axis_small_a": F(1, 2) - F(9, 40) - F(11, 42),
    "sqrt7_comparison": 7 - F(13, 5)**2,
    "profile_transition": F(1, 4) - (F(31, 50)-c)**2 - (A-F(37, 60))**2,
    "upper_vertical_order": 1-F(3, 4)**2-(rho-F(3, 5)-F(15, 31))**2,
    "left_profile_vertex": 1-F(17, 60)**2-F(269, 300)**2,
    "right_profile_vertex": 1-F(3, 4)**2-F(389, 600)**2,
    "high_central_axis": F(1, 2)-F(2963, 5952),
    "high_central_derivative": F(3353, 4960),
    "broader_profile_transition": F(1, 4)-(F(161, 300)-c)**2-(A-F(7, 12))**2,
    "broader_profile_low_center": 1-F(1, 4)**2-F(289, 300)**2,
    "broader_profile_high_center": 1-F(11, 60)**2-F(49, 50)**2,
}
assert d/2 + F(2, 7) == F(197, 420)
assert 1 / (16 * F(197, 420)) == F(105, 788)
assert checks["first_axis_quadratic"] == F(1, 11820)
assert checks["right_profile_vertex"] == F(6179, 360000)
assert F(97, 100) - F(7, 20) == F(31, 50)
assert rho - c - F(1, 2) == F(389, 600)
assert rho - F(31, 50) == F(269, 300)
assert A - F(1, 2) > F(29, 60)
assert A < F(13, 12)
assert F(13, 30)-F(97, 100) == -F(161, 300)
assert F(3, 2)-F(161, 300) == F(289, 300)
assert rho-F(161, 300) == F(49, 50)
assert 2*(F(133, 64)-F(3, 2))*(F(3, 2)-F(168, 155))+rho-F(3, 2) == F(2963, 5952)
assert 2*(F(133, 64)+F(168, 155)-3)-1 == -F(3353, 4960)
assert all(value > 0 for value in checks.values())

print(json.dumps({"result": "PASS", "positive_reserves": {
    name: str(value) for name, value in checks.items()
}}, indent=2))
