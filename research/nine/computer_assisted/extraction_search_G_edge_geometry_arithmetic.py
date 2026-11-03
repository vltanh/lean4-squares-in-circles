#!/usr/bin/env python3
"""Exact scalar arithmetic for the G projection / BF / AE hand consequences."""
from fractions import Fraction as F
from pathlib import Path
import argparse
import json


def checks():
    rho = F(91, 60)
    edge = F(49, 64)
    f_lower = -F(115, 432)
    f_upper = edge - F(1, 2)
    b_lower = -F(31, 60)
    b_upper = -F(27, 64)
    g_ab_lower = F(16, 37)
    g_any_lower = F(7, 20)
    out = {}

    out["inset_radical_square_reserve"] = F(1, 8) - g_any_lower**2
    assert out["inset_radical_square_reserve"] == F(1, 400) > 0
    out["F_right_of_B_reserve"] = f_lower - b_upper
    assert out["F_right_of_B_reserve"] == F(269, 1728) > 0
    out["BF_horizontal_upper"] = f_upper - b_lower
    assert out["BF_horizontal_upper"] == F(751, 960)
    out["BF_inset_lower"] = g_ab_lower + g_any_lower
    assert out["BF_inset_lower"] == F(579, 740)
    out["BF_cone_reserve"] = out["BF_inset_lower"] - out["BF_horizontal_upper"]
    assert out["BF_cone_reserve"] == F(1, 7104) > 0
    out["wrong_BF_order_reserve"] = F(1, 25) + out["BF_cone_reserve"]
    assert out["wrong_BF_order_reserve"] > 0

    out["AE_right_overlap_reserve"] = 2 + g_ab_lower - rho - edge
    assert out["AE_right_overlap_reserve"] == F(5333, 35520)
    out["AE_right_extra_reserve"] = out["AE_right_overlap_reserve"] - F(3, 20)
    assert out["AE_right_extra_reserve"] == F(1, 7104) > 0
    out["AE_left_overlap_reserve"] = F(59, 64) + 1 + g_any_lower - rho
    assert out["AE_left_overlap_reserve"] == F(145, 192) > F(3, 20)
    out["AE_horizontal_distance_upper"] = 1 - F(3, 20)
    assert out["AE_horizontal_distance_upper"] == F(17, 20) < 1

    out["F_horizontal_upper"] = f_upper
    assert f_upper == F(17, 64)
    out["F_strip_left_reserve"] = g_any_lower + f_lower - F(1, 12)
    out["F_strip_right_reserve"] = g_any_lower - f_upper - F(1, 12)
    assert out["F_strip_left_reserve"] == F(1, 2160) > 0
    assert out["F_strip_right_reserve"] == F(1, 960) > 0

    return {"status": "PASS", "arithmetic_only": True,
            "premise": "Completed original G projection theorem; all geometry is proved in its hand manuscript.",
            "comparisons": {key: str(value) for key, value in out.items()}}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    report = checks()
    if args.report:
        args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
