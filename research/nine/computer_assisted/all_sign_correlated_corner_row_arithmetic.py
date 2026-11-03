#!/usr/bin/env python3
"""Exact rational criterion for the correlated-corner seven-original row.

The continuous implication is proved in the adjacent hand manuscript.
Import criterion(Fraction(b), Fraction(U), Fraction(L)) to evaluate an
adaptive guard. This evaluates rational conditions, not a packing search.
"""

from fractions import Fraction as F
import argparse
import json


Q, a, B, k, T, rho = F(1105, 256), F(46), F(27, 2), F(207, 16), F(211, 4), F(91, 60)
P, C, J = (a+k)/2, (a-k)/2, B+k/2


def criterion(b, U, L):
    """Evaluate every hand-criterion gate exactly; inputs must be rational."""
    b, U, L = F(b), F(U), F(L)
    z = 1-b*b
    if z == 0 or 2-b*b == 0:
        return {"status": "FAIL", "reason": "Undefined rational denominator"}
    delta = b/(2-b*b)
    c = (1-b-3*b*b-4*b*b*b)/2
    X0 = 3-b*U/z
    C0 = (T-a*(X0-rho-(1+b)/2))/B
    lam = k*L/z
    eplus, eminus = B-k/2-J*delta, k/2-J*delta
    p, q = C+P*delta-k*c, eminus+C-P*delta-lam
    A = a*c-a*U/(2*z**3)-a*b*(b+F(1, 2))/z
    K = a*a/(23*z*z)-a
    epsilon = min(A, q)-p-K*b
    values = {
        "b": b, "U": U, "L": L, "z": z, "delta": delta, "c": c,
        "X0": X0, "C0": C0, "lambda": lam, "eplus": eplus,
        "eminus": eminus, "p": p, "q": q, "A": A, "K": K,
        "epsilon": epsilon,
    }
    reserves = {
        "b_positive": b,
        "b_below_one_half": F(1, 2)-b,
        "U_positive": U,
        "L_positive": L,
        "main_steep_separator_rejection": 1-2*b*rho-U,
        "endpoint_shallow_separator_rejection": 1-L-2*b*rho,
        "endpoint_pair_horizontal_upper_band": L-(rho-F(3, 2)+C0),
        "endpoint_pair_horizontal_order": (X0-rho)-(C0+(1+b)/2),
        "main_support_shallow_sign": a*z-k*b,
        "main_support_steep_sign": k*z-a*b,
        "shoulder_support_shallow_sign": B*z-k*b,
        "shoulder_support_steep_sign": k*z-B*b,
        "scalar_kc_above_eminus": k*c-eminus,
        "scalar_eplus_above_kc": eplus-k*c,
        "scalar_negative_exterior_cost": k*c+eminus-lam,
        "p_positive": p,
        "q_above_p": q-p,
        "A_above_p": A-p,
        "K_nonnegative": K,
        "final_epsilon_positive": epsilon,
        # Consequences used explicitly in the printed continuous proof.
        "z_above_one_half": z-F(1, 2),
        "alpha_difference_bound": 2*b-b/z,
        "pair_frame_dot_lower_bound": 1-2*b*b*(1+4*b*b),
        "pair_signed_variation_positive": c,
        "main_reversed_shallow_normal_rejection": 1-b*U,
        "endpoint_downward_normal_rejection": 1-b*L,
        "scalar_positive_exterior_cost": k*c+eplus,
        "F_alignment_equality_cost": B*(1-delta),
    }
    checks = []
    for name, value in reserves.items():
        nonstrict = name == "K_nonnegative"
        passes = value >= 0 if nonstrict else value > 0
        checks.append({"name": name, "relation": ">=0" if nonstrict else ">0",
                       "value": str(value), "pass": passes})
    identities = {
        "center_radius_squared_reserve": (rho*rho+rho+F(1, 2)-Q, F(31, 57600)),
        "pair_determinant_coefficient": (z-2*b*b, 1-3*b*b),
        "pair_support_variation_coefficient": (((1-3*b*b)-b*(1+4*b*b))/2, c),
        "main_vector_squared_norm": (a*a+k*k, 23*23*Q),
        "shoulder_vector_squared_norm": (B*B+k*k, 9*9*Q),
        "main_target_corner_x": (a/23, 2),
        "main_target_corner_y_magnitude": (k/23, F(9, 16)),
        "main_A_support_alpha": ((a+k)/2, P),
        "main_A_support_beta": ((k-a)/2, -C),
        "main_D_support_alpha": ((a+k)/2, P),
        "main_D_support_beta": ((a-k)/2, C),
        "E_aggregate_alpha_with_short_chain": ((B+k)/2+B/2, J),
        "E_positive_beta_before_alpha_loss": ((B-k)/2+B/2, B-k/2),
        "E_negative_beta_before_alpha_loss": (-(B-k)/2+B/2, k/2),
        "G_reflected_positive_beta_before_alpha_loss": (-(k-B)/2+B/2, B-k/2),
        "G_reflected_negative_beta_before_alpha_loss": ((k-B)/2+B/2, k/2),
        "total_support_constant": (3*a+2*B+2*k+a+B+2*k, 64*Q),
        "positive_x_scalar_minimum": (k*c-C-P*delta, -p),
        "negative_x_scalar_minimum": (eminus-lam+C-P*delta, q),
        "corner_square_completion_coefficient": (a*a/(4*F(23, 4)), a*a/23),
        "quadratic_common_slope_loss": (a*a/(23*z*z)-a, K),
        "final_nonnegative_excess_coefficient": (min(A, q)-p-K*b, epsilon),
    }
    for name, (actual, expected) in identities.items():
        checks.append({"name": name, "relation": "=", "value": str(actual),
                       "expected": str(expected), "pass": actual == expected})
    return {
        "status": "PASS" if all(check["pass"] for check in checks) else "FAIL",
        "scope": "Rational guards for a continuous hand theorem; no interval-box or whole-mask closure.",
        "parameters": {name: str(value) for name, value in values.items()},
        "check_count": len(checks),
        "checks": checks,
    }


def standard_report():
    first = criterion(F(1, 30), F(11, 30), F(7, 10))
    second = criterion(F(1, 50), F(9, 20), F(7, 10))
    quoted = {
        "first_p": (F(first["parameters"]["p"]), F(931916369, 86352000)),
        "first_q": (F(first["parameters"]["q"]), F(12115211, 924172)),
        "first_A": (F(first["parameters"]["A"]), F(126268435381231, 9808731436500)),
        "first_K": (F(first["parameters"]["K"]), F(37342754, 808201)),
        "first_epsilon": (F(first["parameters"]["epsilon"]), F(305395948055079229, 564669051336432000)),
        "second_epsilon": (F(second["parameters"]["epsilon"]), F(13240758374442033713, 52010454158334000000)),
    }
    quote_checks = []
    for name, (actual, expected) in quoted.items():
        quote_checks.append({"name": name, "relation": "=", "value": str(actual),
                             "expected": str(expected), "pass": actual == expected})
    for name, case in [("first", first), ("second", second)]:
        diff = F(case["parameters"]["q"])-F(case["parameters"]["A"])
        quote_checks.append({"name": name+"_q_above_A", "relation": ">0",
                             "value": str(diff), "pass": diff > 0})
    return {
        "status": "PASS" if first["status"] == second["status"] == "PASS"
                  and all(check["pass"] for check in quote_checks) else "FAIL",
        "scope": "Two all-sign seven-original row terminals and their rational criterion only.",
        "check_count": first["check_count"]+second["check_count"]+len(quote_checks),
        "specializations": {"U_11_30_beta_1_30": first, "U_9_20_beta_1_50": second},
        "printed_constant_checks": quote_checks,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--b", type=F, help="Absolute signed beta bound, e.g. 1/30")
    parser.add_argument("--variation", type=F, help="Total vertical variation bound, e.g. 11/30")
    parser.add_argument("--pair-band", type=F, default=F(7, 10))
    args = parser.parse_args()
    if (args.b is None) != (args.variation is None):
        parser.error("--b and --variation must be supplied together")
    result = standard_report() if args.b is None else criterion(args.b, args.variation, args.pair_band)
    print(json.dumps(result, indent=2, sort_keys=True))
    raise SystemExit(0 if result["status"] == "PASS" else 1)
