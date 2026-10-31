#!/usr/bin/env python3
"""Exact arithmetic supplement for the parallel-HK side-return manuscript.

Requires SymPy. No floating-point input, pose search, Lean compilation, or CI.
This checks polynomial identities and coefficient conversions, not the geometry.
It is not an independent review of the manuscript.
"""
from __future__ import annotations

import argparse
import itertools
import json
from fractions import Fraction
from math import comb
from pathlib import Path
import sympy as sp

PARENT = "f99f0cc7e93e3d0c2d78dbffaf0198d1996cd1ca"


def bernstein(poly, variables, intervals):
    xs = sp.symbols("x0:" + str(len(variables)))
    normalized = sp.Poly(sp.expand(poly.subs(
        {v: a + (b-a)*x for v, x, (a, b) in
         zip(variables, xs, intervals)}, simultaneous=True)), *xs)
    degrees = normalized.degree_list()
    power = {ex: Fraction(co) for ex, co in normalized.terms()}
    result = {}
    for index in itertools.product(*(range(n+1) for n in degrees)):
        value = Fraction(0)
        for ex, coefficient in power.items():
            if all(r <= i for r, i in zip(ex, index)):
                factor = Fraction(1)
                for r, i, n in zip(ex, index, degrees):
                    factor *= Fraction(comb(i, r), comb(n, r))
                value += coefficient * factor
        result[index] = value

    # Reverse reconstruction independently checks the conversion identity.
    reconstruction = 0
    for index, value in result.items():
        term = sp.Rational(value.numerator, value.denominator)
        for i, n, x in zip(index, degrees, xs):
            term *= comb(n, i) * x**i * (1-x)**(n-i)
        reconstruction += term
    if sp.Poly(sp.expand(reconstruction-normalized.as_expr()), *xs) != 0:
        raise AssertionError("Inverse Bernstein identity failed")
    return degrees, result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-certificate", type=Path,
                        help="Optional JSON output of every exact coefficient.")
    args = parser.parse_args()

    F, m, tau, w, z = sp.symbols("F m tau w z")
    c = (1-m*m)/(1+m*m)
    s = 2*m/(1+m*m)
    L = F-tau
    h = (2*L*(s-tau)-tau*tau)/(2*(1+c))
    t = ((s-c)*L+s*s-s*h)/(c*(L+s))
    t0 = sp.factor(t.subs(tau, 0))

    expected_dt = (
        m*(1+m*m)**2*((1+m*m)*(F*F+L*L)+4*m*L+4)
        / (2*(1-m*m)*(L*(1+m*m)+2*m)**2)
    )
    assert sp.cancel(sp.diff(t, tau)-expected_dt) == 0
    assert sp.cancel(h-(L*m-(1+m*m)*(2*L*tau+tau*tau)/4)) == 0
    expected_delta0 = (
        2*m*(F*(1-m)*(1+m*m)-2*m*m)
        / ((1-m*m)*(F*(1+m*m)+2*m))
    )
    assert sp.cancel(1-c-s*t0-expected_delta0) == 0
    assert sp.cancel(
        sp.diff(t0, F)
        + 2*m*(1+m*m)**2/((1-m*m)*(F*(1+m*m)+2*m)**2)
    ) == 0
    assert t0.subs({F: sp.Rational(4, 3), m: sp.Rational(1, 3)}) == -sp.Rational(13, 116)

    R0 = sp.Rational(79, 40)
    Fb = 2*R0*w/(1+w*w)
    Wb = R0*(1-w*w)/(1+w*w)
    hb = Wb-1
    mb = hb/Fb
    tb = sp.factor(t0.subs({F: Fb, m: mb}))
    kb = 1-tb
    aa = 119*w*w-158*w-39
    bb = 119*w*w+158*w-39
    expected_tb = (
        200533921*w**4+174520164*w**3+43077762*w*w
        -57195684*w+2313441
    )/(4641*aa*bb)
    assert sp.cancel(tb-expected_tb) == 0
    assert sp.cancel(Fb*Fb+Wb*Wb-R0*R0) == 0

    Pb = hb*z**4+kb*(1-hb)*z**3+(Fb-1+hb+2-kb*kb)*z*z-kb*(hb+1)*z+Fb-1
    z0 = sp.Rational(3, 8)
    a0 = Pb.subs(z, z0)
    a1 = sp.diff(Pb, z).subs(z, z0)
    a2 = Fb-1+hb+2-kb*kb
    disc = 4*a2*a0-a1*a1

    # The exact Taylor remainder has nonnegative extra cubic/quartic terms.
    remainder = (z-z0)**2 * (
        hb*(z*z+2*z*z0+3*z0*z0)+kb*(1-hb)*(z+2*z0)
    )
    assert sp.cancel(Pb-a0-a1*(z-z0)-a2*(z-z0)**2-remainder) == 0

    I = [(sp.Rational(29, 100), sp.Rational(7, 18))]
    J = [(sp.Rational(29, 100), sp.Rational(9, 25))]
    Dm = (1-m*m)**2*(F*(1+m*m)+2*m)**2
    specifications = [
        ("T0_derivative_minus_two", sp.diff(t0, m)-2, Dm, (F, m),
         [(sp.Rational(1), sp.Rational(4, 3)),
          (sp.Rational(1, 3), sp.Rational(61, 100))], 1,
         [1,1,1,1,2,2,3,4,5, 1,1,1,1,2,2,3,4,5, 1,1,1,1,2,2,3,4,6]),
        ("boundary_turn_lower", tb+sp.Rational(1, 8), -37128*aa*bb,
         (w,), I, 10**6, [45,41,33,21,3]),
        ("boundary_turn_upper", 1-tb, -4641*aa*bb,
         (w,), I, 10**5, [8,37,73,116,169]),
        ("boundary_tangent_discriminant", disc,
         -873480818707660800*(1+w*w)**2*aa**3*bb**3,
         (w,), I, 10**26, [2,6,10,14,20,26,32,38,45,51,55,59,59,56,47,31,5]),
        ("low_F_boundary_turn", tb, -4641*aa*bb,
         (w,), J, 10**6, [4,4,3,2,1]),
        ("opposite_corner_gap",
         sp.Rational(24,5)*(Fb-1)+2*hb*tb-(1-tb)**2,
         2153888100*(1+w*w)*aa**2*bb**2,
         (w,), J, 10**15, [5,5,6,6,7,7,8,8,8,9,9]),
    ]

    report = {"source_parent": PARENT,
              "arithmetic": "Exact rational; no floating-point proof input",
              "independent_review": "Not performed in this continuation",
              "packets": []}
    total = 0
    for name, expression, denominator, variables, intervals, scale, floors in specifications:
        polynomial = sp.Poly(sp.cancel(expression*denominator), *variables)
        assert sp.cancel(polynomial.as_expr()/denominator-expression) == 0
        degrees, coefficients = bernstein(polynomial.as_expr(), variables, intervals)
        assert all(value > 0 for value in coefficients.values())
        assert [int(value//scale) for value in coefficients.values()] == floors
        total += len(coefficients)
        report["packets"].append({
            "name": name, "variables": [str(v) for v in variables],
            "degrees": list(degrees),
            "intervals": [[str(a), str(b)] for a, b in intervals],
            "power_coefficients": [
                {"exponents": list(ex), "value": str(value)}
                for ex, value in polynomial.terms()],
            "bernstein_coefficients": [
                {"index": list(index), "value": str(value)}
                for index, value in coefficients.items()],
            "normalizing_scale": str(scale),
            "positive_integer_floors": floors,
            "minimum": str(min(coefficients.values())),
        })
        print(f"{name}: {len(coefficients)} positive coefficients; inverse identity PASS")
    assert total == 70

    # Exact endpoint and arithmetic reserves used by the manuscript.
    assert sp.Rational(6241,1600) - (sp.Rational(43,40)**2 +
           (1+sp.Rational(61,100)*sp.Rational(43,40))**2) == sp.Rational(55871,16000000)
    assert sp.Rational(6241,1600) - (sp.Rational(4,3)**2 +
           (1+sp.Rational(4,9))**2) == sp.Rational(4721,129600)
    assert sp.Rational(43,40)-Fb.subs(w,sp.Rational(29,100)) == sp.Rational(7963,433640)
    assert Fb.subs(w,sp.Rational(7,18))-sp.Rational(4,3) == sp.Rational(11,11190)
    assert Fb.subs(w,sp.Rational(9,25))-sp.Rational(5,4) == sp.Rational(25,2824)
    print("PASS: 70 exact coefficients, all identities, all displayed floors and reserves.")
    print("Geometry and independent manuscript review are NOT certified by this script.")
    if args.write_certificate:
        args.write_certificate.parent.mkdir(parents=True, exist_ok=True)
        args.write_certificate.write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")


if __name__ == "__main__":
    main()
