#!/usr/bin/env python3
"""Reconstruct the whole-domain HA-pressure polynomial identity exactly.

This uses Fraction arithmetic only. It neither samples a parameter domain nor
runs Lean or CI. With --write, save every exact polynomial and all 288
Bernstein coefficients. Without --write, independently reconstruct and compare
the saved artifact, including every coefficient and every stated row bound.
"""
from collections import defaultdict
from fractions import Fraction
from math import comb
from pathlib import Path
import argparse
import json

F = Fraction


class Poly:
    """Sparse rational polynomial in (k,w,U)."""

    def __init__(self, value=0):
        if isinstance(value, Poly):
            self.terms = value.terms.copy()
        elif isinstance(value, dict):
            self.terms = {key: F(v) for key, v in value.items() if v}
        else:
            self.terms = {(0, 0, 0): F(value)} if value else {}

    def __add__(self, other):
        result = defaultdict(F, self.terms)
        for key, value in Poly(other).terms.items():
            result[key] += value
        return Poly(result)

    __radd__ = __add__

    def __neg__(self):
        return Poly({key: -value for key, value in self.terms.items()})

    def __sub__(self, other):
        return self + (-Poly(other))

    def __rsub__(self, other):
        return Poly(other) + (-self)

    def __mul__(self, other):
        result = defaultdict(F)
        for p, a in self.terms.items():
            for q, b in Poly(other).terms.items():
                result[tuple(p[i] + q[i] for i in range(3))] += a * b
        return Poly(result)

    __rmul__ = __mul__

    def __pow__(self, exponent):
        result = Poly(1)
        for _ in range(exponent):
            result *= self
        return result

    def __truediv__(self, scalar):
        return self * (F(1) / F(scalar))

    def degree(self):
        return tuple(
            max((key[i] for key in self.terms), default=0) for i in range(3)
        )

    def same(self, other):
        return self.terms == Poly(other).terms

    def affine_rectangle(self):
        """Substitute k=x/11, w=(5+19y)/6; no U is permitted."""
        result = defaultdict(F)
        for (i, j, ell), coefficient in self.terms.items():
            assert ell == 0
            for b in range(j + 1):
                result[i, b, 0] += (
                    coefficient
                    * F(1, 11) ** i
                    * comb(j, b)
                    * F(5, 6) ** (j - b)
                    * F(19, 6) ** b
                )
        return Poly(result)

    def bernstein(self, n=15, m=8):
        assert self.degree()[0] <= n and self.degree()[1] <= m
        assert self.degree()[2] == 0
        result = {}
        for i in range(n + 1):
            for j in range(m + 1):
                result[i, j] = sum(
                    coefficient
                    * F(comb(i, a), comb(n, a))
                    * F(comb(j, b), comb(m, b))
                    for (a, b, ell), coefficient in self.terms.items()
                    if a <= i and b <= j
                )
        return result

    def records(self):
        return [
            [*key, str(coefficient)]
            for key, coefficient in sorted(self.terms.items())
        ]


def reconstruct():
    k = Poly({(1, 0, 0): 1})
    w = Poly({(0, 1, 0): 1})
    U = Poly({(0, 0, 1): 1})
    D = 1 + k * k
    rp, rm = 1 + k, 1 - k
    g = F(1, 2) + F(2, 5) * w
    a = w + 1 - k * (w - 1)
    b = w - 1 + k * (w + 1)
    abar, bbar, h = U * a / 2, U * b / 2, k * U

    # K=Knum/rp. Clear this sole denominator before reducing U.
    Knum = U * (1 - k * w) * rp - rm
    C0 = 2 * (abar - g) + h * bbar**2 * (2 - g * h)
    C1num = 2 * Knum * (abar - g) - 2 * rp * bbar * (1 - g * h)
    cleared = C0**2 * (rp**2 + Knum**2) - C1num**2
    assert cleared.degree()[2] <= 10

    # Generic reduction U^(2j)=2^j/D^j, followed by multiplication by D^5.
    # This directly derives D^5*rp^2*P=A+U*B from the original C0,C1.
    A, B = Poly(), Poly()
    powers_D = [D**i for i in range(6)]
    for (i, j, ell), coefficient in cleared.terms.items():
        power = ell // 2
        term = (
            Poly({(i, j, 0): coefficient * 2**power})
            * powers_D[5 - power]
        )
        if ell % 2:
            B += term
        else:
            A += term

    # Separately verify the factored formulas printed in the manuscript.
    H = (1 - k * w) * rp
    p = a * D + k * b**2
    q = g * (2 * D**2 + k**2 * b**2)
    t = 2 * rp * ((1 - k * w) * a + g * k * b) + 2 * g * rm * D
    s = rm * a + rp * (2 * g * (1 - k * w) + b)
    A_factored = (
        4 * D * p**2 * H**2
        + 2 * D**2 * p**2 * (rp**2 + rm**2)
        + 8 * D * p * q * H * rm
        + 2 * q**2 * H**2
        - 2 * D**4 * s**2
        + D * q**2 * (rp**2 + rm**2)
        - D**3 * t**2
    )
    B_factored = (
        -4 * D * p * q * H**2
        - 4 * D**2 * p**2 * H * rm
        - 2 * D**2 * p * q * (rp**2 + rm**2)
        - 2 * D * q**2 * H * rm
        + 2 * D**4 * t * s
    )
    assert A.same(A_factored)
    assert B.same(B_factored)
    assert A.degree() == (12, 8, 0)
    assert B.degree() == (13, 7, 0)

    UL = F(7071, 5000) * (1 - k * k / 2)
    lower = [
        F(31, 50), F(17, 10), F(12, 5), F(14, 5), F(27, 10),
        F(12, 5), F(2), F(13, 10), F(1, 4),
    ]
    endpoint_records = []
    for epsilon in [F(0), F(1, 10000)]:
        polynomial = A + (UL + epsilon) * B
        assert polynomial.degree() == (15, 8, 0)
        transformed = polynomial.affine_rectangle()
        coefficients = transformed.bernstein()
        minima = []
        for j in range(9):
            index = min(range(16), key=lambda i: coefficients[i, j])
            value = coefficients[index, j]
            assert all(coefficients[i, j] > lower[j] for i in range(16))
            minima.append({
                "j": j, "minimizing_i": index, "minimum": str(value),
                "strict_lower_bound": str(lower[j]),
            })
        assert min(coefficients.values()) > F(1, 4)
        endpoint_records.append({
            "epsilon": str(epsilon),
            "polynomial_coefficients_k_w_U": polynomial.records(),
            "transformed_coefficients_x_y_U": transformed.records(),
            "bernstein_bidegree": [15, 8],
            "bernstein_coefficients": [
                [i, j, str(coefficients[i, j])]
                for i in range(16) for j in range(9)
            ],
            "row_minima": minima,
        })

    # Exact independent endpoint/reserve checks used by the analytic argument.
    assert F(16) * F(6241, 1600) - 17 * (F(9, 4) + F(99, 70)) == F(41, 350)
    assert F(6241, 1600) - F(1700, 441) == F(32281, 705600)
    assert F(7071, 5000)**2 < 2 < F(70711, 50000)**2
    assert F(1, 50000) + F(9, 16 * 11**4) < F(1, 10000)
    return {
        "schema": "exact_tensor_bernstein_certificate_v1",
        "manuscript": "NEGATIVE_H_OWNED_LEFT_DIAMOND_HA_PRESSURE.md",
        "coefficient_arithmetic": "exact rational",
        "parameter_rectangle": {"k": ["0", "1/11"], "w": ["5/6", "4"]},
        "affine_substitution": {"k": "x/11", "w": "(5+19*y)/6"},
        "radical": {
            "identity": "U^2*(1+k^2)=2",
            "lower_polynomial": "(7071/5000)*(1-k^2/2)",
            "error_interval": ["0", "1/10000"],
        },
        "factored_definitions": {
            "D": "1+k^2", "rp": "1+k", "rm": "1-k",
            "g": "1/2+(2/5)*w",
            "a": "w+1-k*(w-1)", "b": "w-1+k*(w+1)",
            "abar": "U*a/2", "bbar": "U*b/2", "h": "k*U",
            "K": "U*(1-k*w)-rm/rp",
            "C0": "2*(abar-g)+h*bbar^2*(2-g*h)",
            "C1": "2*K*(abar-g)-2*bbar*(1-g*h)",
            "P": "C0^2*(1+K^2)-C1^2",
            "identity": "D^5*rp^2*P=A+U*B",
            "H": "(1-k*w)*rp",
            "p": "a*D+k*b^2",
            "q": "g*(2*D^2+k^2*b^2)",
            "t": "2*rp*((1-k*w)*a+g*k*b)+2*g*rm*D",
            "s": "rm*a+rp*(2*g*(1-k*w)+b)",
            "A": (
                "4*D*p^2*H^2+2*D^2*p^2*(rp^2+rm^2)+8*D*p*q*H*rm"
                "+2*q^2*H^2-2*D^4*s^2+D*q^2*(rp^2+rm^2)-D^3*t^2"
            ),
            "B": (
                "-4*D*p*q*H^2-4*D^2*p^2*H*rm"
                "-2*D^2*p*q*(rp^2+rm^2)-2*D*q^2*H*rm+2*D^4*t*s"
            ),
        },
        "A_coefficients_k_w_U": A.records(),
        "B_coefficients_k_w_U": B.records(),
        "endpoints": endpoint_records,
        "global_strict_Bernstein_lower_bound": "1/4",
        "exact_radius_reserve": "32281/705600",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    artifact = Path(__file__).with_name("NEGATIVE_H_OWNED_LEFT_DIAMOND_HA_PRESSURE_COEFFICIENTS.json")
    data = reconstruct()
    if args.write:
        artifact.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    else:
        saved = json.loads(artifact.read_text(encoding="utf-8"))
        assert saved == data, "Saved artifact differs from exact reconstruction"
    print("Exact identity and all 288 Bernstein coefficients verified.")
    print("Both endpoint polynomials have every coefficient strictly above 1/4.")
    print("Radius reserve: q0 - 1700/441 = 32281/705600 > 0.")


if __name__ == "__main__":
    main()

