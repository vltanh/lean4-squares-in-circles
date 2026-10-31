"""Rational identity audit for the analytic corner and middle measure proof.

See NINE_RADIUS_TWO_MEASURE_RECTANGLES_ANALYTIC_REDUCTION.md.
This is a convenience reconstruction of the explicitly displayed Taylor
and mass reserves. It is not a box or inverse-trigonometric certificate.
All arithmetic uses fractions from the Python standard library.
"""
from fractions import Fraction as F
import json


def verify():
    lower = [
        (F(9, 10), F(223, 200), F(64180522657, 38400000000000)),
        (F(9, 11), F(191, 200), F(729120878539, 422400000000000)),
        (F(10, 11), F(227, 200), F(880201511023, 422400000000000)),
        (F(21, 22), F(63, 50), F(203016009, 137500000000)),
        (F(2, 3), F(18, 25), F(1063804, 146484375)),
        (F(7, 9), F(89, 100), F(2229221653, 3600000000000)),
        (F(20, 27), F(83, 100), F(29765234213, 10800000000000)),
        (F(22, 27), F(19, 20), F(4363109, 3456000000)),
        (F(8, 9), F(109, 100), F(6858681353, 3600000000000)),
    ]
    upper = [
        (F(1, 10), F(1, 9), F(119, 10935)),
        (F(7, 20), F(9, 25), F(139, 62500)),
        (F(1, 5), F(21, 100), F(16913, 2000000)),
        (F(2, 11), F(19, 100), F(464551, 66000000)),
        (F(7, 22), F(13, 40), F(4633, 4224000)),
    ]
    for z, t, reserve in lower:
        assert 0 < t <= F(63, 50) < F(3, 2)
        assert z - (t - t**3 / 6 + t**5 / 120) == reserve > 0
    for z, t, reserve in upper:
        assert 0 < t <= F(63, 50)
        assert t - t**3 / 6 - z == reserve > 0

    w0, w1, w2, w3 = (F(n, 1000) for n in (714, 3858, 2424, 1709))
    corner = [
        F(292, 1000) + w0 / 4 - (w1 + w2) / 4
        + (w1 * F(223, 200) + w2 * F(191, 200)) * F(7, 22),
        (w1 - w2) / 4 - w1 / 27 + w2 * F(11, 10) * F(7, 22),
        w0 / 6 - w2 / 4
        + (w1 * F(223, 200) + w2 * F(418, 200)) * F(7, 44),
        -(w2 + w3) / 4
        + (w1 * (F(223, 200) + F(1, 10))
           + w2 * (F(191, 200) + F(63, 50))
           + w3 * (F(18, 25) + F(89, 100))) * F(7, 44),
    ]
    numer1 = -w1 * F(57, 100) + w2 * F(189, 200) + w3 * F(89, 50)
    numer2 = -w1 * F(18, 25) - w2 * F(13, 20) + w3 * F(109, 50)
    assert numer1 == F(78341, 25000) > 0
    assert numer2 == -F(31387, 50000) < 0
    middle = [
        (w1 - w3) / 4 + numer1 * F(7, 44),
        (w1 + w2 - w3) / 4 + numer2 / 6,
    ]
    reserves = [x - 1 for x in corner + middle]
    assert reserves == [
        F(11613, 2200000), F(5761, 90000), F(14681, 4400000),
        F(2423, 550000), F(19681, 550000), F(2897, 75000),
    ]
    assert all(x > 0 for x in reserves)
    # Face-order and fixed endpoint comparisons from Sections 2--3.
    assert 1 - 2 * F(1, 10)**2 == F(49, 50) > F(9, 10)
    assert F(121, 100) - F(21, 20)**2 > F(1, 100)
    assert F(729, 400) - F(21, 20)**2 > F(1, 100)
    assert 400 + 49 < 484
    assert 400 + 49 < 729 and 484 + 16 < 729 < 400 + 484
    assert F(8, 9)**2 + F(7, 27)**2 == F(625, 729) < 1
    assert 2 * F(8, 9)**2 > 1
    result = {
        "lower_sine_identities": len(lower),
        "upper_sine_identities": len(upper),
        "whole_region_mass_reserves": [[x.numerator, x.denominator] for x in reserves],
        "replaced_corner_charge_checks": 14,
        "replaced_middle_charge_checks": 2,
        "replaced_corner_empty_tests": 3,
        "new_interval_charge_checks": 0,
    }
    print(json.dumps(result, sort_keys=True), flush=True)
    return result


if __name__ == "__main__":
    verify()

