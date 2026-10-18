#!/usr/bin/env python3
"""Exact finite interfaces in UNRESTRICTED_EIGHT_SQUARE_HAND_PROOF.md.

These fixed comparisons check the main manuscript's arithmetic and finite
word steps. They neither establish a missing whole-pair theorem nor infer
global closure from the scalar reserve of a proposed table. Every analytic
pair theorem and closed domain cover remains an explicit proof dependency.
"""
from fractions import Fraction as F
from itertools import product
import json


comparisons = []


def positive(name, value):
    value = F(value)
    assert value > 0, (name, value)
    comparisons.append({"name": name, "positive_reserve": str(value)})


def equal(name, value, expected):
    value, expected = F(value), F(expected)
    assert value == expected, (name, value, expected)
    comparisons.append({"name": name, "exact_value": str(value)})


def T(x, n):
    return sum((F((-1) ** j, 2 * j + 1) * x ** (2 * j + 1)
                for j in range(n)), F(0))


def sine_lower(x):
    return x - x ** 3 / 6 + x ** 5 / 120 - x ** 7 / 5040


def cosine_lower(x):
    return (1 - x ** 2 / 2 + x ** 4 / 24 - x ** 6 / 720
            + x ** 8 / 40320 - x ** 10 / 3628800)


machin_upper = 32 * T(F(1, 5), 7) - 8 * T(F(1, 239), 4)
positive("Machin upper below the eight-decimal bound", F("6.28318531") - machin_upper)
positive("eight-decimal bound below 710/113", F(710, 113) - F("6.28318531"))
qminus, Q1, Q0 = F(7831, 2000), F(1957767069, 500000000), F(9789, 2500)
positive("qminus above 5/2", qminus - F(5, 2))
positive("Q1 above qminus", Q1 - qminus)
positive("Q0 above Q1", Q0 - Q1)
positive("Q0 below four", 4 - Q0)
positive("central-depth radius buffer", F(98, 25) - Q0 - F(4, 1000) - F(1, 10**6))
positive("central first angular contradiction", F(1259, 200) - F(44, 7))
positive("central second angular contradiction", F(7859, 1250) - F(44, 7))
positive("initial gap cosine comparison", F(41, 50) - F(17443, 21300))
positive("initial maximum radius comparison", F(71, 50)**2 + F(71, 50) + F(1, 2) - Q0)

G = [[9200, 9100, 9005, 8833], [9100, 9100, 9005, 8833],
     [9005, 9005, 8912, 8926], [8833, 8833, 8926, 9099]]
minimum = None
witness = None
for state_word in product(range(4), repeat=7):
    weight = sum(G[state_word[i]][state_word[(i+1) % 7]] for i in range(7))
    if minimum is None or weight < minimum:
        minimum, witness = weight, state_word
equal("four-type seven-walk floor", F(minimum, 10000), F(3881, 625))
frame_U = (F(710, 113) - F(3881, 625)) * F(50, 9)
equal("frame width-cost upper bound", frame_U, F(10394, 25425))
positive("frame U below sqrt2 minus one by squaring", 2 - (1 + frame_U)**2)
frame_taylor = F(2945220061, 7200000000)
positive("explicit Taylor lower bound at .7", sine_lower(F(7, 10)) + cosine_lower(F(7, 10)) - 1 - frame_taylor)
equal("frame concentration strict reserve", frame_taylor - frame_U, F(201866893, 813600000000))
positive("no three consecutive zero increments", F(57, 25) - F(7, 10) - F(11, 7))


def cycle_canonical(word):
    return min(word[i:] + word[:i] for i in range(7))


def dihedral_canonical(word):
    return min(cycle_canonical(word), cycle_canonical(tuple(reversed(word))))


quarter_words = set()
unquotiented = 0
for word in product(range(3), repeat=7):
    if sum(word) != 4 or word.count(2) > 1:
        continue
    if any(word[i] == word[(i+1) % 7] == word[(i+2) % 7] == 0 for i in range(7)):
        continue
    unquotiented += 1
    quarter_words.add(dihedral_canonical(word))
quarter_strings = sorted("".join(map(str, w)) for w in quarter_words)
assert quarter_strings == ["0010012", "0010102", "0010111", "0010201",
                           "0011002", "0011011", "0101011"]
equal("four jump-two words", 4*F(391, 400) + 2*F(157, 200) + F(163, 200), F(1259, 200))
equal("wrong 0010111 reserve", 6*F(17953, 20000) + F(359, 400) - F(710, 113), F(121, 565000))
equal("wrong 0011011 reserve", 7*F(17953, 20000) - F(710, 113), F(823, 2260000))
equal("G and upper-T and H cut reserve", F(62839, 10000)-F(710, 113), F(807, 1130000))
equal("lower-T cut reserve", F(3927, 625)-F(710, 113), F(1, 70625))

gamma, beta = F(89727, 100000), F(99, 5000)
equal("coarse .4 reserve", 7*gamma + beta*F(29, 100)*F(2, 5)-F(710, 113), F(271, 282500000))
increases = [15, 13, 18, 12, 15, 23, 6]
printed = [1539796384, 1387463060, 1885909004, 1251076023,
           1539189132, 2347069107, 642432521]
for edge, (kept, floor) in enumerate(zip(increases, printed)):
    positive(f"retained coarse edge {edge} reserve", F(floor, 10**14)-F(kept, 10**6))
equal("coarse increases sum", F(sum(increases), 10**6), F(51, 500000))
x = F(13, 50)
P = x/2-x**2/4-x**3/12+x**4/48+x**5/240-x**6/1440-x**7/10080
equal("coarse .26 contradiction", 7*gamma+F(51, 500000)+beta*P-F(710, 113),
      F(9154605884982919, 494375000000000000000))
equal("zero-quarter primary margin", F(".915")-F("1.05875")*F(".92")+F(".05875")*F(".4"), -F(711, 20000))
equal("zero-quarter first sign margin", F(".915")*F(".1")+F(".4")-F(".5"), -F(".0085"))
equal("zero-quarter second sign margin", F(".4")+F(".915")*F(".1")-F(".5")*(1-F(".1")**2/2), -F(".006"))

x = F(1, 10)
equal("M1 scalar contraction, conditional on its pair theorem", 7*F(".897582")+F(1,400)*(x/2-x**2/4-x**3/12)-F(710,113), F(18173,2712000000))
gammas_narrow = [F(".8975928")]*5+[F(".89759275"), F(".8975917")]
equal("narrow gamma sum", sum(gammas_narrow), F(125662969,20000000))
x = F(3, 200)
equal("narrow cubic Taylor value", x/2-x**2/4-x**3/12, F(238191,32000000))
equal("narrow contraction", sum(gammas_narrow)+F(1,200)*F(238191,32000000)-F("6.28318531"), F(2287,6400000000))
gammas_final = [F(".897595")]*6+[F(".8975925")]
equal("M2 gamma sum", sum(gammas_final), F(502653,80000))
x = F(1, 1000)
equal("M2 cubic Taylor value", x/2-x**2/4-x**3/12, F(5996999,12000000000))
equal("M2 scalar contraction, conditional on its pair theorem", sum(gammas_final)+F(1,20)*F(5996999,12000000000)-F("6.28318531"), F(522599,240000000000))
equal("terminal angular reserve", F(56793,5000000)-F(93,10)*F(1,1000), F(10293,5000000))
positive("central containment from core", qminus-F(121,72))

report = {
    "status": "PASS_FIXED_ARITHMETIC_AND_COMBINATORIAL_INTERFACES",
    "scope": "This report verifies only displayed scalar and finite word steps; all continuous pair theorems and complete domain covers are separate dependencies.",
    "rational_comparisons": comparisons,
    "four_type_walks": 4**7,
    "four_type_minimum": str(F(minimum,10000)),
    "four_type_minimizer_example": list(witness),
    "admissible_quarter_words_before_dihedral_quotient": unquotiented,
    "seven_quarter_words": quarter_strings,
}
print(json.dumps(report, indent=2, sort_keys=True))
