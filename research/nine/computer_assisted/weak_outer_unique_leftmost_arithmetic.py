"""Exact scalar checks for the unique-leftmost-original hand theorem."""
from fractions import Fraction as F
import json

rho = F(91,60)
assert rho-F(91,64) == F(91,960)
assert F(8,15)+F(17,40) == F(23,24)
radical_reserve = F(8,15)**2-(rho**2-F(91,64)**2)
distance_reserve = 1-F(91,960)**2-F(23,24)**2
assert radical_reserve == F(1811,307200) > 0
assert distance_reserve == F(66919,921600) > 0
print(json.dumps({
    "status":"PASS",
    "scope":"Exact scalar identities and strict comparisons; continuous proof is in the hand document",
    "radical_squared_reserve":str(radical_reserve),
    "unit_center_distance_reserve":str(distance_reserve)
},indent=2))
