#!/usr/bin/env python3
"""Retain seven uniform parts of the already verified printed cost reserves."""
from fractions import Fraction as F
from hashlib import sha256
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = Path(__file__).resolve().parents[2]


def source(name):
    local = HERE/name
    return local if local.is_file() else ROOT/"candidate_hand/root_coarse_mismatch"/name


data_name = "CANDIDATE_COARSE_MISMATCH_HAND_DATA.json"
report_name = "CANDIDATE_COARSE_MISMATCH_HAND_COMPACT_REPORT.json"
paths = {name: source(name) for name in (data_name, report_name)}
expected_sha = {
    data_name: "ffa48df0d02e18880314907a72a70fcc6aaceea4ee1060ea76b4fdb04c23a5fa",
    report_name: "995c1c652957c00ac0aa40e0a3dede26db689e15e281e78dac2b5ae8091f963f",
}
assert all(sha256(paths[n].read_bytes()).hexdigest() == h for n, h in expected_sha.items())
d = json.loads(paths[data_name].read_text())
c = json.loads(paths[report_name].read_text())
assert c["status"] == c["cover"]["status"] == "PASS"
assert not c["failures"] and not c["cover"]["errors"]
assert c["rows"] == c["passed"] == len(d["rows"]) == len(c["row_records"]) == 129031
gamma, beta = F(89727, 100000), F(99, 5000)
assert list(map(F, d["gamma"])) == [gamma]*7
assert list(map(F, d["beta"])) == [beta, F(0), beta, beta, beta, beta, F(0)]
minima = [None]*7
for row, (_, costs) in zip(d["rows"], c["row_records"]):
    edge = row["edge"]
    assert edge in range(7) and costs
    assert F(row.get("gamma", d["gamma"][edge])) >= gamma
    value = min(F(bound) for _, bound in costs)
    minima[edge] = value if minima[edge] is None else min(minima[edge], value)
numerators = [1539796384, 1387463060, 1885909004, 1251076023,
              1539189132, 2347069107, 642432521]
assert minima == [F(n, 10**14) for n in numerators]
increases = [F(n, 10**6) for n in (15, 13, 18, 12, 15, 23, 6)]
assert all(m > a > 0 for m, a in zip(minima, increases))
total = sum(increases, F(0))
assert total == F(51, 500000)
t = F(13, 50)
p = t/2-t**2/4-t**3/12+t**4/48+t**5/240-t**6/1440-t**7/10080
reserve = 7*gamma+total+beta*p-F(710, 113)
assert reserve == F(9154605884982919, 494375000000000000000) > 0
assert all(sha256(paths[n].read_bytes()).hexdigest() == h for n, h in expected_sha.items())
result = {"status": "PASS_PRINTED_RESERVE_HAND_COROLLARY", "conclusion": "S<13/50",
          "scope": "Same complete coarse pair table and original G/T/E scope; no additional pair row or geometric premise.",
          "rows_recounted": len(d["rows"]), "gamma": str(gamma), "beta": str(beta),
          "edge_minimum_cost_reserves": list(map(str, minima)),
          "retained_edge_increases": list(map(str, increases)),
          "retained_cyclic_increase": str(total),
          "reserve_above_710_over_113": str(reserve), "sha256": expected_sha,
          "unchanged_inputs": True}
HERE.joinpath("coarse_mismatch_printed_reserves_arithmetic.json").write_text(
    json.dumps(result, indent=2)+"\n")
print(json.dumps(result, indent=2))
