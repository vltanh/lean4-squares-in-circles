#!/usr/bin/env python3
"""Run the frozen kernel privately and independently match every compact row.

The full output is streamed to an exclusive temporary file, then the results
array is decoded one object at a time.  This avoids holding the multi-million
coefficient output twice in memory.  No root proof files are rewritten.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import json
from pathlib import Path
import re
import subprocess
import tempfile

ap = argparse.ArgumentParser()
ap.add_argument("data")
ap.add_argument("compact")
ap.add_argument("kernel")
ap.add_argument("--out", required=True)
args = ap.parse_args()
data, compact, kernel, out = map(lambda s: Path(s).resolve(),
                               (args.data, args.compact, args.kernel, args.out))


def digest(path):
    h = sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024*1024), b""):
            h.update(chunk)
    return h.hexdigest()


c = json.loads(compact.read_text())
before = {p: digest(p) for p in (data, compact, kernel)}
assert c["sha256"][data.name] == before[data]
assert c["sha256"][kernel.name] == before[kernel]
assert before[kernel] == "6af3d41fe7d404da7dd286c46644160f5444edd3028d864701266e9a4cd18697"
tmp = Path(tempfile.mkdtemp(prefix="m5_coarse_mismatch_independent_replay_"))
raw, err = tmp/"full.json", tmp/"stderr.txt"
with raw.open("xb") as stdout, err.open("xb") as stderr:
    run = subprocess.run(["node", str(kernel), str(data)],
                         stdout=stdout, stderr=stderr)
assert run.returncode == 0 and err.stat().st_size == 0
raw_sha = digest(raw)
assert raw_sha == c["sha256"]["CANDIDATE_COARSE_MISMATCH_HAND_ARITHMETIC.json"]
with raw.open() as stream:
    prefix = stream.read(4096)
assert re.search(r'^\{\s*"status":\s*"PASS"', prefix)


def result_objects(path):
    decoder = json.JSONDecoder()
    with path.open() as stream:
        for line in stream:
            if line.rstrip() == '  "results": [':
                break
        else:
            raise AssertionError("missing root results array")
        buf = ""
        while True:
            buf = buf.lstrip()
            if buf.startswith(","):
                buf = buf[1:].lstrip()
            if buf.startswith("]"):
                return
            try:
                item, end = decoder.raw_decode(buf)
            except json.JSONDecodeError:
                chunk = stream.read(65536)
                assert chunk, "incomplete result object"
                buf += chunk
                assert len(buf) < 2**22, "unexpected oversized result object"
                continue
            assert isinstance(item, dict)
            buf = buf[end:]
            yield item


rows = polynomials = coefficients = 0
least_cost = None
for index, item in enumerate(result_objects(raw)):
    assert item["index"] == index
    actual = []
    for field in ("premises", "cost"):
        records = []
        for poly in item[field]:
            degree = poly["degree"]
            values = list(map(F, poly["coefficient_lower"]))
            assert isinstance(degree, int) and degree >= 0
            assert len(values) == degree+1
            lower = min(values)
            assert lower >= 0 if field == "premises" else lower > 0
            records.append((degree, lower))
            polynomials += 1
            coefficients += degree+1
            if field == "cost":
                least_cost = lower if least_cost is None else min(least_cost, lower)
        if field == "cost":
            assert records
        actual.append(records)
    stored = c["row_records"][index]
    assert len(stored) == 2
    for rebuilt, recorded in zip(actual, stored):
        assert rebuilt == [(degree, F(value)) for degree, value in recorded]
    rows += 1
assert rows == c["rows"] == c["passed"] == len(c["row_records"])
assert polynomials == c["polynomials"] and coefficients == c["coefficients"]
assert all(digest(p) == value for p, value in before.items())
result = {"status": "PASS_INDEPENDENT_FULL_COEFFICIENT_REPLAY",
          "rows": rows, "polynomials": polynomials,
          "coefficient_bounds_compared": coefficients,
          "least_strict_cost_coefficient": str(least_cost),
          "full_output_sha256": raw_sha, "full_output_bytes": raw.stat().st_size,
          "exit_code": run.returncode, "stderr_empty": True,
          "unchanged_inputs": True,
          "sha256": {p.name: value for p, value in before.items()}}
out.parent.mkdir(parents=True, exist_ok=True)
out.write_text(json.dumps(result, indent=2)+"\n")
print(json.dumps(result, indent=2))
