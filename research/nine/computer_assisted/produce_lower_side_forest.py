#!/usr/bin/env python3
"""Portable untrusted discovery driver for all 128 fixed lower-side roots.

The producer is guidance only. Every resulting certificate requires the
separate exact source in verify_lower_side_exact.cpp and its complete replay.
Uses only the Python standard library and a C++17 compiler.
"""
from pathlib import Path
import argparse
import concurrent.futures
import gzip
import hashlib
import json
import subprocess
import tempfile
import time

BASE = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-directory", type=Path, default=BASE / "lower_side_roots")
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--first", type=int, default=0)
    parser.add_argument("--last", type=int, default=127)
    args = parser.parse_args()
    if not (1 <= args.jobs <= 8 and 0 <= args.first <= args.last < 128):
        raise ValueError("invalid jobs or fixed root range")
    out = args.output_directory.resolve()
    out.mkdir(parents=True, exist_ok=True)
    source = BASE / "discover_lower_side_coupled.cpp"
    source_hash = hashlib.sha256(source.read_bytes()).hexdigest()
    with tempfile.TemporaryDirectory(prefix="lower-side-discovery-") as tmp:
        executable = Path(tmp) / "discover_lower_side_coupled"
        subprocess.run(["g++", "-O3", "-std=c++17", str(source), "-o", str(executable)], check=True)

        def run(rid):
            raw = out / f"root_{rid:03d}.json"
            checkpoint = Path(str(raw) + ".checkpoint")
            zipped = out / f"root_{rid:03d}.json.gz"
            record_path = out / f"root_{rid:03d}.record.json"
            if record_path.exists():
                record = json.loads(record_path.read_text())
                if record["source_sha256"] != source_hash:
                    raise ValueError("existing root was produced by another source")
                if hashlib.sha256(zipped.read_bytes()).hexdigest() != record["sha256"]:
                    raise ValueError("existing root bytes changed")
                return record
            start = time.monotonic()
            while True:
                if raw.exists():
                    payload = raw.read_bytes()
                    data = json.loads(payload)
                    if data["proof_status"] == "discovery_complete_pending_independent_replay":
                        if data["leaves_per_root"] != [data["leaves"] if i == rid else 0 for i in range(128)]:
                            raise ValueError("producer returned the wrong fixed root")
                        with zipped.open("wb") as dst:
                            with gzip.GzipFile(fileobj=dst, mode="wb", mtime=0) as stream:
                                stream.write(payload)
                        record = dict(root=rid, discovery_complete=True, leaves=data["leaves"],
                                      nodes=data["nodes"], depth=data["max_depth"],
                                      source_sha256=source_hash, certificate=zipped.name,
                                      sha256=hashlib.sha256(zipped.read_bytes()).hexdigest(),
                                      payload_sha256=hashlib.sha256(payload).hexdigest(),
                                      seconds=time.monotonic()-start)
                        record_path.write_text(json.dumps(record, indent=2) + "\n")
                        raw.unlink()
                        checkpoint.unlink(missing_ok=True)
                        return record
                argv = [str(executable), "--first", str(rid), "--last", str(rid),
                        "--seconds", "55", "--nodes", "200000000", "--out", str(raw)]
                if checkpoint.exists():
                    argv.append("--resume")
                with (out / f"root_{rid:03d}.log").open("ab") as log:
                    subprocess.run(argv, stdout=log, stderr=log, check=True)

        with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
            for result in pool.map(run, range(args.first, args.last + 1)):
                print(json.dumps(result), flush=True)
    print("Discovery finished; every root still requires independent exact replay.", flush=True)


if __name__ == "__main__":
    main()
