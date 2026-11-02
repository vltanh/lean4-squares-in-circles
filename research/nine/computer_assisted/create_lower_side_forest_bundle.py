#!/usr/bin/env python3
"""Package unchanged roots and raw reports after all 128 exact replays pass.

This script binds existing accepted records; it performs no arithmetic replay.
The archive is deterministic ZIP_STORED over the unchanged gzip certificates,
the unchanged raw per-root exact reports, and the unchanged discovery records.
"""
from pathlib import Path
import argparse
import gzip
import hashlib
import json
import zipfile

BASE = Path(__file__).resolve().parent


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root-directory", type=Path, default=BASE / "lower_side_roots")
    args = parser.parse_args()
    source_hash = sha((BASE / "verify_lower_side_exact.cpp").read_bytes())
    producer_hash = sha((BASE / "discover_lower_side_coupled.cpp").read_bytes())
    original_wrapper_hash = sha((BASE / "replay_lower_side_roots.py").read_bytes())
    forest_wrapper_hash = sha((BASE / "verify_lower_side_forest.py").read_bytes())
    binding = json.loads((BASE / "lower_side_no_extra_build_binding.json").read_bytes())
    if (binding.get("result") != "PASS" or binding["source_sha256"] != source_hash
            or binding["replayed_executable_sha256"] != sha((BASE / "verify_lower_side_exact").read_bytes())
            or not binding["executables_byte_identical"]):
        raise ValueError("missing complete-source/executable binding")
    archive = BASE / "lower_side_no_extra_forest.zip"
    records, reports = [], []
    with zipfile.ZipFile(archive, "w", compression=zipfile.ZIP_STORED) as z:
        for rid in range(128):
            files = [("roots", "json.gz"), ("replays", "exact.json"), ("discovery", "record.json")]
            parts = {kind: (args.root_directory / f"root_{rid:03d}.{suffix}").read_bytes()
                     for kind, suffix in files}
            data = json.loads(gzip.decompress(parts["roots"]))
            report = json.loads(parts["replays"])
            discovery = json.loads(parts["discovery"])
            leaves, nodes = data["leaves"], data["nodes"]
            root_hash, payload_hash = sha(parts["roots"]), sha(gzip.decompress(parts["roots"]))
            if not (report.get("result") == "PASS" and report.get("complete") is True
                    and report["root"] == rid and report["minimum_reserve_numerator"] > 0
                    and report["checker_sha256"] == source_hash
                    and report["wrapper_sha256"] == original_wrapper_hash
                    and discovery["source_sha256"] == producer_hash
                    and report["nodes"] == discovery["nodes"] == nodes == 2 * leaves - 1
                    and report["leaves"] == discovery["leaves"] == leaves
                    and report["sha256"] == discovery["sha256"] == root_hash
                    and report["payload_sha256"] == discovery["payload_sha256"] == payload_hash
                    and report["depth"] == data["max_depth"] == discovery["depth"]
                    and report["rules"] == data["counts"]
                    and data["leaves_per_root"] == [leaves if i == rid else 0 for i in range(128)]
                    and data["frontier_count"] == 0):
                raise ValueError(f"root {rid} not completely and consistently replayed")
            for kind, suffix in files:
                info = zipfile.ZipInfo(f"{kind}/root_{rid:03d}.{suffix}", (2000, 1, 1, 0, 0, 0))
                info.compress_type = zipfile.ZIP_STORED
                info.create_system = 3
                info.external_attr = 0o100644 << 16
                z.writestr(info, parts[kind])
            records.append(dict(root=rid, sha256=root_hash, payload_sha256=payload_hash,
                                exact_report_sha256=sha(parts["replays"]),
                                discovery_record_sha256=sha(parts["discovery"]),
                                leaves=leaves, nodes=nodes, depth=report["depth"],
                                minimum_reserve_numerator=report["minimum_reserve_numerator"],
                                rules=report["rules"]))
            reports.append(report)
    aggregate = dict(root_count=128, frontier_count=0,
                     leaves=sum(r["leaves"] for r in reports), nodes=sum(r["nodes"] for r in reports),
                     maximum_depth=max(r["depth"] for r in reports),
                     minimum_reserve_numerator=min(r["minimum_reserve_numerator"] for r in reports),
                     denominator="2^48", rules=[sum(r["rules"][i] for r in reports) for i in range(23)])
    manifest = dict(schema="weak_middle_lower_side_forest_manifest_v1", root_count=128,
                    frontier_count=0, archive=archive.name, archive_sha256=sha(archive.read_bytes()),
                    archive_bytes=archive.stat().st_size,
                    checker_source_sha256=source_hash,
                    checker_executable_sha256=binding["replayed_executable_sha256"],
                    producer_source_sha256=producer_hash,
                    original_replay_wrapper_sha256=original_wrapper_hash,
                    forest_replayer_sha256=forest_wrapper_hash,
                    build_binding_sha256=sha((BASE / "lower_side_no_extra_build_binding.json").read_bytes()),
                    aggregate=aggregate, roots=records)
    manifest_path = BASE / "lower_side_no_extra_manifest.json"
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
    report = dict(result="PASS", complete=True, mode="aggregate_of_128_unchanged_full_exact_replays",
                  **aggregate, archive_sha256=manifest["archive_sha256"],
                  manifest_sha256=sha(manifest_path.read_bytes()),
                  checker_source_sha256=source_hash,
                  checker_executable_sha256=binding["replayed_executable_sha256"],
                  original_replay_wrapper_sha256=original_wrapper_hash,
                  recorded_arithmetic_seconds=sum(r["seconds"] for r in reports),
                  raw_reports="Each unchanged raw report is pinned in replays/ in the archive.")
    (BASE / "lower_side_no_extra_independent_replay.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
