#!/usr/bin/env python3
"""Replay all 128 fixed roots from the immutable lower-side forest archive.

Default: compile the delivered independent exact C++ source and replay every
leaf. --identities-only checks archival byte identities and recorded reports;
that mode deliberately does not claim to perform a fresh arithmetic replay.
No discovery implementation is imported or executed.
"""
from __future__ import annotations

import argparse
import array
import concurrent.futures
import gzip
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import zipfile

BASE = Path(__file__).resolve().parent
SCHEMA = "weak_middle_lower_side_forest_manifest_v1"
CERT_SCHEMA = "weak_middle_lower_side_coupled_cover_v1"
SOURCE_NAME = "verify_lower_side_exact.cpp"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def load_manifest(path):
    manifest = json.loads(path.read_bytes())
    require(manifest.get("schema") == SCHEMA, "unknown manifest schema")
    require(manifest.get("root_count") == 128, "wrong fixed root count")
    require(manifest.get("frontier_count") == 0, "manifest retains a frontier")
    roots = manifest.get("roots")
    require(isinstance(roots, list) and len(roots) == 128, "missing root records")
    require([r.get("root") for r in roots] == list(range(128)),
            "fixed roots must occur exactly once in their canonical order")
    return manifest


def archive_members():
    return {f"{kind}/root_{rid:03d}.{suffix}"
            for rid in range(128)
            for kind, suffix in (("roots", "json.gz"),
                                 ("replays", "exact.json"),
                                 ("discovery", "record.json"))}


def validate_archive(archive, manifest):
    require(sha(archive.read_bytes()) == manifest["archive_sha256"],
            "archive byte identity changed")
    with zipfile.ZipFile(archive) as z:
        names = z.namelist()
        require(len(names) == len(set(names)), "duplicate archive member")
        require(set(names) == archive_members(), "archive member union changed")
        for info in z.infolist():
            require(info.compress_type == zipfile.ZIP_STORED,
                    "archive must retain the original gzip bytes")


def root_payload(archive, record):
    rid = record["root"]
    with zipfile.ZipFile(archive) as z:
        compressed = z.read(f"roots/root_{rid:03d}.json.gz")
        raw_report = z.read(f"replays/root_{rid:03d}.exact.json")
        raw_discovery = z.read(f"discovery/root_{rid:03d}.record.json")
    require(sha(compressed) == record["sha256"], "root gzip identity changed")
    require(sha(raw_report) == record["exact_report_sha256"],
            "raw exact report identity changed")
    require(sha(raw_discovery) == record["discovery_record_sha256"],
            "raw discovery record identity changed")
    payload = gzip.decompress(compressed)
    require(sha(payload) == record["payload_sha256"], "root payload changed")
    data = json.loads(payload)
    require(data.get("schema") == CERT_SCHEMA, "wrong root schema")
    require(data.get("proof_status") == "discovery_complete_pending_independent_replay",
            "wrong producer completion marker")
    require(data.get("root_count") == 128 and data.get("frontier_count") == 0,
            "wrong root union or retained frontier")
    require(data.get("Q") == "1105/256" and data.get("floor") == "1/10"
            and data.get("target") == "no_original_lower_side_extra",
            "wrong original physical target")
    nodes, leaves, events = data.get("nodes"), data.get("leaves"), data.get("events")
    require(type(nodes) is int and type(leaves) is int and leaves >= 1
            and nodes == 2 * leaves - 1, "invalid binary tree counts")
    require(isinstance(events, list) and len(events) == nodes, "wrong event count")
    require(data.get("leaves_per_root") ==
            [leaves if i == rid else 0 for i in range(128)],
            "payload does not identify the fixed root")
    require(all(type(e) is int and -23 <= e <= 6 for e in events),
            "unknown proof event")
    require(nodes == record["nodes"] and leaves == record["leaves"],
            "manifest tree counts differ")
    old = json.loads(raw_report)
    discovery = json.loads(raw_discovery)
    for label, other in (("replay", old), ("discovery", discovery)):
        require(other.get("root") == rid and other.get("nodes") == nodes
                and other.get("leaves") == leaves, label + " counts changed")
        require(other.get("sha256") == record["sha256"] and
                other.get("payload_sha256") == record["payload_sha256"],
                label + " byte binding changed")
    require(old.get("result") == "PASS" and old.get("complete") is True
            and old.get("minimum_reserve_numerator", 0) > 0
            and old.get("denominator") == "2^48", "incomplete archived exact replay")
    require(old.get("depth") == record["depth"] == data.get("max_depth"),
            "depth record changed")
    require(old.get("rules") == record["rules"] == data.get("counts"),
            "terminal counts changed")
    require(old.get("minimum_reserve_numerator") == record["minimum_reserve_numerator"],
            "strict reserve record changed")
    return data, old


def check_one(archive, record, checker=None):
    data, old = root_payload(archive, record)
    if checker is None:
        return old
    rid, nodes, leaves = record["root"], data["nodes"], data["leaves"]
    binary = f"{rid} {nodes} {leaves}\n".encode("ascii") + array.array("b", data["events"]).tobytes()
    process = subprocess.run([str(checker)], input=binary,
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    require(process.returncode == 0,
            f"exact root {rid} rejected: {process.stderr.decode(errors='replace')}")
    report = json.loads(process.stdout)
    for field in ("result", "complete", "root", "nodes", "leaves", "depth",
                  "rules", "minimum_reserve_numerator", "denominator"):
        require(report.get(field) == old.get(field),
                f"fresh replay differs at root {rid}: {field}")
    return report


def aggregate(reports):
    require(sorted(r["root"] for r in reports) == list(range(128)),
            "incomplete replay root union")
    return dict(root_count=128, frontier_count=0,
                leaves=sum(r["leaves"] for r in reports),
                nodes=sum(r["nodes"] for r in reports),
                maximum_depth=max(r["depth"] for r in reports),
                minimum_reserve_numerator=min(r["minimum_reserve_numerator"] for r in reports),
                denominator="2^48",
                rules=[sum(r["rules"][i] for r in reports) for i in range(23)])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path,
                        default=BASE / "lower_side_no_extra_manifest.json")
    parser.add_argument("--archive", type=Path)
    parser.add_argument("--source", type=Path, default=BASE / SOURCE_NAME)
    parser.add_argument("--identities-only", action="store_true")
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    require(1 <= args.jobs <= 8, "jobs must be between 1 and 8")
    manifest = load_manifest(args.manifest)
    archive = args.archive or args.manifest.parent / manifest["archive"]
    validate_archive(archive, manifest)
    require(sha(args.source.read_bytes()) == manifest["checker_source_sha256"],
            "delivered exact checker source identity changed")
    wrapper_hash = sha(Path(__file__).read_bytes())
    require(wrapper_hash == manifest["forest_replayer_sha256"],
            "forest replay wrapper identity changed")
    with tempfile.TemporaryDirectory(prefix="lower-side-exact-") as temp:
        executable = None
        executable_hash = None
        if not args.identities_only:
            executable = Path(temp) / "verify_lower_side_exact"
            subprocess.run(["g++", "-O3", "-std=c++17", str(args.source.resolve()),
                            "-o", str(executable)], check=True)
            executable_hash = sha(executable.read_bytes())
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
            reports = list(pool.map(lambda r: check_one(archive, r, executable),
                                    manifest["roots"]))
        result = aggregate(reports)
    for field, value in result.items():
        require(value == manifest["aggregate"][field],
                "aggregate record differs: " + field)
    for old in reports:
        if args.identities_only:
            require(old["checker_sha256"] == manifest["checker_source_sha256"],
                    "an archived replay used different source")
            require(old["wrapper_sha256"] == manifest["original_replay_wrapper_sha256"],
                    "an archived replay used different wrapper")
    result.update(result="PASS", complete=True,
                  mode=("archive_identity_and_recorded_replay_check" if args.identities_only
                        else "fresh_complete_independent_exact_arithmetic_replay"),
                  archive_sha256=manifest["archive_sha256"],
                  manifest_sha256=sha(args.manifest.read_bytes()),
                  checker_source_sha256=manifest["checker_source_sha256"],
                  forest_replayer_sha256=wrapper_hash,
                  executable_sha256=executable_hash)
    if executable_hash is not None:
        result["matches_recorded_executable"] = executable_hash == manifest["checker_executable_sha256"]
    text = json.dumps(result, indent=2) + "\n"
    if args.report:
        args.report.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
