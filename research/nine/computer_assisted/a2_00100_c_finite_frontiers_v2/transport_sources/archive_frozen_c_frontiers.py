"""Deterministic finite archive transport and independent streamed byte audit.

This script never replays proof arithmetic or changes a cover. Its receipt
binds the accepted hash/graph audit, inventory, compressed bytes and every
regular archive member. External dependencies remain explicitly external.
"""
from pathlib import Path
import argparse
import hashlib
import json
import lzma
import tarfile
import time


def file_hash(path):
    result = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            result.update(block)
    return result.hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("folder", type=Path)
    parser.add_argument("archive", type=Path)
    parser.add_argument("graph_report", type=Path)
    parser.add_argument("receipt", type=Path)
    args = parser.parse_args()
    started = time.monotonic()
    folder = args.folder.resolve()
    archive = args.archive.resolve()
    assert folder.is_dir() and not archive.exists() and not args.receipt.exists()
    graph_report_raw = args.graph_report.read_bytes()
    graph_report = json.loads(graph_report_raw)
    assert graph_report["status"] == "PASS_HASH_AND_COMPLETE_FRONTIER_TRANSPORT_ONLY"
    assert graph_report["arithmetic_replayed_now"] is False
    assert graph_report["new_original_cells"] == graph_report["new_masks"] == 0
    inventory_raw = (folder / "INVENTORY.json").read_bytes()
    inventory = json.loads(inventory_raw)
    assert graph_report["files_rehashed"] == len(inventory)
    expected = dict(inventory)
    expected["INVENTORY.json"] = dict(
        sha256=hashlib.sha256(inventory_raw).hexdigest(), bytes=len(inventory_raw))
    observed_files = {str(path.relative_to(folder)) for path in folder.rglob("*") if path.is_file()}
    assert observed_files == set(expected)
    temporary = archive.with_suffix(archive.suffix + ".tmp")
    assert not temporary.exists()
    with lzma.open(temporary, "wb", preset=6) as compressed, tarfile.open(fileobj=compressed, mode="w|") as packed:
        for count, name in enumerate(sorted(expected), 1):
            relative = Path(name)
            assert not relative.is_absolute() and ".." not in relative.parts
            path = folder / relative
            assert path.is_file() and not path.is_symlink()
            spec = expected[name]
            assert path.stat().st_size == spec["bytes"]
            assert file_hash(path) == spec["sha256"]
            member = tarfile.TarInfo(folder.name + "/" + name)
            member.size = spec["bytes"]
            member.mtime = 0
            member.mode = 0o644
            member.uid = member.gid = 0
            member.uname = member.gname = ""
            with path.open("rb") as stream:
                packed.addfile(member, stream)
            if count % 200 == 0:
                print("PACKED", count, "OF", len(expected), flush=True)
    temporary.replace(archive)
    visited = set()
    total_bytes = 0
    with tarfile.open(archive, "r|xz") as packed:
        for member in packed:
            assert member.isfile() and not member.issym() and not member.islnk()
            path = Path(member.name)
            assert not path.is_absolute() and ".." not in path.parts
            assert path.parts[0] == folder.name
            name = str(Path(*path.parts[1:]))
            assert name in expected and name not in visited
            assert member.size == expected[name]["bytes"]
            stream = packed.extractfile(member)
            assert stream is not None
            digest, size = hashlib.sha256(), 0
            for block in iter(lambda: stream.read(1024 * 1024), b""):
                digest.update(block)
                size += len(block)
            assert size == member.size and digest.hexdigest() == expected[name]["sha256"]
            visited.add(name)
            total_bytes += size
    assert visited == set(expected)
    assert (folder / "INVENTORY.json").read_bytes() == inventory_raw
    assert args.graph_report.read_bytes() == graph_report_raw
    result = dict(
        status="PASS_FROZEN_C_ARCHIVE_AND_EVERY_MEMBER_BYTE_AUDIT",
        archive=str(archive), archive_sha256=file_hash(archive),
        archive_bytes=archive.stat().st_size, regular_members=len(visited),
        uncompressed_member_bytes=total_bytes,
        inventory_sha256=hashlib.sha256(inventory_raw).hexdigest(),
        manifest_sha256=file_hash(folder / "MANIFEST.json"),
        external_inputs_sha256=file_hash(folder / "EXTERNAL_PROOF_INPUTS.json"),
        published_recovery_sha256=file_hash(folder / "PUBLISHED_DEPENDENCY_RECOVERY.json"),
        published_catalog_sha256=file_hash(folder / "PUBLISHED_DEPENDENCY_ARCHIVE_CATALOG.json"),
        hash_graph_report=str(args.graph_report.resolve()),
        hash_graph_report_sha256=hashlib.sha256(graph_report_raw).hexdigest(),
        archive_auditor_source=str(Path(__file__).resolve()),
        archive_auditor_source_sha256=file_hash(__file__),
        all_regular_members_rehashed=True, no_links_or_path_traversal=True,
        inventory_and_member_names_exhaustive=True,
        independent_arithmetic_replayed_now=False, standalone_arithmetic_packet=False,
        new_original_cells=0, new_masks=0, seconds=time.monotonic() - started)
    args.receipt.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result), flush=True)


if __name__ == "__main__":
    assert __debug__
    main()
