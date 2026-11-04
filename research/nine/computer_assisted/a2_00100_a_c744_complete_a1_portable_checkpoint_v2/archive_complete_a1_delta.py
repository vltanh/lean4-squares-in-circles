#!/usr/bin/env python3
"""Stream and fully audit the frozen A1 delta; no raw tar is created."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import subprocess
import tarfile
import time


DELTA_SHA = "70c971d00fb804d0765cce66ef540b3c79e18a0eed29b08d5f63793b94eedf4d"
INPUT_SHA = "d8ca6d465aa3831e26d6d0149b8ce734a1043c51694f81a9ce9b9a4e3baaf965"
BASE_ARCHIVE_SHA = "e7ddb4f4e5b943a6f69a0aa861f6721ca49835311fa595ef40a10881b62e4343"
BASE_INPUT_SHA = "6b730ae5e0dabed264d7e71ba6de72bc15f744d7bba619ed8f6c27a86b9097cf"
ROOT = "complete_a1_consequence_delta_v2"


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for block in iter(lambda: f.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def manifest_files(delta: Path) -> dict[str, str]:
    manifest = delta / "DELTA_MANIFEST.json"
    assert digest(manifest) == DELTA_SHA
    data = json.loads(manifest.read_bytes())
    assert data["assembled_input_manifest_sha256"] == INPUT_SHA
    assert data["new_original_cells"] == data["new_masks"] == 0
    expected = dict(data["files"])
    assert "DELTA_MANIFEST.json" not in expected
    expected["DELTA_MANIFEST.json"] = DELTA_SHA
    assert len(expected) == 859
    for name, sha in expected.items():
        p = PurePosixPath(name)
        assert name == str(p) and not p.is_absolute()
        assert all(part not in (".", "..") for part in p.parts)
        assert len(sha) == 64 and int(sha, 16) >= 0
    actual = set()
    for path in delta.rglob("*"):
        assert not path.is_symlink(), ("symlink in frozen delta", str(path))
        if path.is_file():
            actual.add(path.relative_to(delta).as_posix())
        else:
            assert path.is_dir(), ("nonregular entry", str(path))
    assert actual == set(expected), (actual - set(expected), set(expected) - actual)
    for name, sha in sorted(expected.items()):
        assert digest(delta / name) == sha, name
    assert digest(delta / "INPUT_MANIFEST.json") == INPUT_SHA
    return expected


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--delta", required=True, type=Path)
    ap.add_argument("--archive", required=True, type=Path)
    ap.add_argument("--report", required=True, type=Path)
    args = ap.parse_args()
    start = time.monotonic()
    delta = args.delta.resolve(strict=True)
    assert delta.is_dir() and not args.delta.is_symlink()
    archive = args.archive.absolute()
    report = args.report.absolute()
    partial = archive.with_name(archive.name + ".partial")
    for target in (archive, report, partial):
        assert not target.exists() and not target.is_symlink(), str(target)
        assert not target.resolve().is_relative_to(delta), str(target)
        assert target.parent.is_dir()
    expected = manifest_files(delta)
    print(json.dumps({"stage": "INPUTS_VERIFIED", "files": len(expected)}), flush=True)
    sizes = {name: (delta / name).stat().st_size for name in expected}
    assert sum(sizes.values()) == 607136233
    with partial.open("xb") as target:
        proc = subprocess.Popen(["xz", "-T1", "-1", "-c"], stdin=subprocess.PIPE,
                                stdout=target, stderr=subprocess.PIPE)
        assert proc.stdin is not None and proc.stderr is not None
        try:
            with tarfile.open(fileobj=proc.stdin, mode="w|", format=tarfile.PAX_FORMAT) as out:
                for name in sorted(expected):
                    info = tarfile.TarInfo(ROOT + "/" + name)
                    info.size = sizes[name]
                    info.mode = 0o644
                    info.uid = info.gid = info.mtime = 0
                    info.uname = info.gname = ""
                    with (delta / name).open("rb") as source:
                        out.addfile(info, source)
            proc.stdin.close()
            err = proc.stderr.read().decode("utf-8", "replace")
            rc = proc.wait()
            assert rc == 0, ("xz failed", rc, err)
        except BaseException:
            proc.kill()
            proc.wait()
            raise
    print(json.dumps({"stage": "STREAM_COMPLETE", "compressed_bytes": partial.stat().st_size}), flush=True)
    audited = {}
    with tarfile.open(partial, "r|xz") as stream:
        for info in stream:
            assert info.isfile() and not info.issym() and not info.islnk()
            assert info.name.startswith(ROOT + "/")
            name = info.name[len(ROOT) + 1:]
            assert name in expected and name not in audited, name
            assert info.size == sizes[name]
            source = stream.extractfile(info)
            assert source is not None
            h = hashlib.sha256()
            n = 0
            for block in iter(lambda: source.read(1 << 20), b""):
                h.update(block)
                n += len(block)
            assert n == sizes[name] and h.hexdigest() == expected[name], name
            audited[name] = {"sha256": h.hexdigest(), "bytes": n}
    assert set(audited) == set(expected)
    assert manifest_files(delta) == expected
    archive_sha = digest(partial)
    partial.rename(archive)
    result = {
        "status": "PASS_FROZEN_COMPLETE_A1_DELTA_STREAM_ARCHIVE_AND_ALL_MEMBERS",
        "archive": str(archive), "archive_sha256": archive_sha,
        "archive_bytes": archive.stat().st_size, "archive_root": ROOT,
        "compression_command": ["xz", "-T1", "-1", "-c"],
        "raw_tar_created": False, "archive_members": len(audited),
        "uncompressed_member_bytes": sum(sizes.values()),
        "source_files_rehashed_before_and_after": True,
        "every_decompressed_member_rehashed": True,
        "delta_manifest_sha256": DELTA_SHA, "assembled_input_manifest_sha256": INPUT_SHA,
        "required_published_base": {
            "repository_path": "research/nine/computer_assisted/a2_00100_a_c744_portable_open_checkpoint",
            "archive_sha256": BASE_ARCHIVE_SHA, "input_manifest_sha256": BASE_INPUT_SHA,
            "reused_aliases": 1392, "base_included_in_delta_archive": False,
        },
        "source_script_sha256": digest(Path(__file__)),
        "new_original_cells": 0, "new_masks": 0, "whole_original_status": "OPEN",
        "seconds": time.monotonic() - start, "members": audited,
    }
    with report.open("x") as f:
        json.dump(result, f, indent=2)
        f.write("\n")
    print(json.dumps({k: v for k, v in result.items() if k != "members"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
