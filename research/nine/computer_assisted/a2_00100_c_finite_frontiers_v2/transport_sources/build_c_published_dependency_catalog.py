"""Hash every member of four already published accepted dependency archives.

This is a byte-provenance audit, not a mathematical replay. Direct archives
must match their immutable Git blob identity. The multipart A archive must
match every published part and the published whole-archive SHA256 manifest.
No extraction, source rewriting, repository mutation or numerical import.
"""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import tarfile
import time

ap = argparse.ArgumentParser()
ap.add_argument("repo", type=Path)
ap.add_argument("output", type=Path)
args = ap.parse_args()
repo = args.repo.resolve()
w = repo / "research/nine/.runs/closure_20261104"
c = w / "c_runtime"
commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=repo, text=True).strip()

def git_blob(path):
    line = subprocess.check_output(["git", "ls-tree", commit, "--", path], cwd=repo, text=True).strip()
    fields = line.split()
    assert fields[0] == "100644" and fields[1] == "blob" and fields[3] == path
    return fields[2]

def hash_git_bytes(raw):
    return hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()

metadata_path = "research/nine/computer_assisted/a2_00100_a_c744_portable_open_checkpoint/ARCHIVE_MANIFEST.json"
metadata_raw = subprocess.check_output(["git", "show", commit + ":" + metadata_path], cwd=repo)
assert hash_git_bytes(metadata_raw) == git_blob(metadata_path)
metadata = json.loads(metadata_raw)
specs = [
    dict(id="a_c744_portable_open_checkpoint", local=w/"a_dependencies/a_c744_portable_open_checkpoint.tar.xz",
         public_directory="research/nine/computer_assisted/a2_00100_a_c744_portable_open_checkpoint",
         metadata_path=metadata_path, metadata_sha256=hashlib.sha256(metadata_raw).hexdigest(),
         expected_sha256=metadata["archive_sha256"], expected_bytes=metadata["archive_bytes"]),
    dict(id="cb882_whole_eight_checkpoint", local=c/"fetched/a2_00100_cb882_whole_eight_checkpoint.tar.xz",
         public_archive="research/nine/computer_assisted/a2_00100_cb882_whole_eight_checkpoint.tar.xz"),
    dict(id="c887_fresh_whole_state", local=c/"fetched/c887_fresh_whole_state_v1.tar.xz",
         public_archive="research/nine/computer_assisted/c887_fresh_original_starting_state_v1/c887_fresh_whole_state_v1.tar.xz"),
    dict(id="cd402_original_checkpoint_delta", local=c/"fetched/cd402_fresh_original_checkpoint_v1_delta.tar.xz",
         public_archive="research/nine/computer_assisted/a2_00100_cd402_fresh_original_checkpoint_v1/cd402_fresh_original_checkpoint_v1_delta.tar.xz"),
]
started = time.monotonic()
archives = []
members = []
for spec in specs:
    local = spec["local"]
    raw = local.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    identity = dict(id=spec["id"], bytes=len(raw), sha256=digest, published_commit=commit)
    if "public_archive" in spec:
        oid = git_blob(spec["public_archive"])
        assert hash_git_bytes(raw) == oid
        identity.update(published_archive=spec["public_archive"], published_git_blob=oid)
    else:
        assert digest == spec["expected_sha256"] and len(raw) == spec["expected_bytes"]
        offset = 0
        parts = []
        for item in metadata["parts"]:
            chunk = raw[offset:offset+item["bytes"]]
            assert len(chunk) == item["bytes"] and hashlib.sha256(chunk).hexdigest() == item["sha256"]
            path = spec["public_directory"] + "/" + item["file"]
            oid = git_blob(path)
            assert hash_git_bytes(chunk) == oid
            parts.append(dict(path=path, bytes=item["bytes"], sha256=item["sha256"], git_blob=oid))
            offset += item["bytes"]
        assert offset == len(raw)
        identity.update(published_parts=parts, published_archive_manifest=metadata_path,
                        published_archive_manifest_sha256=spec["metadata_sha256"])
    del raw
    seen = set()
    count = expanded = 0
    with tarfile.open(local, "r|xz") as archive:
        for member in archive:
            path = Path(member.name)
            assert not path.is_absolute() and ".." not in path.parts
            if member.isdir():
                continue
            assert member.isfile() and member.name not in seen
            seen.add(member.name)
            source = archive.extractfile(member)
            hasher = hashlib.sha256()
            length = 0
            while True:
                block = source.read(1 << 20)
                if not block:
                    break
                length += len(block)
                hasher.update(block)
            assert length == member.size
            members.append(dict(archive_id=spec["id"], member=member.name,
                                bytes=length, sha256=hasher.hexdigest()))
            count += 1
            expanded += length
    identity.update(regular_members=count, expanded_bytes=expanded)
    archives.append(identity)
    print("CATALOGED", spec["id"], count, digest, flush=True)
report = dict(schema="published_C_dependency_archive_member_catalog_v1",
              status="PASS_PUBLISHED_GIT_BYTES_AND_STREAMED_ARCHIVE_MEMBERS",
              archives=archives, members=members, archive_count=len(archives),
              member_count=len(members), arithmetic_replayed=False,
              new_original_cells=0, new_masks=0, seconds=time.monotonic()-started)
args.output.write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps({k:v for k,v in report.items() if k not in ("archives", "members")}), flush=True)
