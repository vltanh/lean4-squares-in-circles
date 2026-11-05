#!/usr/bin/env python3
"""Small real-filesystem controls for the atomic JSON checkpoint writer."""
from pathlib import Path
from unittest import mock
import errno
import hashlib
import importlib.util
import json
import os
import stat
import tempfile


HERE = Path(__file__).resolve().parent
SOURCE = HERE / "atomic_json_checkpoint.py"
spec = importlib.util.spec_from_file_location("checked_atomic_json_checkpoint", SOURCE)
ATOMIC = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ATOMIC)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def run():
    checks = []
    source_before = sha(SOURCE)
    value = {"exact": ["-9027608472833/281474976710656", [1, 2]],
             "unicode": "α", "nested": {"open": True, "none": None},
             "long": "x" * 500}
    expected = (json.dumps(value, indent=2) + "\n").encode("utf-8")
    with tempfile.TemporaryDirectory(prefix="atomic_json_checkpoint_controls_") as raw:
        root = Path(raw)
        target = root / "node_00001.json"
        target.write_bytes(b"previous complete exact record\n")
        target.chmod(0o640)
        old_bytes = target.read_bytes()
        old_stat = target.stat()
        real_dump = json.dump

        def assert_old():
            assert target.read_bytes() == old_bytes
            current = target.stat()
            assert (current.st_dev, current.st_ino, current.st_mode) == (
                old_stat.st_dev, old_stat.st_ino, old_stat.st_mode)

        def failure(label, patch):
            before = set(root.iterdir())
            with patch:
                try:
                    ATOMIC.write_json(target, value)
                except OSError as error:
                    assert error.errno in (errno.ENOSPC, errno.EACCES)
                    assert any("destination_replaced=False" in note
                               for note in getattr(error, "__notes__", []))
                else:
                    raise AssertionError("Injected failure was not propagated: " + label)
            assert_old()
            added = set(root.iterdir()) - before
            assert len(added) == 1
            diagnostic = added.pop()
            assert diagnostic.name.startswith(target.name + ".atomic-")
            assert diagnostic.is_file()
            checks.append(label + ": prior bytes/inode/mode intact; diagnostic retained; OSError propagated")
            return diagnostic

        def fail_before(value, stream, **kwargs):
            raise OSError(errno.ENOSPC, "injected before first JSON write")

        before_temp = failure("ENOSPC before serialization", mock.patch.object(
            ATOMIC.json, "dump", side_effect=fail_before))
        assert before_temp.read_bytes() == b""

        class LimitedWriter:
            def __init__(self, stream):
                self.stream = stream
                self.remaining = 111

            def write(self, text):
                if len(text) <= self.remaining:
                    self.remaining -= len(text)
                    return self.stream.write(text)
                if self.remaining:
                    self.stream.write(text[:self.remaining])
                    self.remaining = 0
                raise OSError(errno.ENOSPC, "injected within JSON write")

        def fail_within(value, stream, **kwargs):
            return real_dump(value, LimitedWriter(stream), **kwargs)

        partial = failure("ENOSPC within serialization", mock.patch.object(
            ATOMIC.json, "dump", side_effect=fail_within))
        assert partial.read_bytes() == expected[:111]

        replaced_failure = failure("os.replace failure", mock.patch.object(
            ATOMIC.os, "replace", side_effect=OSError(errno.EACCES, "injected replace failure")))
        assert replaced_failure.read_bytes() == expected

        file_sync_failure = failure("file fsync ENOSPC", mock.patch.object(
            ATOMIC.os, "fsync", side_effect=OSError(errno.ENOSPC, "injected file fsync failure")))
        assert file_sync_failure.read_bytes() == expected

        before = set(root.iterdir())
        calls = []
        real_fsync = os.fsync

        def record_sync(fd):
            calls.append("directory" if stat.S_ISDIR(os.fstat(fd).st_mode) else "file")
            return real_fsync(fd)

        with mock.patch.object(ATOMIC.os, "fsync", side_effect=record_sync):
            ATOMIC.write_json(target, value)
        assert target.read_bytes() == expected
        assert stat.S_IMODE(target.stat().st_mode) == 0o640
        assert set(root.iterdir()) == before
        assert calls == ["file", "directory"]
        checks.append("Success: byte-identical indent2/newline serialization; existing0640 mode preserved; file then directory fsync; no temp remains")

        fresh = root / "new_manifest.json"
        prior_umask = os.umask(0o077)
        try:
            ATOMIC.write_json(fresh, value)
        finally:
            os.umask(prior_umask)
        assert fresh.read_bytes() == expected
        assert stat.S_IMODE(fresh.stat().st_mode) == 0o644
        checks.append("New file: exact0644 mode despite restrictive umask; identical bytes")

        before = set(root.iterdir())
        updated = {"new": "valid completed checkpoint"}
        updated_bytes = (json.dumps(updated, indent=2) + "\n").encode()

        def fail_directory_sync(fd):
            if stat.S_ISDIR(os.fstat(fd).st_mode):
                raise OSError(errno.ENOSPC, "injected directory fsync failure")
            return real_fsync(fd)

        with mock.patch.object(ATOMIC.os, "fsync", side_effect=fail_directory_sync):
            try:
                ATOMIC.write_json(target, updated)
            except OSError as error:
                assert error.errno == errno.ENOSPC
                assert any("destination_replaced=True" in note and
                           "diagnostic_temp_retained=True" in note
                           for note in error.__notes__)
            else:
                raise AssertionError("Directory fsync failure was not propagated")
        assert target.read_bytes() == updated_bytes
        added = set(root.iterdir()) - before
        assert len(added) == 1
        diagnostic = added.pop()
        assert diagnostic.read_bytes() == updated_bytes
        assert (diagnostic.stat().st_dev, diagnostic.stat().st_ino) == (
            target.stat().st_dev, target.stat().st_ino)
        checks.append("Post-replace directory-fsync failure: new installed bytes and exact diagnostic link retained; explicit replaced=True; error propagated")

        symbolic = root / "symbolic.json"
        symbolic.symlink_to(target.name)
        before = set(root.iterdir())
        try:
            ATOMIC.write_json(symbolic, value)
        except ValueError:
            pass
        else:
            raise AssertionError("Symlink checkpoint destination accepted")
        assert symbolic.is_symlink() and target.read_bytes() == updated_bytes
        assert set(root.iterdir()) == before
        checks.append("Symlink destination rejected before staging; linked target unchanged")

    assert sha(SOURCE) == source_before
    return {"status": "PASS_ATOMIC_JSON_CHECKPOINT_CONTROLS", "count": len(checks),
            "checks": checks, "helper_sha256": source_before,
            "control_source_sha256": sha(__file__), "disposable_fixtures_only": True,
            "live_driver_or_proof_path_modified": False,
            "multi_file_transaction_claimed": False}


if __name__ == "__main__":
    result = run()
    path = HERE / "ATOMIC_JSON_CHECKPOINT_CONTROLS.json"
    with path.open("x") as stream:
        json.dump(result, stream, indent=2)
        stream.write("\n")
    print(json.dumps({"status": result["status"], "count": result["count"],
                      "report_sha256": sha(path)}))
