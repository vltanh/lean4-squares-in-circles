#!/usr/bin/env python3
"""Small discovery storage controls; no numerical search or proof credit."""
if not __debug__:
    raise RuntimeError('Assertions must be enabled')
from pathlib import Path
import errno
import hashlib
import importlib.util
import json
import os
import subprocess
import sys
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
B = HERE.parent
sys.path.insert(0, str(B))
import resume_b_five_proxy_round_atomic_tree_v1 as DRIVER

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    assert sha(DRIVER.__file__) == '12ff1d2b9a8aa044ff212e72c78d6dd0d1fd1167844fbdaadf181a6b8a9103ea'
    assert sha(DRIVER.ATOMIC.__file__) == '2f17219f8689b343f7f1c29e7a314272bd5ace8d25fbee11f58cd20b44543eb3'
    fixtures = HERE / 'atomic_driver_dispatch_fixtures'
    fixtures.mkdir()
    old = b'{"old": true}\n'
    value = {'status': 'OPEN', 'rounds': [], 'unicode': '\u03b1'}
    expected = (json.dumps(value, indent=2) + '\n').encode()
    controls = []
    # Exact ordinary bytes and source-hardlink preservation on replacement.
    source = fixtures / 'immutable_source.json'
    target = fixtures / 'linked_target.json'
    source.write_bytes(old)
    source.chmod(0o640)
    os.link(source, target)
    DRIVER.dump(target, value)
    assert source.read_bytes() == old and target.read_bytes() == expected
    assert (source.stat().st_dev, source.stat().st_ino) != (target.stat().st_dev, target.stat().st_ino)
    assert target.stat().st_mode & 0o777 == 0o640
    controls.append('ordinary JSON bytes, permissions, and immutable hardlink donor preserved')
    # Disk-full at file fsync propagates out of the driver and keeps old target.
    target = fixtures / 'file_fsync_failure.json'
    target.write_bytes(old)
    with patch.object(DRIVER.ATOMIC.os, 'fsync', side_effect=OSError(errno.ENOSPC, 'fixture disk full')):
        try:
            DRIVER.dump(target, value)
        except OSError as error:
            assert error.errno == errno.ENOSPC
        else:
            raise AssertionError('Driver swallowed checkpoint write failure')
    assert target.read_bytes() == old
    assert len(list(fixtures.glob(target.name + '.atomic-*.tmp'))) == 1
    controls.append('file-fsync ENOSPC propagated; prior destination and diagnostic retained')
    # A post-replacement directory failure truthfully leaves the new destination.
    target = fixtures / 'directory_fsync_failure.json'
    target.write_bytes(old)
    original_fsync = DRIVER.ATOMIC.os.fsync
    calls = 0
    def fsync(fd):
        nonlocal calls
        calls += 1
        if calls == 2:
            raise OSError(errno.ENOSPC, 'fixture directory full')
        return original_fsync(fd)
    with patch.object(DRIVER.ATOMIC.os, 'fsync', side_effect=fsync):
        try:
            DRIVER.dump(target, value)
        except OSError as error:
            assert error.errno == errno.ENOSPC
            assert any('destination_replaced=True' in note for note in error.__notes__)
        else:
            raise AssertionError('Driver swallowed directory durability failure')
    assert target.read_bytes() == expected
    diagnostic = list(fixtures.glob(target.name + '.atomic-*.tmp'))
    assert len(diagnostic) == 1 and diagnostic[0].stat().st_ino == target.stat().st_ino
    controls.append('directory-fsync ENOSPC propagated with truthful replaced status and exact inode diagnostic')
    # An invalid source pin must fail before Context/search or node publication.
    seed = json.loads((HERE / 'prepared_B580_complete_frontier/manifest.json').read_text())
    for group in ('sources', 'accepted_geometric_sources'):
        damaged = json.loads(json.dumps(seed))
        first = next(iter(damaged[group]))
        damaged[group][first] = '0' * 64
        folder = fixtures / ('bad_' + group)
        folder.mkdir()
        (folder / 'manifest.json').write_text(json.dumps(damaged, indent=2) + '\n')
        output = fixtures / ('rejected_' + group)
        run = subprocess.run([sys.executable, '-B', str(Path(DRIVER.__file__).resolve()), str(folder), str(output), '--prepare-only'], capture_output=True, text=True)
        assert run.returncode != 0 and 'AssertionError' in run.stderr
        assert not list(output.glob('node_*.json'))
        controls.append(group + ' wrong pin rejected before node/search publication')
    result = {'status': 'PASS_B_ATOMIC_DRIVER_DISPATCH_AND_FAIL_FAST_CONTROLS', 'controls': controls, 'control_count': len(controls), 'driver_sha256': sha(DRIVER.__file__), 'atomic_helper_sha256': sha(DRIVER.ATOMIC.__file__), 'control_source_sha256': sha(Path(__file__)), 'mathematical_or_cover_rules_changed': False, 'numerical_search_run': False, 'whole_original_credit': 0, 'whole_mask_credit': 0, 'one_file_atomicity_only': True, 'node_plus_manifest_transaction_claimed': False}
    destination = HERE / 'B_ATOMIC_DRIVER_DISPATCH_CONTROLS.json'
    destination.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2), flush=True)

if __name__ == '__main__':
    main()
