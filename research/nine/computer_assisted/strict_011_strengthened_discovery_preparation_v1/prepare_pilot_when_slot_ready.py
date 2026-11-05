#!/usr/bin/env python3
"""Run the reviewed frozen pilot only after a fresh free numerical-slot check."""
if not __debug__:
    raise RuntimeError('Launch bindings require assertions.')
from pathlib import Path
from hashlib import sha256
from datetime import datetime, timezone
import argparse
import json
import os
import time

WORK = Path('/workspace/scratch/f9f48fcfb253')
DRIVER = WORK / 'global_work/strict011_strengthened_discovery_v1'
SOURCE = '9df42998d72dc39e358883fc44582e9dc69152f4f5dd20cc1de42d4e5e039ab3'
LAUNCH = '84ba95ee37a7b03aa19119589de768f7fd09f105b271e81780d9cf69fcf8a693'
ROOT_REVIEW = '2a1f69461e0e3939ef41bf54e12db7e9e3f87bd468883a3e4a19f6d56fd720d1'
PEER_REVIEW = '37188deb285431389bdcba9e844b694d9359559f44552a66b83a34d9740c3646'
CONTROL_PREFIXES = ('check_', 'verify_', 'replay_', 'restore_', 'audit_',
                    'capture_', 'prepare_', 'build_', 'freeze_', 'package_')
NUMERICAL_MARKERS = ('resume', 'c_dfs', 'run_conditional', 'discovery',
                     'search', 'solve', 'probe')
MAX_JOBS = 8

def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()

def inventory():
    numerical, controls, unknown = [], [], []
    for process in Path('/proc').iterdir():
        if not process.name.isdigit():
            continue
        try:
            argv = [s.decode() for s in (process / 'cmdline').read_bytes().split(b'\0') if s]
        except (FileNotFoundError, PermissionError, ProcessLookupError, UnicodeDecodeError):
            continue
        if not argv or not Path(argv[0]).name.startswith('python'):
            continue
        scripts = [s for s in argv[1:] if s.endswith('.py')]
        if not scripts:
            continue
        name = Path(scripts[0]).name
        item = {'pid': int(process.name), 'script': scripts[0], 'argv': argv}
        if name == Path(__file__).name or name.startswith(CONTROL_PREFIXES):
            controls.append(item)
        elif any(marker in name for marker in NUMERICAL_MARKERS):
            numerical.append(item)
        else:
            unknown.append(item)
    return {'numerical': numerical, 'controls': controls, 'unclassified': unknown}

def validate_inputs():
    assert digest(DRIVER / 'SOURCE_FREEZE.json') == SOURCE
    assert digest(DRIVER / 'HELD_PILOT_LAUNCH.json') == LAUNCH
    root = WORK / 'd_work/STRICT011_STRENGTHENED_DISCOVERY_ROOT_REVIEW.json'
    peer = WORK / 'ac_work/recovery_20261105_reset2/STRICT011_STRENGTHENED_DISCOVERY_V1_INDEPENDENT_REVIEW.json'
    assert digest(root) == ROOT_REVIEW and digest(peer) == PEER_REVIEW
    assert json.loads(root.read_text())['status'] == 'PASS_ROOT_STRICT011_STRENGTHENED_DISCOVERY_SOURCE_REVIEW'
    freeze = json.loads((DRIVER / 'SOURCE_FREEZE.json').read_text())
    checked = 0
    for name, entry in freeze['files'].items():
        path = (DRIVER / name).resolve()
        assert path.is_relative_to(DRIVER) and not (DRIVER / name).is_symlink()
        assert path.stat().st_size == entry['bytes'] and digest(path) == entry['sha256']
        checked += 1
    dependencies = json.loads((DRIVER / 'DEPENDENCIES.json').read_text())['dependencies']
    for entry in dependencies.values():
        folder = (WORK / entry['workspace_relative_folder']).resolve()
        assert folder.is_relative_to(WORK)
        source = folder / entry['inventory_file']
        assert digest(source) == entry['inventory_sha256']
        members = json.loads(source.read_text())['files']
        assert len(members) == entry['member_count']
        for name, pin in members.items():
            path = (folder / name).resolve()
            assert path.is_relative_to(folder) and not (folder / name).is_symlink()
            assert path.stat().st_size == pin['bytes'] and digest(path) == pin['sha256']
            checked += 1
    launch = json.loads((DRIVER / 'HELD_PILOT_LAUNCH.json').read_text())
    assert launch['status'] == 'PREPARED_HELD_NOT_LAUNCHED'
    assert launch['source_freeze_sha256'] == SOURCE and launch['no_new_branches'] is True
    assert launch['max_nodes'] == 1 and launch['max_LP_time_seconds'] == 2
    argv = launch['argv']
    assert argv[:4] == ['python', '-B', '-u', str(DRIVER / 'strengthened_discovery.py')]
    assert argv[argv.index('--source-binding') + 1] == SOURCE
    assert '--require-positive-corner-weight' in argv
    assert not Path(argv[argv.index('--output') + 1]).exists()
    assert launch['environment'] == {'OPENBLAS_NUM_THREADS':'1', 'OMP_NUM_THREADS':'1', 'MKL_NUM_THREADS':'1'}
    return launch, checked

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--publication-commit', required=True)
    parser.add_argument('--wait-seconds', type=int, default=1800)
    args = parser.parse_args()
    assert len(args.publication_commit) == 40 and all(c in '0123456789abcdef' for c in args.publication_commit)
    assert 0 < args.wait_seconds <= 1800
    launch, checked = validate_inputs()
    started = time.monotonic(); last_notice = -60.0
    while time.monotonic() - started < args.wait_seconds:
        observed = inventory()
        if len(observed['numerical']) < MAX_JOBS and not observed['unclassified']:
            launch, checked = validate_inputs()
            observed = inventory()
            if len(observed['numerical']) >= MAX_JOBS or observed['unclassified']:
                continue
            receipt = dict(schema='strict011_strengthened_pilot_actual_launch_observation_v1',
                observed_utc=datetime.now(timezone.utc).isoformat(),
                source_freeze_sha256=SOURCE, held_launch_sha256=LAUNCH,
                root_review_sha256=ROOT_REVIEW, peer_review_sha256=PEER_REVIEW,
                launcher_sha256=digest(__file__), publication_commit=args.publication_commit,
                input_members_rehashed=checked, process_inventory=observed,
                numerical_jobs_before_launch=len(observed['numerical']),
                numerical_jobs_including_this_launch=len(observed['numerical'])+1,
                maximum_numerical_jobs=MAX_JOBS, argv=launch['argv'],
                environment_overrides=launch['environment'],
                new_original_cells=0, new_masks=0)
            path = WORK / 'd_work/STRICT011_STRENGTHENED_PILOT_ACTUAL_LAUNCH_V1.json'
            with path.open('x') as stream:
                json.dump(receipt, stream, indent=2); stream.write('\n')
                stream.flush(); os.fsync(stream.fileno())
            print(json.dumps(dict(event='REVIEWED_FROZEN_STRENGTHENED_PILOT_LAUNCH',
                receipt=str(path), sha256=digest(path), numerical_jobs_before=len(observed['numerical']))), flush=True)
            environment = dict(os.environ); environment.update(launch['environment'])
            os.chdir(WORK)
            os.execvpe(launch['argv'][0], launch['argv'], environment)
        elapsed = time.monotonic() - started
        if elapsed - last_notice >= 60:
            print(json.dumps(dict(event='WAITING_FOR_NUMERICAL_CAPACITY',
                numerical_jobs=len(observed['numerical']),
                unclassified_scripts=[p['script'] for p in observed['unclassified']],
                elapsed_seconds=round(elapsed,2))), flush=True)
            last_notice = elapsed
        time.sleep(2)
    print(json.dumps(dict(event='CAPACITY_WAIT_LIMIT_REACHED', numerical_job_started=False)), flush=True)

if __name__ == '__main__':
    main()
