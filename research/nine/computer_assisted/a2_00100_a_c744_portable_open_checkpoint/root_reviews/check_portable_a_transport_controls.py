#!/usr/bin/env python3
"""Exercise the portable launcher's path/child boundary on small exact fixtures."""
from pathlib import Path
import argparse, hashlib, json, shutil, subprocess, sys, time


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def dump(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + '\n')


CASE_BODY = r'''
import importlib.util, json, os, pathlib, subprocess, sys
from pathlib import Path
root=Path(sys.argv[1]); case=sys.argv[2]
launcher=root/'packet/replay_portable_a_c744_packet.py'
spec=importlib.util.spec_from_file_location('portable_transport_under_test',launcher)
module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
original_path_class=pathlib.Path
try:
    inventory,aliases,locate=module.install(root/'packet',root/'output')
    from pathlib import Path as Transport
    old='/workspace/portable_A_transport_fixture/original/input.json'
    if case=='valid_aliases':
        assert Transport(old).read_text()=='{"exact":"17/31"}\n'
        assert (Transport('/workspace/portable_A_transport_fixture/original')/'input.json').read_text()==Transport(old).read_text()
        assert Transport('/workspace/portable_A_transport_fixture/original','input.json').read_text()==Transport(old).read_text()
        assert sys.modules['pathlib'].Path is original_path_class
    elif case=='isolated_child':
        run=subprocess.run([sys.executable,'-B','-S',str(root/'packet/payload/ac_work/tree/fixture.py')],capture_output=True,text=True)
        assert run.returncode==0,run.stdout+run.stderr
        assert 'PORTABLE_FIXTURE_CHILD_OK' in run.stdout
        assert len(list((root/'output/isolated_child_receipts').glob('*.json')))==1
    elif case=='external_workspace_read':
        (root/'outside.json').read_text()
    elif case=='unlisted_packet_read':
        (root/'packet/unlisted.json').read_text()
    elif case=='frozen_input_write':
        (root/'packet/payload/ac_work/tree/input.json').write_text('changed')
    elif case=='numerical_import':
        __import__('numpy')
    elif case=='foreign_subprocess':
        subprocess.run(['/bin/echo','must not execute'])
    elif case=='missing_file_alias':
        Transport(old).read_text()
    else:
        assert case in ('wrong_input_hash','escaping_binding')
        raise RuntimeError('malformed fixture was accepted')
except AssertionError as error:
    if case in ('valid_aliases','isolated_child'):
        raise
    print(json.dumps({'case':case,'status':'REJECTED_EXPECTED','reason':str(error)}))
else:
    assert case in ('valid_aliases','isolated_child'),('control did not reject',case)
    print(json.dumps({'case':case,'status':'PASS'}))
'''


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('launcher', type=Path)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    launcher = args.launcher.resolve()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    started = time.monotonic()
    cases = ('valid_aliases', 'isolated_child', 'external_workspace_read',
             'unlisted_packet_read', 'frozen_input_write', 'numerical_import',
             'foreign_subprocess', 'missing_file_alias', 'wrong_input_hash', 'escaping_binding')
    results = []
    for case in cases:
        root = output / case
        packet = root / 'packet'
        code = packet / 'payload/ac_work/tree'
        code.mkdir(parents=True)
        (root / 'outside.json').write_text('outside workspace fixture\n')
        (code / 'input.json').write_text('{"exact":"17/31"}\n')
        (code / 'fixture.py').write_text(
            "from pathlib import Path\n"
            "assert Path('/workspace/portable_A_transport_fixture/original/input.json').read_text()=='{\"exact\":\"17/31\"}\\n'\n"
            "print('PORTABLE_FIXTURE_CHILD_OK')\n")
        shutil.copy2(launcher, packet / launcher.name)
        if launcher.name != 'replay_portable_a_c744_packet.py':
            shutil.copy2(launcher, packet / 'replay_portable_a_c744_packet.py')
        old = '/workspace/portable_A_transport_fixture/original/input.json'
        binding = dict(files={old:dict(path='payload/ac_work/tree/input.json',sha256=sha(code/'input.json'))},
                       directories={'/workspace/portable_A_transport_fixture/original':'payload/ac_work/tree'})
        if case == 'missing_file_alias':
            binding['files'] = {}
        elif case == 'escaping_binding':
            binding['files'][old]['path'] = '../outside.json'
        dump(packet / 'BINDINGS.json', binding)
        inventory = {str(p.relative_to(packet)):sha(p) for p in packet.rglob('*') if p.is_file()}
        if case == 'wrong_input_hash':
            inventory['payload/ac_work/tree/input.json'] = '0'*64
        dump(packet/'INPUT_MANIFEST.json', dict(files=inventory))
        if case == 'unlisted_packet_read':
            (packet/'unlisted.json').write_text('not manifest-bound\n')
        run = subprocess.run([sys.executable,'-B','-S','-c',CASE_BODY,str(root),case],
                             capture_output=True,text=True)
        (root/'CONTROL.log').write_text(run.stdout+run.stderr)
        assert run.returncode == 0, (case,run.stdout,run.stderr)
        result = json.loads(run.stdout.splitlines()[-1])
        assert result['case'] == case
        results.append(result)
    report = dict(status='PASS_PORTABLE_A_FILENAME_AND_CHILD_BOUNDARY_CONTROLS',
        launcher_sha256=sha(launcher),control_source_sha256=sha(__file__),
        positive_controls=2,rejected_damaged_or_disallowed_controls=8,controls=results,
        exact_mathematical_sources_or_proofs_modified=False,new_original_cells=0,new_masks=0,
        seconds=time.monotonic()-started)
    dump(output/'CONTROLS.json',report)
    print(json.dumps(report,indent=2),flush=True)


if __name__ == '__main__':
    main()
