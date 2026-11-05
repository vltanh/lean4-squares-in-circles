#!/usr/bin/env python3
"""Relocate only pinned packet/foundation bytes, then repeat exact controls."""
if not __debug__:
    raise RuntimeError('Relocated exact controls reject optimized Python.')
import argparse
from hashlib import sha256
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

PACKET='4c1fb0040f43281fd6e21bbece48d7293d0310a7341f490930c40ef51b689023'
FOUNDATION='ac389f6184af6503294a13fb30c1da82e38d052a5d579bf43ccd4a0017b0485b'
CONTROLS='ea2239fe63020a44e9e35da24008df2f300b2a5d4734995c9c134172048681e0'
def digest(path):return sha256(Path(path).read_bytes()).hexdigest()
def checked_copy(source,destination,manifest_name,expected):
    assert digest(source/manifest_name)==expected
    manifest=json.loads((source/manifest_name).read_text())
    destination.mkdir()
    for name,entry in manifest['files'].items():
        original=(source/name).resolve()
        assert original.is_relative_to(source) and not (source/name).is_symlink()
        assert original.stat().st_size==entry['bytes'] and digest(original)==entry['sha256']
        target=destination/name;target.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(original,target)
        assert target.stat().st_size==entry['bytes'] and digest(target)==entry['sha256']
    shutil.copyfile(source/manifest_name,destination/manifest_name)
    assert digest(destination/manifest_name)==expected
    return manifest
def check_again(folder,manifest,name,expected):
    assert digest(folder/name)==expected
    for relative,entry in manifest['files'].items():
        target=folder/relative
        assert target.stat().st_size==entry['bytes'] and digest(target)==entry['sha256']

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--packet',type=Path,required=True)
    parser.add_argument('--foundation',type=Path,required=True)
    parser.add_argument('--output-folder',type=Path,required=True)
    args=parser.parse_args()
    source=args.packet.resolve();foundation=args.foundation.resolve();output=args.output_folder.resolve()
    assert not output.is_relative_to(source) and not output.is_relative_to(foundation)
    output.mkdir(parents=True,exist_ok=False)
    parent=Path(tempfile.mkdtemp(prefix='strict011_guards_v2_relocated_')).resolve()
    packet=checked_copy(source,parent/'packet','PREMISE_BINDINGS.json',PACKET)
    base=checked_copy(foundation,parent/'foundation','CHECKPOINT_MANIFEST.json',FOUNDATION)
    command=[sys.executable,'-B','-S',str(parent/'packet/check_guards.py'),
             '--foundation',str(parent/'foundation'),'--output',str(output/'FRESH_CONTROLS.json')]
    with (output/'process.log').open('x') as log:
        result=subprocess.run(command,stdout=log,stderr=subprocess.STDOUT,check=False)
    assert result.returncode==0
    assert digest(output/'FRESH_CONTROLS.json')==CONTROLS
    assert (output/'FRESH_CONTROLS.json').read_bytes()==(source/'FRESH_GUARD_CONTROLS.json').read_bytes()
    check_again(source,packet,'PREMISE_BINDINGS.json',PACKET)
    check_again(parent/'packet',packet,'PREMISE_BINDINGS.json',PACKET)
    check_again(foundation,base,'CHECKPOINT_MANIFEST.json',FOUNDATION)
    check_again(parent/'foundation',base,'CHECKPOINT_MANIFEST.json',FOUNDATION)
    receipt=dict(status='PASS_RELOCATED_STRICT011_HI_C_V2_GUARD_CONTROLS',
        child_exit_code=result.returncode,packet_binding_sha256=PACKET,
        foundation_manifest_sha256=FOUNDATION,exact_control_report_sha256=CONTROLS,
        native_and_relocated_report_bytes_identical=True,
        packet_members=len(packet['files']),foundation_members=len(base['files']),
        before_and_after_source_and_copy_hashes_verified=True,
        launcher_sha256=digest(__file__),relocated_directory=str(parent),
        scalar_replay_performed=False,numerical_solver_called=False,
        original_cell_credit=0,whole_mask_credit=0)
    with (output/'RECEIPT.json').open('x') as stream:json.dump(receipt,stream,indent=2,sort_keys=True);stream.write('\n')
    print(json.dumps(dict(status=receipt['status'],receipt_sha256=digest(output/'RECEIPT.json'),
                         output=str(output))))
if __name__=='__main__':main()
