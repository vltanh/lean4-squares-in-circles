#!/usr/bin/env python3
"""Restore only byte-identical published strict011 inputs after workspace loss."""
if not __debug__:
    raise RuntimeError('Exact source restoration requires assertions.')
from pathlib import Path
from hashlib import sha256
import json

W=Path('/workspace/scratch/f9f48fcfb253')
REPO=W/'repo/research/nine/computer_assisted'
OUT=Path(__file__).resolve().parent
def digest(path):return sha256(Path(path).read_bytes()).hexdigest()
def frozen(folder,name,expected):
    path=folder/name
    assert digest(path)==expected
    value=json.loads(path.read_text())
    for relative,entry in value['files'].items():
        child=(folder/relative).resolve()
        assert child.is_relative_to(folder) and child.stat().st_size==entry['bytes']
        assert digest(child)==entry['sha256']
    return value

foundation=REPO/'strict_011_rebuilt_foundations_v3/checkpoint'
first=REPO/'strict_011_discovery_first_use_v1'
frozen_foundation=frozen(foundation,'CHECKPOINT_MANIFEST.json','ac389f6184af6503294a13fb30c1da82e38d052a5d579bf43ccd4a0017b0485b')
frozen_first=frozen(first,'PUBLICATION_MANIFEST.json','83cb6dacf09d87c6c62728a521d7c832a9098e1b50c1744f33da678452c4ef17')
frozen_discovery=frozen(first/'discovery','SOURCE_FREEZE.json','ddfedb0223c21441359d9b23d1cf49c77c7a87800d9e4f61e1b8f016abf44965')
retained=Path('/tmp/strict011_first_use_portable_mwngpeax/packet')
frozen(retained,'PUBLICATION_MANIFEST.json','83cb6dacf09d87c6c62728a521d7c832a9098e1b50c1744f33da678452c4ef17')
for relative in frozen_first['files']:
    assert (first/relative).read_bytes()==(retained/relative).read_bytes()

copies=[]
def copy(source,target):
    assert source.is_file() and not source.is_symlink()
    data=source.read_bytes();expected=sha256(data).hexdigest()
    if target.exists():
        assert target.is_file() and not target.is_symlink() and target.read_bytes()==data
        action='VERIFIED_IDENTICAL_EXISTING'
    else:
        target.parent.mkdir(parents=True,exist_ok=True)
        with target.open('xb') as stream:stream.write(data)
        action='RESTORED_ABSENT_ONLY'
    assert digest(source)==digest(target)==expected
    copies.append(dict(source=str(source),target=str(target),bytes=len(data),sha256=expected,action=action))

for relative in list(frozen_foundation['files'])+['CHECKPOINT_MANIFEST.json']:
    copy(foundation/relative,W/'global_work/strict_011_rebuilt_v3'/relative)
for relative in list(frozen_discovery['files'])+['SOURCE_FREEZE.json']:
    copy(first/'discovery'/relative,W/'global_work/strict_011_discovery_v1'/relative)
pilot_members=[relative for relative in frozen_first['files'] if relative.startswith('actual_pilot/')]
assert len(pilot_members)==12
for relative in pilot_members:
    copy(first/relative,OUT/'accepted_first_actual_pilot'/Path(relative).relative_to('actual_pilot'))
for item in copies:
    assert digest(item['source'])==digest(item['target'])==item['sha256']
receipt=dict(status='PASS_PUBLISHED_STRICT011_RUNTIME_AND_FIVE_NODE_PILOT_RESTORATION',
    source_script_sha256=digest(Path(__file__)),foundation_commit='58bb59bac06714502b9438e795d61588a5a45671',
    first_use_commit='35ac6d675d74f013a59804ef5506b74b005b59d6',
    foundation_manifest_sha256=digest(foundation/'CHECKPOINT_MANIFEST.json'),
    first_use_manifest_sha256=digest(first/'PUBLICATION_MANIFEST.json'),
    discovery_freeze_sha256=digest(first/'discovery/SOURCE_FREEZE.json'),
    independent_retained_first_use_copy_checked=True,
    restored_or_verified_files=len(copies),copies=copies,
    later_33_node_or_full_objective_or_growth_tree_restored=False,
    missing_guard_or_C_receipts_replaced=False,numerical_solver_started=False,
    git_index_or_worktree_modified_by_this_script=False,original_cell_credit=0,whole_mask_credit=0)
output=OUT/'PUBLISHED_STRICT011_RUNTIME_RESTORATION.json'
with output.open('x') as stream:json.dump(receipt,stream,indent=2,sort_keys=True);stream.write('\n')
print(json.dumps(dict(status=receipt['status'],files=len(copies),bytes=sum(x['bytes'] for x in copies),
                      receipt=str(output),sha256=digest(output))))
