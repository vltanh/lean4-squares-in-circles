#!/usr/bin/env python3
"""Root archive, literal reserve, source-binding and scope audit; no weighted replay."""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,tarfile,time

R=Path('/workspace/scratch/f9f48fcfb253')
P=R/'b_work/b_angle_policy_checkpoint'
A=R/'b_work/b_angle_policy_checkpoint_archive_v1'
def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb')as f:
        for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
    return h.hexdigest()
def read(p):return json.loads(Path(p).read_text())
start=time.monotonic()
ready=read(A/'ARCHIVE_READY.json');release=read(P/'RELEASE_MANIFEST.json');info=read(P/'CHECKPOINT.json')
assert ready['status']=='PASS_COMPACT_ZERO_CREDIT_POLICY_ARCHIVE'
assert ready['new_original_cells']==ready['new_masks']==0
assert sha(A/ready['archive'])==ready['archive_sha256']
assert (A/ready['archive']).stat().st_size==ready['archive_bytes']
combined=hashlib.sha256()
for part in ready['parts']:
    p=A/part['file'];assert sha(p)==part['sha256']and p.stat().st_size==part['bytes']
    with p.open('rb')as f:
        for b in iter(lambda:f.read(1024*1024),b''):combined.update(b)
assert combined.hexdigest()==ready['archive_sha256']
assert sha(P/'RELEASE_MANIFEST.json')==ready['release_manifest_sha256']
expected=dict(release['files']);expected['RELEASE_MANIFEST.json']=ready['release_manifest_sha256']
seen=set()
with tarfile.open(A/ready['archive'],'r|xz')as archive:
    for member in archive:
        if member.isdir():continue
        assert member.isfile(),('nonregular member',member.name)
        prefix='b_angle_policy_checkpoint/'
        assert member.name.startswith(prefix)
        name=member.name[len(prefix):]
        assert name in expected and name not in seen
        stream=archive.extractfile(member);h=hashlib.sha256()
        for b in iter(lambda:stream.read(1024*1024),b''):h.update(b)
        assert h.hexdigest()==expected[name]==sha(P/name)
        seen.add(name)
assert seen==set(expected)and len(seen)==ready['all_regular_members_verified']==82
cases=[]
for case in info['cases']:
    report=read(P/case['native_report']);tree=read(P/case['tree'])
    assert sha(P/case['native_report'])==case['native_report_sha256']
    assert sha(P/case['tree'])==case['tree_sha256']==report['certificate_sha256']
    assert report['status']=='PASS_COMPLETE_RESTRICTED_PHYSICAL_TREE'
    assert report['complete']and not report['whole_original_proved']
    assert report['initial_original_id']==case['original_id']
    assert report['nodes']==3 and report['excluded_leaves']==2 and report['open_leaves']==0
    nodes={n['index']:read((P/case['tree']).parent/n['file'])for n in tree['nodes']}
    for n in tree['nodes']:assert sha((P/case['tree']).parent/n['file'])==n['sha256']
    root=nodes[0];split=root['split'];assert root['children']==[1,2]and split['kind']=='angle'
    owner=split['owner'];cut=F(split['cut']);lo,hi=map(F,root['record']['final']['angles'][owner]);assert lo<cut<hi
    reserves=[]
    for index,interval in [(1,[lo,cut]),(2,[cut,hi])]:
        node=nodes[index];assert node['parent']==0 and node['depth']==1 and node['choice']==index-1
        assert list(map(F,node['initial']['angles'][owner]))==interval
        t=node['record']['terminal'];assert t['kind']=='positive_exact_reserve'
        actual=F(t['reserve']);lower=F(case['reserve_lower_bounds'][str(index)])
        assert actual>=lower>0
        reserves.append(dict(node=index,displayed_lower_bound=str(lower),exact_reserve=str(actual)))
    assert report['local_rounds']==case['local_rounds']==2
    assert report['local_deductions']==case['local_deductions']
    assert report['local_printed_rows']==case['local_printed_weighted_row_occurrences']
    cases.append(dict(name=case['name'],original_id=case['original_id'],nodes=3,excluded_leaves=2,
        complete_closed_angle_union=True,original_scope='CONDITIONAL_SELECTED_BRANCH_ONLY',
        owner=owner,parent_interval=list(map(str,(lo,hi))),cut=str(cut),reserves=reserves,
        native_report_sha256=case['native_report_sha256']))
assert len(cases)==2 and info['mathematical_rule_changes']==0
assert info['new_original_cells']==info['new_masks']==0 and not info['whole_original_proved']
out=dict(status='PASS_ROOT_TWO_CONDITIONAL_B_UNIONS_SOURCE_TABLE_AND_ARCHIVE_AUDIT',
    archive_sha256=ready['archive_sha256'],archive_bytes=ready['archive_bytes'],
    regular_members_checked=82,all_archived_bytes_match_literal_source=True,
    checkpoint_sha256=sha(P/'CHECKPOINT.json'),input_manifest_sha256=sha(P/'INPUT_MANIFEST.json'),
    cases=cases,weighted_arithmetic_repeated=False,new_original_cells=0,new_masks=0,
    whole_original_proved=False,no_numerical_optimizer_called=True,
    source_sha256=sha(__file__),seconds=time.monotonic()-start)
dest=R/'d_work/B_ANGLE_POLICY_CHECKPOINT_ROOT_AUDIT.json';dest.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items()if k!='cases'}))
