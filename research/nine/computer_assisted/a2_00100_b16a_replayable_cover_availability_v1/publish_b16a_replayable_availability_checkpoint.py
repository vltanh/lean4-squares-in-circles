#!/usr/bin/env python3
"""Audit and preserve B16a availability records; no new proof/ledger credit."""
from pathlib import Path, PurePosixPath
from fractions import Fraction as F
import hashlib
import json
import shutil
import subprocess
import tarfile

W = Path('/workspace/scratch/f9f48fcfb253')
R = W / 'repo'
S = W / 'b_work/b16a_replayable_cover_availability_v1_archive'
REL = 'research/nine/computer_assisted/a2_00100_b16a_replayable_cover_availability_v1'
D = R / REL

def sha(p):
    h = hashlib.sha256()
    with Path(p).open('rb') as f:
        for b in iter(lambda: f.read(1048576), b''):
            h.update(b)
    return h.hexdigest()

def dump(p, d):
    p.write_text(json.dumps(d, indent=2, sort_keys=True)+'\n')

def main():
    assert not D.exists()
    ready = json.loads((S/'ARCHIVE_READY.json').read_text())
    assert sha(S/'ARCHIVE_READY.json') == 'ff0b88ee04927bbda1e32680412c30e8de6c244a98b7791640834de1c210e193'
    assert ready['scope'] == 'BYTE_PRESERVATION_AND_EVIDENCE_ACCOUNTING_ONLY'
    assert ready['self_contained_arithmetic_proof'] is False
    assert ready['new_original_cells'] == ready['new_masks'] == 0
    archive = Path(ready['archive'])
    assert sha(archive) == ready['archive_sha256'] == 'a5e0e136334079483dbe67b3069a57a13a923e9e7af5eed1e75a641040831fac'
    assert archive.stat().st_size == ready['archive_bytes'] == 1034956
    subprocess.run(['xz','-t',str(archive)],check=True)
    inventory_path = S/'MEMBER_MANIFEST.json'
    assert sha(inventory_path) == ready['member_manifest_sha256']
    members = dict(json.loads(inventory_path.read_text())['members'])
    root = ready['archive_root']
    members[root+'/MEMBER_MANIFEST.json'] = {'sha256':sha(inventory_path),'bytes':inventory_path.stat().st_size}
    assert len(members) == 30
    seen = set()
    with tarfile.open(archive,'r|xz') as tf:
        for entry in tf:
            p=PurePosixPath(entry.name)
            assert not p.is_absolute() and '..' not in p.parts
            assert p.parts[0] == root and entry.isfile() and not entry.issym() and not entry.islnk()
            assert entry.name in members and entry.name not in seen
            expected=members[entry.name]
            raw=tf.extractfile(entry).read()
            assert len(raw)==entry.size==expected['bytes']
            assert hashlib.sha256(raw).hexdigest()==expected['sha256']
            if 'source_workspace_relative' in expected:
                assert sha(W/expected['source_workspace_relative'])==expected['sha256']
            seen.add(entry.name)
    assert seen==set(members)
    for part in ready['parts']:
        assert (S/part['file']).stat().st_size==part['bytes'] and sha(S/part['file'])==part['sha256']
    checkpoint=json.loads((S/'CHECKPOINT.json').read_text())
    assert sha(S/'CHECKPOINT.json')==ready['checkpoint_sha256']
    assert checkpoint['historical_published_count']==14 and checkpoint['currently_replayable_count']==11
    assert len(checkpoint['required_published_complete_masters'])==4
    note=W/'b_work/B16A_REPLAYABLE_COVER_RECOVERY_NOTE.md'
    accounting=W/'b_work/B16A_REPLAYABLE_COVER_RECOVERY_INVENTORY.json'
    a=json.loads(accounting.read_text())
    assert sha(accounting)==checkpoint['accounting_inventory_sha256']
    for name,pin in a['input_sha256'].items(): assert sha(name)==pin
    table_path=W/'b_work/B16A_VERIFIED_SIXTEEN_QUARTER_INVENTORY.json'
    table=json.loads(table_path.read_text())
    rows=table['rows']
    assert len(rows)==16 and {tuple(x['tile'])for x in rows}=={(i,j)for i in range(4)for j in range(4)}
    by_tile={tuple(x['tile']):x for x in rows}
    x0,x1=F(by_tile[(0,0)]['rectangle'][0][0]),F(by_tile[(3,0)]['rectangle'][0][1])
    y0,y1=F(by_tile[(0,0)]['rectangle'][1][0]),F(by_tile[(0,3)]['rectangle'][1][1])
    for (i,j),item in by_tile.items():
        assert item['tile_index']==4*i+j
        expected=[[x0+(x1-x0)*F(i,4),x0+(x1-x0)*F(i+1,4)],
                  [y0+(y1-y0)*F(j,4),y0+(y1-y0)*F(j+1,4)]]
        assert [[F(z)for z in interval]for interval in item['rectangle']]==expected
    excluded={k for k,v in by_tile.items()if v['status']=='EXACT_EXCLUDED'}
    opened={k for k,v in by_tile.items()if v['status']=='OPEN'}
    assert len(excluded)==11 and len(opened)==5
    assert opened=={(2,0),(2,1),(2,2),(3,1),(3,3)}=={tuple(x)for x in a['current_pending_tiles']}
    assert excluded=={tuple(x)for x in a['recovered_published_complete_tiles']+a['fresh_reconstructed_complete_tiles']}
    assert a['earlier_mathematics_invalidated'] is False
    register=R/'research/nine/gates/A2_00100_FIXED_FRONTIER.json'
    register_sha=sha(register)
    assert register_sha=='b805df8706151a4eb43bd8c0912205ffbfd67d8dfb582daf441717e04fd023dc'
    cell=next(c for c in json.loads(register.read_text())['cells']if c['id']==a['original_id'])
    assert cell['status']=='OPEN' and cell['path']==table['original_path']

    D.mkdir()
    for name in ['ARCHIVE_READY.json','CHECKPOINT.json','MEMBER_MANIFEST.json']+[x['file']for x in ready['parts']]:
        shutil.copyfile(S/name,D/name)
    for p in [note,accounting,table_path,Path(__file__)]: shutil.copyfile(p,D/p.name)
    report=dict(status='PASS_ROOT_B16A_AVAILABILITY_ARCHIVE_AND_ACCOUNTING_AUDIT',
        scope='BYTE_PRESERVATION_AND_EVIDENCE_ACCOUNTING_ONLY',archive_sha256=sha(archive),
        archive_members=30,evidence_input_files=26,xz_integrity_passed=True,
        every_regular_member_and_source_hash_checked=True,all_sixteen_closed_grid_tiles_checked=True,
        currently_replayable_excluded_quarters=11,pending_tiles=sorted([list(x)for x in opened]),
        historical_fourteen_quarter_publication_unchanged=True,
        new_arithmetic_replay_claimed=False,self_contained_arithmetic_proof=False,
        whole_original_excluded=False,new_original_cells=0,new_masks=0,
        fixed_register_sha256_unchanged=register_sha,source_sha256=sha(__file__))
    dump(D/'ROOT_ARCHIVE_AND_ACCOUNTING_AUDIT.json',report)
    (D/'README.md').write_text('''# B16a: preserved replayable-cover evidence

The current reproducible cover has **11 excluded I quarters and five pending
quarters**. The six published complete quarters and five freshly reconstructed
quarters are separately identified in `B16A_REPLAYABLE_COVER_RECOVERY_NOTE.md`.
I20, I21, I22, I31 and I33 remain pending. B16a itself remains OPEN.

This checkpoint preserves the exact evidence records, including all five new
terminal records, the three OPEN prefixes, the current sixteen-tile inventory
and the historical I32 publication. It distinguishes the old fourteen-quarter
claim from the currently available replayable inputs. It does not invalidate
the earlier mathematics or change any original-cell or mask ledger.

The single archive part has SHA-256
`a5e0e136334079483dbe67b3069a57a13a923e9e7af5eed1e75a641040831fac`.
It is a complete xz tar of 1,034,956 bytes; extract it directly with `tar -xJf`.
The archive root is `b16a_replayable_cover_availability_v1`. Its 30 regular
members include 26 unique evidence inputs. `MEMBER_MANIFEST.json` pins every
member other than itself, which is pinned by `ARCHIVE_READY.json`.

Root independently checks xz integrity, every member and its source bytes,
all sixteen rational grid rectangles, the exact eleven/five status split and
the unchanged original path. This publication repeats no arithmetic proof.
`CHECKPOINT.json` names the four required published complete masters and
249 native reconstruction replay input/provenance hashes; dependencies
marked absent must be supplied for a fresh mathematical replay. The archive
is an availability checkpoint, not a self-contained new proof package.

The original register remains **221 CLOSED / 10 OPEN** and the mask register
**8 CLOSED / 24 OPEN**. All nine original squares, 36 corners, 36 physical
pairs, five center cones and exact marked conditions remain required by the
eventual complete B16a proof. No Lean, Lake or CI was run.
''')
    files={p.name:dict(sha256=sha(p),bytes=p.stat().st_size)for p in sorted(D.iterdir())if p.is_file()}
    dump(R/(REL+'_manifest.json'),dict(schema='B16a_replayable_cover_availability_publication_v1',
        package=REL,files=files,original_id=a['original_id'],original_status='OPEN',
        currently_replayable_quarters=11,pending_quarters=5,whole_original_excluded=False,
        new_original_cells=0,new_masks=0,register_sha256=register_sha,
        self_contained_arithmetic_proof=False,arithmetic_repeated=False,lean_lake_ci_run=False))
    p=R/'research/nine/PROGRESS.md';text=p.read_text()
    old='Fourteen of sixteen I rectangles are excluded; only I21 and I22 remain OPEN.\nB16a itself and all fixed original/mask/positional/roadmap ledgers are unchanged.'
    assert text.count(old)==1
    new='''The historical publication reported fourteen excluded I rectangles. The
[current recovery inventory](computer_assisted/a2_00100_b16a_replayable_cover_availability_v1/README.md)
has eleven replayable exclusions: six published complete quarters and five
freshly reconstructed quarters. I20, I21, I22, I31 and I33 remain pending;
the earlier complete certificates for I20/I31/I33 were not recovered.
This is an evidence-availability distinction, with no later mathematical
invalidation asserted. The old publication bytes remain unchanged. B16a
and all fixed original/mask/positional/roadmap ledgers remain unchanged.'''
    p.write_text(text.replace(old,new,1))
    p=R/'research/nine/HANDOFF_A2_FIXED_CLOSURE.md';text=p.read_text();marker='## Read first\n\n';assert text.count(marker)==1
    text=text.replace(marker,marker+'''The [B16a replayable-cover checkpoint](computer_assisted/a2_00100_b16a_replayable_cover_availability_v1/README.md)
preserves eleven currently reproducible I-quarter exclusions and explicitly
queues I20/I21/I22/I31/I33. It distinguishes the historical fourteen-quarter
claim from recovered evidence, preserves all available earlier proofs and
the five new terminal records, and changes no original or mask status.

''',1);p.write_text(text)
    assert sha(register)==register_sha
    print(json.dumps(dict(status=report['status'],package=REL,files=len(files),archive_bytes=1034956,
        new_original_cells=0,new_masks=0)))

if __name__=='__main__':main()
