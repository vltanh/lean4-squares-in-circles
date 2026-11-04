#!/usr/bin/env python3
"""Independent source/table audit of the already replayed Dc71 checkpoint."""
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from pathlib import Path
import json
import re

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
PACKET=ROOT/'dc71_i16_six_round_checkpoint_package'
OUT=HERE/'DC71_I16_CHECKPOINT_SOURCE_AND_HAND_TABLE_REVIEW.json'
PIN={'SHA256_MANIFEST.json':'f8eebf96fae3077ba0c20c1ed430bebdc520838669e4a21cf0e6f541eb85f421',
     'CHECKPOINT_PORTABLE_REPLAY.json':'4343240ca9bc75fb57af6c761e97f721ac154bc343e7cbdcc4b260a087ca2c35',
     'verify_checkpoint.py':'20edb7c1338059cb583ef7ad45daa3c9f033f7da0d2eed414e77f74520d5b45e',
     'DC71_I16_HAND_CHECKPOINT.md':'fa47080c01be89bbdbd4106ea3924f767aa1ee4451813d39698a86d26eddcf17',
     'DC71_SIX_ROUND_RECORDS.json':'de7d09fb73747cea493b9bf3d18fd508f25f878238416c67f26747a27dcbb423'}

def main():
    assert __debug__ and not OUT.exists()
    inputs={}
    def bind(path,expected=None):
        path=Path(path).resolve();raw=path.read_bytes();actual=sha256(raw).hexdigest()
        if expected is not None:assert actual==expected,(str(path),actual,expected)
        assert path not in inputs or inputs[path]==actual
        inputs[path]=actual;return raw
    for name,h in PIN.items():bind(PACKET/name,h)
    manifest=json.loads((PACKET/'SHA256_MANIFEST.json').read_text())
    for name,h in manifest['files'].items():
        path=(PACKET/name).resolve();assert path.is_relative_to(PACKET);bind(path,h)
    assert len(manifest['files'])==236
    r=json.loads((PACKET/'CHECKPOINT_PORTABLE_REPLAY.json').read_text())
    index=json.loads((PACKET/'DC71_SIX_ROUND_RECORDS.json').read_text())
    assert r['status']=='PASS_COMPLETE_I16_DECLARATION_WITH_SEVEN_OPEN_RECTANGLES'
    original='positive-c71dc2feef1abb0b'
    caller=[['angle',3,1],['angle_cut',[0,'0'],1],['alternate_four_escape',[1,7],[2]]]
    prefix='3d5c6def24cd920103c2a26b81d4f898e135cda0b125a2eea87a8880fee840fa'
    assert r['id']==index['id']==original
    assert r['original_parent_path']==index['original_parent_path']==caller
    assert r['original_prefix_sha256']==index['original_prefix_sha256']==prefix
    original_data=json.loads(bind(PACKET/'ancestry/cd_family/diagonal_results'/(original+'.json'),prefix))
    assert original_data['rounds']==[] and original_data['path']==caller
    assert original_data['prior']['sha256']=='00ba91a487f8098f00e6804344bdc5f724ef6e0bd7a5ef3a7d94767fce341942'
    full_intervals=[tuple(map(F,pair)) for pair in original_data['final']['positions'][16:18]]
    def rectangle(tile):
        return [[str(lo+(hi-lo)*F(k,4)),str(lo+(hi-lo)*F(k+1,4))]
                for k,(lo,hi) in zip(tile,full_intervals)]
    records={tuple(t['tile']):t for t in r['tile_reports']}
    assert len(records)==len(index['records'])==14
    for entry in index['records']:
        raw=json.loads(bind(PACKET/entry['certificate'],entry['sha256']))
        tile=tuple(entry['tile']);t=records[tile]
        assert t['certificate_sha256']==entry['sha256']
        assert raw['id']==t['id']==original and raw['path']==t['original_parent_path']==caller
        assert t['original_prefix_replay']['certificate_sha256']==prefix
        assert raw['prior']['sha256']==prefix and raw['prior']['tile']==entry['tile']
        assert raw['prior']['rectangle']==t['rectangle']==rectangle(tile)
        assert raw['prior']['h_rectangle'] is t['h_rectangle'] is None
        assert raw['prior']['closed_cover_parts']==t['closed_cover_parts']==[4,4]
        assert t['unfinished_rounds_admitted'] is False
        assert t['unsupported_rules_accepted'] is False
        assert t['new_original_cells']==t['new_masks']==0
    direct=r['direct_interval_report']
    assert direct['id']==original and direct['original_parent_path']==caller
    assert direct['original_prefix_sha256']==prefix
    direct_map={tuple(t['tile']):t for t in direct['tile_reports']}
    assert set(direct_map)=={(0,1),(0,2)}
    for tile,t in direct_map.items():
        assert t['rectangle']==rectangle(tile) and t['closed_cover_parts']==[4,4]
        assert t['closed_faces_retained'] is True and t['status']=='PASS_COMPLETE_PHYSICAL_TILE'
        for w in t['witnesses']:
            a,b=map(F,w['intersection'])
            assert a-b==F(w['strict_gap'])>0
    assert not set(records)&set(direct_map)
    assert set(records)|set(direct_map)==set(product(range(4),repeat=2))
    opened={tile for tile,t in records.items() if t['status']=='PASS_CERTIFIED_TILE_STATE_OPEN'}
    closed={tile for tile,t in records.items() if t['status']=='PASS_COMPLETE_PHYSICAL_TILE'}|set(direct_map)
    assert opened=={(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)} and len(closed)==9
    assert all(records[t]['bound_rounds']==6 for t in opened)
    assert set(map(tuple,r['open_I_tiles']))==opened and set(map(tuple,r['closed_I_tiles']))==closed
    assert sum(t['bound_rounds']for t in records.values())==r['bound_rounds']==49
    assert sum(t['bound_deductions']for t in records.values())==r['bound_deductions']==6467
    assert sum(t['printed_rows_checked']for t in records.values())==r['printed_rows_checked']==10479
    assert sum(t['terminal_rows']for t in records.values())==r['terminal_rows']==82
    assert sum(t['printed_rows_checked']-t['terminal_rows']for t in records.values())==10397
    for axis in range(2):
        intervals=[tuple(map(F,rectangle((k,0) if axis==0 else (0,k))[axis]))for k in range(4)]
        assert intervals[0][0]==full_intervals[axis][0] and intervals[-1][1]==full_intervals[axis][1]
        assert all(intervals[k][1]==intervals[k+1][0]for k in range(3))
    hand=(PACKET/'DC71_I16_HAND_CHECKPOINT.md').read_text()
    rows=[]
    for line in hand.splitlines():
        m=re.match(r'^\| `(\d),(\d)` \| (\d+) \| (\d+) \| (.*?) \|$',line)
        if m:
            i,j,rounds,deductions,status=m.groups();tile=(int(i),int(j));rows.append(tile)
            if tile in direct_map:assert (int(rounds),int(deductions))==(0,0)
            else:assert (int(rounds),int(deductions))==(records[tile]['bound_rounds'],records[tile]['bound_deductions'])
            assert status.startswith('OPEN') == (tile in opened)
    assert rows==list(product(range(4),repeat=2))
    assert r['whole_original_closed'] is False and r['whole_original_cover_checked'] is False
    assert r['new_original_cells']==r['new_masks']==0
    bind(__file__)
    for path,h in inputs.items():assert sha256(path.read_bytes()).hexdigest()==h
    out=dict(status='PASS_SOURCE_AND_COMPLETE_TABLE_WITH_DOCUMENTATION_TERMINOLOGY_NOTE',
        scope='Source/attachment/hand-table review of accepted exact replay; no bound arithmetic repeated',
        original_id=original,original_parent_path=caller,whole_prefix_sha256=prefix,
        closed_I_rectangles=9,open_six_round_I_rectangles=7,declared_I_rectangles=16,
        complete_equal_closed_quarter_union_checked=True,all_shared_boundary_faces_retained=True,
        bound_rounds=49,exact_deductions=6467,total_printed_row_occurrences=10479,
        induction_row_occurrences=10397,terminal_row_occurrences=82,
        hand_table_entries_checked=16,independent_direct_strict_gap_checks=3,
        source_review_findings=[
          'The unchanged accepted recursive checker computes every I rectangle from the same whole prefix with exact quarters.',
          'The wrapper replays all fourteen distinct records, joins exactly the two independently checked direct exclusions, and asserts every one of the sixteen indices.',
          'Whole original identity, literal path, no H cut, common prefix and exact seven OPEN indices are checked after replay.',
          'All manifest bytes and project-local module origins are checked before final output; original/mask credit remains zero.'
        ],
        documentation_note='The frozen hand calls 10479 premise rows and separately mentions 82 terminal rows. The accepted report/checker count 10479 TOTAL printed rows, including those 82; induction rows are10397. Root acknowledged and will clarify the live documentation without altering frozen mathematical sources or rerunning arithmetic.',
        frozen_wrapper_sha256=PIN['verify_checkpoint.py'],frozen_hand_sha256=PIN['DC71_I16_HAND_CHECKPOINT.md'],
        accepted_replay_sha256=PIN['CHECKPOINT_PORTABLE_REPLAY.json'],source_manifest_sha256=PIN['SHA256_MANIFEST.json'],
        source_sha256={str(p):h for p,h in sorted(inputs.items())},
        evaluator_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
        arithmetic_replay_repeated=False,new_original_cells=0,new_masks=0,lean_lake_ci_run=False)
    OUT.write_text(json.dumps(out,indent=2)+'\n')
    print(out['status']);print('REVIEW_SHA256',sha256(OUT.read_bytes()).hexdigest())
    print('EVALUATOR_SHA256',out['evaluator_sha256'])

if __name__=='__main__':main()
