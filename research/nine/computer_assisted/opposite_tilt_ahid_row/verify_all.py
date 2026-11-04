#!/usr/bin/env python3
"""Hash-bound portable exact replay of the conditional opposite-tilt row proof."""
from pathlib import Path
import hashlib,json
import verify_chiral_cover as table
import review_opposite_tilt_guard as guard_review
import check_chiral_negative_controls as damage

if not __debug__:
    raise RuntimeError('Exact portable replay requires assertions; Python -O is not supported')

ROOT=Path(__file__).resolve().parent


def check_inputs(manifest):
    for name,expected in manifest['immutable_inputs'].items():
        rel=Path(name)
        assert not rel.is_absolute()and'..'not in rel.parts
        path=ROOT/rel
        assert path.is_file(),('missing input',name)
        assert hashlib.sha256(path.read_bytes()).hexdigest()==expected,('changed input',name)


def main():
    manifest=json.loads((ROOT/'MANIFEST.json').read_text())
    assert manifest['schema']=='opposite_tilt_ahid_row_packet_v1'
    check_inputs(manifest)
    for module,name in((table,'verify_chiral_cover.py'),(guard_review,'review_opposite_tilt_guard.py'),(guard_review.candidate,'opposite_tilt_four_row_guard.py'),(damage,'check_chiral_negative_controls.py')):
        assert Path(module.__file__).resolve()==ROOT/name,('unexpected loaded source',name)
    scalar=table.run(ROOT/'cover')
    guard=guard_review.run()
    controls=damage.run(ROOT)
    assert scalar['complete_domains']==80 and scalar['leaves']==1405 and scalar['coefficient_checks']==878125 and scalar['frontier']==0
    assert guard['checks']==529 and guard['complete_complement_domains']==11
    assert len(controls['controls'])==8
    check_inputs(manifest)
    report={'status':'PASS_PORTABLE_COMPLETE_OPPOSITE_TILT_AHID_ROW',
            'scope':'Complete conditional hand/table theorem; original caller guards and all complementary domains remain application obligations',
            'table':scalar,'guard_algebra':guard,'negative_controls':controls,
            'immutable_inputs_checked':len(manifest['immutable_inputs']),
            'new_original_cells_closed':0,'new_masks_closed':0}
    (ROOT/'FRESH_REPLAY.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items()if k not in('table','guard_algebra','negative_controls')},indent=2))

if __name__=='__main__':main()
