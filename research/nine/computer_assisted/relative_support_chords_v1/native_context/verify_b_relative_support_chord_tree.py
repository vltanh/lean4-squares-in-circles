"""Independent original B tree replay with relative-support chord literals."""
from pathlib import Path
from fractions import Fraction as F
from copy import deepcopy
import argparse, json, sys, time
import verify_b_center_difference_tree as BASE

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE/'relative_support_chords'))
import independent_relative_support_chords as CHORD
CORE, TREE, WHOLE = BASE.CORE, BASE.TREE, BASE.WHOLE

class Adapter(BASE.Adapter):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.relative_support_chord_rows = 0
        for p in (__file__, CHORD.__file__,
                  HERE/'relative_support_chords/RELATIVE_SUPPORT_CHORD_HAND_PROOF.md',
                  HERE/'relative_support_chords/OWNER_FREE_RELATIVE_SUPPORT_HAND_PROOF.md'):
            self.retain(p)

    def rebuild(self, state, printed):
        ordinary = [r for r in printed if not r['name'].startswith(CHORD.PREFIX)]
        rows, bounds, physical = super().rebuild(state, ordinary)
        for r in printed:
            if not r['name'].startswith(CHORD.PREFIX):
                continue
            literal = tuple((k, F(v)) for k, v in r['coefficients']), F(r['rhs']), r['name']
            CHORD.verify_literal(literal, physical['scalar'], physical['differences'])
            assert r['index'] not in rows
            rows[r['index']] = literal
            self.relative_support_chord_rows += 1
        return rows, bounds, physical

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('manifest', type=Path)
    ap.add_argument('report', type=Path)
    ap.add_argument('--packet', type=Path, required=True)
    a = ap.parse_args()
    started = time.monotonic()
    adapter = Adapter(a.packet)
    report = TREE.verify_tree(a.manifest, adapter)
    parent = json.loads(a.manifest.read_text())['parent']
    whole = WHOLE.verify(adapter.retain(parent['path'], parent['sha256']), adapter)
    report['entire_registered_original_domain_retained'] = whole
    if report['complete'] and whole:
        report.update(status='PASS_COMPLETE_ORIGINAL_PHYSICAL_TREE', whole_original_proved=True)
    for mod in list(sys.modules.values()):
        raw = getattr(mod, '__file__', None)
        if raw:
            p = Path(raw).resolve()
            if p.suffix == '.py' and p.is_relative_to(HERE):
                adapter.retain(p)
    adapter.recheck()
    assert not any(x in sys.modules for x in ('numpy', 'scipy', 'highspy',
        'physical_relative_support_chords', 'physical_incircle_chords',
        'physical_rotating_frame_center_rows', 'physical_general_center_cone_rows'))
    report.update(source_sha256=adapter.files, ancestry_reports=deepcopy(adapter.reports),
        universal_center_disk_rows_checked=adapter.center_rows,
        incircle_chord_rows_checked=adapter.chord_rows,
        rotating_center_cone_rows_checked=adapter.cone_rows,
        general_center_cone_rows_checked=adapter.general_cone_rows,
        relative_support_chord_rows_checked=adapter.relative_support_chord_rows,
        seconds=time.monotonic()-started)
    a.report.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k: report[k] for k in ('status', 'relative_support_chord_rows_checked', 'seconds')}), flush=True)

if __name__ == '__main__':
    main()
