#!/usr/bin/env python3
"""Independent universal-center literals over full B physical cover replay."""
from pathlib import Path
from fractions import Fraction as F
from copy import deepcopy
import argparse,json,sys,time
import verify_b_four_corner_trees as BASE
import independent_b_lazy_tree_replay as TREE
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'universal_center_disk'))
import independent_physical_center_disk_rows as CENTER
CORE=BASE.CORE

class Adapter(BASE.Adapter):
    def __init__(self,packet,cap_proof_dir=None,sharp_package=None):
        super().__init__(packet,cap_proof_dir or HERE/'cap_proof',sharp_package)
        self.center_rows=0
        self.retain(__file__);self.retain(CENTER.__file__)
        self.retain(HERE/'universal_center_disk/UNIVERSAL_CENTER_DISK_HAND_PROOF.md')
        assert self.K.V.Q==F(1105,256)
    def rebuild(self,state,printed):
        ordinary=[r for r in printed if not r['name'].startswith(CENTER.PREFIX)]
        rows,bounds,propagated=super().rebuild(state,ordinary)
        for r in printed:
            if not r['name'].startswith(CENTER.PREFIX):continue
            literal=(tuple((k,F(v))for k,v in r['coefficients']),F(r['rhs']),r['name'])
            CENTER.verify_literal(literal)
            assert r['index']not in rows
            rows[r['index']]=literal;self.center_rows+=1
        return rows,bounds,propagated

def main():
    ap=argparse.ArgumentParser();ap.add_argument('input',type=Path);ap.add_argument('report',type=Path)
    ap.add_argument('--packet',type=Path,required=True);ap.add_argument('--cap-proof-dir',type=Path);ap.add_argument('--sharp-package',type=Path)
    ap.add_argument('--record',action='store_true')
    a=ap.parse_args();started=time.monotonic();adapter=Adapter(a.packet,a.cap_proof_dir,a.sharp_package)
    if a.record:report,state=adapter.replay(a.input)
    else:
        report=TREE.verify_tree(a.input,adapter);p=json.loads(a.input.read_text())['parent']
        whole=BASE.BASE.WHOLE.verify(adapter.retain(p['path'],p['sha256']),adapter)
        report['entire_registered_original_domain_retained']=whole
        if report['complete']and whole:report.update(status='PASS_COMPLETE_ORIGINAL_PHYSICAL_TREE',whole_original_proved=True)
    for module in list(sys.modules.values()):
        raw=getattr(module,'__file__',None)
        if raw:
            p=Path(raw).resolve()
            if p.suffix=='.py'and p.is_relative_to(HERE):adapter.retain(p)
    assert not any('runtime'in name and name.startswith('b_')for name in sys.modules)
    adapter.recheck();BASE.BASE.SHARP.verify_binding(adapter.sharp_package)
    report=deepcopy(report);report.update(source_sha256=adapter.files,ancestry_reports=deepcopy(adapter.reports),
        seconds=time.monotonic()-started,universal_center_disk_rows_checked=adapter.center_rows,
        four_product_unit_corner_rows_checked=adapter.four_corner_rows,original_corner_disk_rows_checked=adapter.corner_rows,
        physical_pair_frame_square_rows_checked=adapter.frame_square_rows,physical_projection_square_rows_checked=adapter.projection_square_rows,
        oriented_cap_rows_checked=adapter.cap_rows,full_angle_terminal_occurrences_checked=adapter.full_angle_occurrences,
        full_angle_AB_extra_terminal_occurrences_checked=adapter.extra_full_occurrences,opposite_ABID_terminal_occurrences_checked=adapter.opposite_abid_occurrences)
    a.report.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:report[k]for k in('status','universal_center_disk_rows_checked','seconds')}),flush=True)
if __name__=='__main__':main()
