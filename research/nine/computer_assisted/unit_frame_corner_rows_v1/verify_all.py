#!/usr/bin/env python3
"""Relocated standard-library replay of both unit-corner arithmetic suites."""
import argparse,hashlib,json,shutil,subprocess,sys,tempfile
from pathlib import Path
if not __debug__:
    raise RuntimeError('Exact replay requires assertions')
ROOT=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path);args=parser.parse_args()
    binding=json.loads((ROOT/'PREMISE_BINDINGS.json').read_text())
    for name,digest in binding['immutable_inputs'].items():
        assert Path(name).name==name and sha(ROOT/name)==digest,name
    with tempfile.TemporaryDirectory(prefix='unit_corner_exact_')as temporary:
        folder=Path(temporary)
        for name in binding['immutable_inputs']:
            if name.endswith('.py')or name=='UNIT_FRAME_CORNER_HAND_PROOF.md':shutil.copy2(ROOT/name,folder/name)
        for script in('check_physical_unit_corner_rows.py','review_physical_unit_corner_b.py'):
            subprocess.run([sys.executable,'-B','-S',script],cwd=folder,check=True,capture_output=True,text=True)
        primary=json.loads((folder/'EXACT_CONTROLS.json').read_text())
        independent=json.loads((folder/'UNIT_FRAME_CORNER_B_REVIEW.json').read_text())
        assert primary['status']=='PASS_EXACT_UNIT_FRAME_CORNER_ROWS'
        for key,expected in dict(independently_rebuilt_rows=864,exact_physical_expansions=12096,
                contained_corner_evaluations=10044,zero_width_interval_rows=432,
                damaged_literals_rejected=1728,nonunit_relaxation_control_violation='4623/160000').items():
            assert primary[key]==expected
        assert independent['status']=='PASS_INDEPENDENT_B_UNIT_CORNER_REVIEW'
        assert independent['exact_literal_and_residual_checks']==independent['physical_contained_corner_checks']==720
        for report in(primary,independent):
            for path,digest in report.pop('source_sha256').items():assert binding['immutable_inputs'][Path(path).name]==digest
    result=dict(status='PASS_PORTABLE_PHYSICAL_UNIT_CORNER_ROWS',
        premise_bindings_sha256=sha(ROOT/'PREMISE_BINDINGS.json'),immutable_inputs_checked=len(binding['immutable_inputs']),
        primary=primary,independent_review=independent,new_original_cells=0,new_masks=0,
        numerical_producer_imported=False,lean_lake_ci_run=False)
    rendered=json.dumps(result,indent=2)+'\n'
    if args.output:args.output.write_text(rendered)
    print(rendered,end='')
if __name__=='__main__':main()
