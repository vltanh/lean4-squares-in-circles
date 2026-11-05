"""Fresh independent archived C887 original-prefix replay.

Run in a separate Python process so the archive's frozen module bindings
cannot interact with the C887-family row adapter used for new records.
"""
from pathlib import Path
from fractions import Fraction as F
import sys,json,hashlib,argparse,time
HERE=Path(__file__).resolve().parent
PACKET=HERE/'c887_whole_eight_checkpoint_package'
MANIFEST_SHA='d95bb23022ab5ba457c88139490e5147045069ce58bf3fef83c5ad1a3602c9c0'
PREFIX_SHA='9a5c4af1e23964ee661e4e1ae427265a29303b2a6f6bd5a65c5ece14177040a3'
TARGET='negative-887236b78100baf3'
ROOT_PATH=[['angle',3,0],['angle_cut',[0,'0'],1],['alternate_four_escape',[1,7],[1]]]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def boxes(v):return [[str(a),str(b)]for a,b in v]
def diff(v):return [dict(pair=list(k),intervals=boxes(v[k]))for k in sorted(v)]
def main(output):
 assert __debug__;started=time.monotonic();mp=PACKET/'SHA256_MANIFEST.json';assert sha(mp)==MANIFEST_SHA
 manifest=json.loads(mp.read_text());assert manifest['schema']=='C887_sharp_foundation_frozen_inputs_v1'
 inputs={str(mp):MANIFEST_SHA}
 for name,digest in manifest['files'].items():
  assert sha(PACKET/name)==digest;inputs[str(PACKET/name)]=digest
 sys.path.insert(0,str(PACKET))
 import verify_cd_triple_energy_recursive_bounds as RULE
 checker=RULE.Checker(PACKET,PACKET/'ancestry')
 source=PACKET/'ancestry/cd_family/diagonal_results'/f'{TARGET}.json';assert sha(source)==PREFIX_SHA
 audit,state,diagonal=checker.D.replay(source)
 assert audit['status']=='PASS_CERTIFIED_PARENT_STATE_OPEN'
 assert state['id']==TARGET and state['path']==ROOT_PATH
 assert checker.K.V.Q==F(1105,256)and checker.K.V.EDGES==((0,1,0),(1,2,0),(2,3,1),(4,5,0),(5,6,0))
 view=dict(id=TARGET,path=ROOT_PATH,angles=boxes(state['angles']),positions=boxes(state['positions']),scalar=boxes(state['scalar']),differences=diff(state['differences']),diagonal=diff(diagonal))
 saved=json.loads(source.read_text());assert saved['schema']=='correlated_diagonal_whole_parent_v1'and saved['rounds']==[]
 assert dict(saved['final'],id=saved['id'],path=saved['path'])==view
 for path,digest in inputs.items():assert sha(path)==digest
 assert not any(n in sys.modules for n in('numpy','scipy','highspy','c_center_runtime','physical_sat_diagonal_engine','ac_objective_unit_four_corner_runtime'))
 report=dict(status='PASS_FRESH_C887_ORIGINAL_PREFIX',original_id=TARGET,original_path=ROOT_PATH,original_mask='001/00',squared_radius='1105/256',ancestor=audit,certified_original_state=view,input_sha256=inputs,checker_sha256=sha(__file__),no_selected_sat_proxy_or_angle_child=True,new_original_cells=0,new_masks=0,seconds=time.monotonic()-started)
 output=Path(output);output.write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps({k:report[k]for k in('status','original_id','seconds')}),flush=True)
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('output',type=Path);a=ap.parse_args();main(a.output)
