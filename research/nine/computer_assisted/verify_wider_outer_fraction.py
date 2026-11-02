"""Second exact arithmetic implementation for the widened outer tables.

Shares structural validation and physical row formulas with the independent
checker; uses the separately implemented Fraction/radical interval kernel.
Imports neither producer nor floating proposal code.
"""
import hashlib,json,sys
from pathlib import Path

HERE=Path(__file__).resolve().parent
CHECKER_DIR=HERE if (HERE/'verify_wider_outer.py').exists() else HERE.parent/'agent_whole_mask'
sys.path.insert(0,str(CHECKER_DIR))
import verify_wider_outer as checker
import verify_joint_five_fraction as fractional

checker.ar=fractional

def upper(box,row,owner,chart):
    whole=checker.evaluate(box,row,owner,chart)
    midpoints=[(box[0]+box[1])/2,(box[2]+box[3])/2]
    point=tuple(v for m in midpoints for v in (m,m))
    centered=checker.evaluate(point,row,owner,chart).x
    for j,m in enumerate(midpoints):
        centered+=whole.der[j]*fractional.I(box[2*j]-m,box[2*j+1]-m)
    return min(whole.x.hi,centered.hi)

checker.upper=upper

if __name__=='__main__':
    path=Path(sys.argv[1]);raw=path.read_bytes()
    report=checker.verify(json.loads(raw),True)
    report.update(proof_status='independent_fraction_arithmetic_replay_passed',
                  certificate_sha256=hashlib.sha256(raw).hexdigest(),
                  structural_checker_sha256=hashlib.sha256(Path(checker.__file__).read_bytes()).hexdigest(),
                  fraction_wrapper_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  arithmetic_sha256=hashlib.sha256(Path(fractional.__file__).read_bytes()).hexdigest())
    destination=HERE/(path.stem+'_fraction_replay.json')
    destination.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report),flush=True)
