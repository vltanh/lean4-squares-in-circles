"""Second arithmetic implementation for the central singleton-floor cover.

Shares the structural checker and its reviewed physical formulas, while
using the independently implemented Fraction interval/derivative kernel.
"""
import hashlib,json,sys
from pathlib import Path

HERE=Path(__file__).resolve().parent
CHECKER_DIR=HERE if(HERE/'verify_central_singleton_floor.py').exists()else HERE.parent/'agent_whole_mask'
sys.path.insert(0,str(CHECKER_DIR))
import verify_central_singleton_floor as checker
import verify_joint_five_fraction as arithmetic
checker.ar=arithmetic

def upper(box):
    full=checker.evaluate(box)
    mid=[(box[2*j]+box[2*j+1])/2 for j in range(4)]
    centered=checker.evaluate(tuple(v for m in mid for v in(m,m))).x
    for j,m in enumerate(mid):
        centered+=full.der[j]*arithmetic.I(box[2*j]-m,box[2*j+1]-m)
    return min(full.x.hi,centered.hi)

checker.upper=upper

if __name__=='__main__':
    path=Path(sys.argv[1]);raw=path.read_bytes()
    report=checker.verify(json.loads(raw),True)
    report.update(proof_status='independent_fraction_arithmetic_replay_passed',
        certificate_sha256=hashlib.sha256(raw).hexdigest(),
        structural_checker_sha256=hashlib.sha256(Path(checker.__file__).read_bytes()).hexdigest(),
        fraction_wrapper_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        arithmetic_sha256=hashlib.sha256(Path(arithmetic.__file__).read_bytes()).hexdigest())
    (HERE/(path.stem+'_fraction_replay.json')).write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report),flush=True)
