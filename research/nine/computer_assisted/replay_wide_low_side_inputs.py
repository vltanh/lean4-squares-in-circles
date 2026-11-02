#!/usr/bin/env python3
"""Fresh exact executions of the frozen wide-main low-side input covers.

This independent-agent execution raises the accepted integer kernel to
80 fractional bits. It imports only the frozen acceptance evaluators,
never either floating producer. Physical/code review is recorded beside
the resulting report; this is not a wholly independent formula program.
"""
from pathlib import Path
import hashlib
import importlib
import json
import sys
import time

HERE = Path(__file__).resolve().parent
WORK = HERE.parents[1]
SOURCE = WORK / 'agent_whole_mask/weak_middle_low_side'
sys.path.insert(0, str(SOURCE))
height = importlib.import_module('verify_upper_central_height')
floor = importlib.import_module('verify_low_side_floor')
helper = importlib.import_module('verify_wide_central_pair')
kernel = importlib.import_module('verify_joint_five_dyadic')
kernel.BITS = 80
kernel.SCALE = 1 << kernel.BITS
helper.SCALE = height.SCALE = floor.SCALE = kernel.SCALE

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    results = []
    for name, module, cert_name in (
        ('upper_central_height', height, 'upper_central_height_candidate.json'),
        ('low_side_floor', floor, 'low_side_floor_candidate.json'),
    ):
        cert = SOURCE / cert_name
        data = json.loads(cert.read_bytes())
        start = time.monotonic()
        result = module.verify(data)
        result.update(
            arithmetic='80-bit directed integer intervals, exact rational tree endpoints; precision raised in this process only',
            execution_seconds=time.monotonic()-start,
            certificate_sha256=sha(cert),
            evaluator_sha256=sha(Path(module.__file__)),
            clearance_helper_sha256=sha(Path(helper.__file__)),
            kernel_source_sha256=sha(Path(kernel.__file__)),
            damaged_controls=module.controls(data),
        )
        results.append({'gate': name, **result})
        print(json.dumps({'gate':name, 'status':result['status'], 'leaves':result['leaves'], 'seconds':result['execution_seconds']}), flush=True)
    report = {
        'reviewer':'root_certificates, independent agent; not human or kernel review',
        'method':'Fresh 80-bit exact execution of the frozen acceptance formulas, combined with separate physical and code review',
        'driver_sha256':sha(Path(__file__)),
        'results':results,
    }
    (HERE/'wide_low_side_inputs_independent_replays.json').write_text(json.dumps(report, indent=2)+'\n')

if __name__ == '__main__':
    main()
