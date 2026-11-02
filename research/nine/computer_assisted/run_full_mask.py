#!/usr/bin/env python3
"""Reproduce the raw full-mask solver attempt; UNKNOWN is not an exclusion."""
from emit_fixed_mask import emit
from z3_ctypes import run
from pathlib import Path
import time

if __name__ == '__main__':
    body=emit('000/01','strict',9)
    spec='(set-option :timeout 20000)\n'+body+'\n(get-info :reason-unknown)\n(get-info :all-statistics)\n'
    Path(__file__).with_name('full_mask_00001.smt2').write_text(spec)
    start=time.monotonic()
    out=run(spec)
    Path(__file__).with_name('full_mask_raw_result.txt').write_text(out)
    print('elapsed_seconds',time.monotonic()-start)
    print(out)
