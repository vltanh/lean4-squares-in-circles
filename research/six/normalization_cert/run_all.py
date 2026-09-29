"""Reproduce every supplied normalization predicate and preserve a local log.

Default backend: python-flint/Arb. For an independent stdlib-only execution,
run replay_rational.py instead. Neither entry point invokes GitHub or Lean.
A sampled minimum is diagnostic only: strict interval comparisons decide
acceptance. Direct certificates require no unresolved boxes.
"""
import argparse
import contextlib
import hashlib
import io
import math
import platform
import sys
import time
from pathlib import Path

import flint
from ia import *
from bnb import bnb

LOG = []
DIRECT = []


def log(text=''):
    print(text,flush=True)
    LOG.append(text)


def run_bnb(title,root,ev,weights,**kw):
    t0 = time.monotonic()
    with contextlib.redirect_stdout(io.StringIO()):
        stats,unresolved,n = bnb(root,ev,weights,verbose=False,name=title,**kw)
    ok = not unresolved
    DIRECT.append((title,ok,n,len(unresolved)))
    reasons = ', '.join(f'{k}: {v}' for k,v in sorted(stats.items()))
    log(f'| {title} | {"CERTIFIED" if ok else "FAILED"} | {n} | '
        f'{len(unresolved)} | {time.monotonic()-t0:.2f}s | {reasons} |')
    return ok


def main(log_path='LOCAL_CERT_LOG.md'):
    import cert_main as M
    import cert_main2 as M2
    import cert_cone as K
    import cert_wd as WD
    import cert_scalars as S

    LOG.clear()
    DIRECT.clear()
    backend = getattr(flint,'__certificate_backend__',
                      f'python-flint {getattr(flint,"__version__","unknown")}, Arb, ctx.prec={ctx.prec}')
    log('# Normalization certificate execution log')
    log(f'Python: {platform.python_version()}; backend: {backend}.')
    log('This log records local execution, not Lean kernel acceptance or a downstream A2 audit.')
    log('Predicate inputs: Q0=142559/50000; genuine Seven label; specified central domains.')
    log('Lemma A uses the hand CE/OWN exclusions for cx>c0; the face cx=c0 is NOT excluded.')
    log('Each source file used in this execution is identified below by SHA-256.')
    log('')
    log('## Direct certificates')
    log('| certificate | result | boxes | unresolved | elapsed | closure reasons |')
    log('|---|---|---:|---:|---|---|')
    root = [(-3.1416,3.1416),(0.5,1.2),(-1.2,1.2)]
    ok = run_bnb('L1 chart bounds, axial label, no SEC',root,M.L1_eval,[1,1,1])
    ok &= run_bnb('L2 five pins, margin 1/100',root,M.L2_eval_factory(arb(1)/100),[1,1,1])
    for k in 'ENWDS':
        ok &= run_bnb('L3-'+k+' windows and separators',M.root_around(M.WINDOWS[k][0]),
                      M.L3_eval_factory(k),[1,1,1])
    for (k,s),(cen,l,h) in M2.SEP_WINDOWS.items():
        r = [(cen-3.1416,cen+3.1416),(0.5,1.2),(-1.2,1.2)]
        ok &= run_bnb(f'L3-prime {k}/{s}',r,M.sep_window_factory(k,s,l,h),[1,1,1])
    ok &= run_bnb('L6 cap piercing, margin 1/30',
                  [(M2.H_LO,M2.H_HI),(-0.7854,0.7854),(-1.3,1.3),(-1.3,1.3)],
                  M2.L6_eval_factory(arb(1)/30),[1,1,1,1])
    c0hi = math.nextafter(float(C0.upper()),math.inf)
    ok &= run_bnb('L7 own moving pin, margin 1/20',root+[(0.0,c0hi)],
                  M2.L7_eval_factory(arb(1)/20),[1,1,1,1])
    rwd = [(math.pi-2/3-1e-9,math.pi+5/8+1e-9),(0.884,1.116),(-0.469,0.469),
           (5*math.pi/4-15/14-1e-9,5*math.pi/4+15/14+1e-9),(0.884,1.116),(-0.469,0.469)]
    ok &= run_bnb('W/D order, all four pair axes',rwd,WD.ev,[1,2,1,1,2,1],max_boxes=30_000_000)
    cx,cy = C0.union(arb(1)/2),arb(0).union(C0)
    ok &= run_bnb('A1 forbidden arc (-99/100,61/50), cx>c0',K.ROOT,
                  K.cone_eval_factory(cx,cy,arb(99)/100,arb(61)/50),[1,1,1])
    low = math.nextafter(float(C0.lower()),-math.inf)
    edges = [low+(0.5-low)*i/8 for i in range(9)]
    edges[-1] = 0.5
    if max(edges[i+1]-edges[i] for i in range(8))>=0.1:
        raise AssertionError('staircase exceeds hand-lemma diagonal tolerance')
    na,nun,regions = 0,0,0
    t0 = time.monotonic()
    for i in range(8):
        for j in range(i+1):
            ev = K.cone_eval_factory(iv(edges[i],edges[i+1]),iv(edges[j],edges[j+1]),
                                    arb(27)/50,arb(39)/25)
            stats,un,n = bnb(K.ROOT,ev,[1,1,1],verbose=False)
            na += n
            nun += len(un)
            regions += 1
    if regions!=36: raise AssertionError('A2 coverage inventory changed')
    ok &= nun==0
    DIRECT.append(('A2 forbidden arc, 36 central boxes',nun==0,na,nun))
    log(f'| A2 forbidden arc (-27/50,39/25), 36 central boxes, cx>c0 | '
        f'{"CERTIFIED" if nun==0 else "FAILED"} | {na} | {nun} | {time.monotonic()-t0:.2f}s | |')
    if len(DIRECT)!=23: raise AssertionError(('direct inventory',len(DIRECT)))
    log('')
    log('## Scalar obligations')
    with contextlib.redirect_stdout(io.StringIO()) as captured:
        results = S.main()
    log('| id | interval result | sampled diagnostic minimum | tested intervals | statement |')
    log('|---|---|---:|---:|---|')
    for name,passed,estimate,n,note in results:
        log(f'| {name} | {"PASS" if passed else "FAIL"} | {estimate:.9g} | {n} | {note} |')
        ok &= bool(passed)
    if len(results)!=78 or len(S.SANITY)!=4:
        raise AssertionError(('scalar inventory',len(results),len(S.SANITY)))
    log('')
    log('The four identities are algebraic; the following are numerical sanity checks only.')
    for name,passed,note in S.SANITY:
        log(f'- {name}: {"PASS" if passed else "FAIL"}; {note}')
        ok &= bool(passed)
    if not ok:
        log('```text\n'+captured.getvalue()+'```')
    log('')
    log('## Source hashes')
    directory = Path(__file__).resolve().parent
    for p in sorted(directory.glob('*.py')):
        log(f'`{p.name}`: `{hashlib.sha256(p.read_bytes()).hexdigest()}`')
    log('')
    log(f'OVERALL: {"ALL CERTIFIED" if ok else "FAILED"}; '
        '78 scalar inequalities, 4 identity sanity checks, 23 direct groups.')
    Path(log_path).write_text('\n'.join(LOG)+'\n',encoding='utf-8')
    return bool(ok)


if __name__=='__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--log',default='LOCAL_CERT_LOG.md')
    args = parser.parse_args()
    sys.exit(0 if main(args.log) else 1)
