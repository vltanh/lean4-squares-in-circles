"""Positive and negative controls supplied with the normalization certificate.

An expected non-certification is a regression control, NOT itself a proof
that a counterexample exists. A positive certificate still requires zero
unresolved boxes. Run with --backend rational for the independent stdlib
backend or --backend arb for installed python-flint.
"""
import argparse
import contextlib
import io
import math
import sys
from pathlib import Path


def main(backend='arb',log_path='SHARPNESS_LOG.md'):
    if backend=='rational':
        import rational_arb_compat as arithmetic
        sys.modules['flint'] = arithmetic
    import flint
    import ia as I
    from bnb import bnb
    import cert_main as M
    import cert_main2 as M2
    import cert_cone as K
    import cert_wd as WD
    label = getattr(flint,'__certificate_backend__','python-flint/Arb')
    lines = ['# Normalization sharpness controls',f'Backend: {label}.',
             'Expected non-certification does not by itself prove a counterexample.',
             '| test | expected | observed | boxes | unresolved | result |',
             '|---|---|---|---:|---:|---|']
    outcomes = []

    def run(name,root,ev,weights,expected,depth=60,limit=3_000_000):
        stats,un,n = bnb(root,ev,weights,max_depth=depth,max_boxes=limit,verbose=False)
        certified = not un
        good = certified==expected
        outcomes.append(good)
        line = f'| {name} | {"certified" if expected else "not certified"} | '+ \
               f'{"certified" if certified else "not certified"} | {n} | {len(un)} | {"PASS" if good else "FAIL"} |'
        print(line,flush=True)
        lines.append(line)

    R3 = [(-3.1416,3.1416),(0.5,1.2),(-1.2,1.2)]
    run('pins margin 0.049',R3,M.L2_eval_factory(I.arb('0.049')),[1,1,1],True,depth=80)
    run('pins margin 0.051',R3,M.L2_eval_factory(I.arb('0.051')),[1,1,1],False,depth=26)
    r6 = [(M2.H_LO,M2.H_HI),(-0.7854,0.7854),(-1.3,1.3),(-1.3,1.3)]
    run('L6 margin 0.037',r6,M2.L6_eval_factory(I.arb('0.037')),[1,1,1,1],True)
    run('L6 margin 0.038',r6,M2.L6_eval_factory(I.arb('0.038')),[1,1,1,1],False,depth=40)
    r7 = R3+[(0.0,math.nextafter(float(I.C0.lower()),-math.inf))]
    r7[-1] = (0.0,math.nextafter(float(I.C0.upper()),math.inf))
    run('L7 margin 0.10',r7,M2.L7_eval_factory(I.arb('0.10')),[1,1,1,1],True)
    run('L7 margin 0.11',r7,M2.L7_eval_factory(I.arb('0.11')),[1,1,1,1],False,depth=40)
    run('E/CE window +/-0.2025',R3,M.sep_window_factory('E','CE',-0.2025,0.2025),[1,1,1],True)
    run('E/CE window +/-0.200',R3,M.sep_window_factory('E','CE',-0.2,0.2),[1,1,1],False,depth=40)
    run('W/OWN upper 0.6165',[(0.0,6.2832),(0.5,1.2),(-1.2,1.2)],
        M.sep_window_factory('W','OWN',-0.6645,0.6165),[1,1,1],False,depth=40)
    cx,cy = I.C0.union(I.arb(1)/2),I.arb(0).union(I.C0)
    run('A1 arc (-0.995,1.22)',K.ROOT,K.cone_eval_factory(cx,cy,I.arb('0.995'),I.arb('1.22')),[1,1,1],False,depth=40)
    run('A1 arc (-0.99,1.23)',K.ROOT,K.cone_eval_factory(cx,cy,I.arb('0.99'),I.arb('1.23')),[1,1,1],False,depth=40)
    low = math.nextafter(float(I.C0.lower()),-math.inf)
    edges = [low+(0.5-low)*i/8 for i in range(9)]
    edges[-1] = 0.5
    run('A2 corner arc (-0.57,1.56)',K.ROOT,
        K.cone_eval_factory(I.iv(edges[7],edges[8]),I.iv(edges[7],edges[8]),I.arb('0.57'),I.arb('1.56')),
        [1,1,1],False,depth=30,limit=500_000)
    run('A2 near (1/2,c0), arc (-0.54,1.60)',K.ROOT,
        K.cone_eval_factory(I.iv(edges[7],edges[8]),I.iv(edges[0],edges[1]),I.arb('0.54'),I.arb('1.60')),
        [1,1,1],False,depth=40)

    def without_pair(box):
        reason = WD.ev(box)
        return None if reason=='pair-overlap' else reason

    run('W/D without pair disjointness',WD.root_box(),without_pair,[1,2,1,1,2,1],False,depth=40,limit=200_000)
    if len(outcomes)!=14: raise AssertionError('control inventory mismatch')
    ok = all(outcomes)
    lines.append(f'\nOVERALL: {sum(outcomes)}/14 controls behaved as expected.')
    Path(log_path).write_text('\n'.join(lines)+'\n',encoding='utf-8')
    return ok


if __name__=='__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--backend',choices=['arb','rational'],default='arb')
    parser.add_argument('--log',default='SHARPNESS_LOG.md')
    args = parser.parse_args()
    sys.exit(0 if main(args.backend,args.log) else 1)
