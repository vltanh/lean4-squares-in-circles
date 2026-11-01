#!/usr/bin/env python3
"""Append proved wide-slide chart guards in the ORIGINAL physical coordinates.

A guarded strict-Q model is refuted by WIDE_SLIDE_SHARP_TERMINAL.md. The guards
are sufficient terminal hypotheses, NOT a cover of every packing or root.
No global frame gauge is imposed, including on an already fixed hex root.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
from typing import Sequence
from emit_unrestricted_nine import build,op,add,mul,sub
from emit_hex_root import build_root


def build_terminal(selected: Sequence[int] = tuple(range(7)), mirror: int = 1,
                   radius: str = 'strict', row: dict | None = None,
                   cells: list | None = None):
    selected=tuple(selected)
    if len(selected)!=7 or len(set(selected))!=7 or any(type(i) is not int or not 0<=i<9 for i in selected):
        raise ValueError('select seven distinct original square IDs, in M0..M3,B0..B2 order')
    if type(mirror) is not int or mirror not in (-1,1):
        raise ValueError('mirror must be +1 or -1')
    if radius not in ('strict','closed'):
        raise ValueError('use strict or closed original corner constraints')
    if (row is None)!=(cells is None):
        raise ValueError('a positional root requires its cell list')
    f=build(n=9,radius=radius,gauge=False) if row is None else build_root(row,cells,radius)
    ref=selected[0];ar,br=f'a_{ref}',f'b_{ref}'
    # Coordinates in one common frame; no original variable is substituted.
    # Reflection reverses the second frame axis, representing the same square.
    xbase8=(-12,-4,4,12,-8,0,8)
    ybounds=((16,-1,3),(16,-1,12),(16,-1,12),(16,-1,3),
             (16,-17,-13),(32,-49,-26),(16,-17,-13))
    for j,i in enumerate(selected):
        x,y,a,b=(f'{v}_{i}' for v in ('x','y','a','b'))
        X=f.define(f'chart_X_{j}',add(mul(ar,x),mul(br,y)))
        Y=f.define(f'chart_Y_{j}',mul(mirror,sub(mul(ar,y),mul(br,x))))
        A=f.define(f'chart_A_{j}',add(mul(ar,a),mul(br,b)))
        T=f.define(f'chart_T_{j}',mul(mirror,sub(mul(ar,b),mul(br,a))))
        f.require(f'guard_x_low_{j}',op('>=',mul(8,X),xbase8[j]-1))
        f.require(f'guard_x_high_{j}',op('<=',mul(8,X),xbase8[j]+1))
        scale,low,high=ybounds[j]
        f.require(f'guard_y_low_{j}',op('>=',mul(scale,Y),low))
        f.require(f'guard_y_high_{j}',op('<=',mul(scale,Y),high))
        f.require(f'guard_frame_half_{j}',op('>=',A,0))
        f.require(f'guard_tilt_low_{j}',op('>=',mul(64,T),-1))
        f.require(f'guard_tilt_high_{j}',op('<=',mul(64,T),1))
    return f


def build_pruned(selected: Sequence[int] = tuple(range(7)), mirror: int = 1,
                 row: dict | None = None, cells: list | None = None):
    """Add the sharp theorem's forbidden-chart cut to a STRICT-Q root.

    Every physical subcritical packing must violate at least one chart guard.
    This cuts out a proved terminal without assuming that the rest is empty.
    Applying this cut to the closed-Q equality model would be unsound.
    """
    f=build_terminal(selected,mirror,'strict',row,cells)
    guards=[predicate for name,predicate in f.assertions if name.startswith('guard_')]
    if len(guards)!=49 or any(p[0] not in ('>=','<=') for p in guards):
        raise ValueError('unexpected sharp-guard schema')
    f.assertions=[(name,p) for name,p in f.assertions if not name.startswith('guard_')]
    complement=[op('<' if p[0]=='>=' else '>',*p[1:]) for p in guards]
    f.require('sharp_terminal_complement',op('or',*complement))
    return f


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--selected',default='0,1,2,3,4,5,6')
    ap.add_argument('--mirror',type=int,choices=(-1,1),default=1)
    ap.add_argument('--radius',choices=('strict','closed'),default='strict')
    ap.add_argument('--root',type=int)
    ap.add_argument('--cut',action='store_true',help='Exclude the proved chart from a strict-Q search root')
    ap.add_argument('--manifest',type=Path,default=Path(__file__).with_name('hex_root_manifest.json'))
    ap.add_argument('--output',type=Path)
    args=ap.parse_args()
    try:selected=tuple(int(i) for i in args.selected.split(','))
    except ValueError:ap.error('selected must be comma-separated original square IDs')
    row=cells=None
    if args.root is not None:
        data=json.loads(args.manifest.read_text());cells=data['cells']
        if not 0<=args.root<len(data['roots']):ap.error('invalid root ID')
        row=data['roots'][args.root]
    if args.cut and args.radius!='strict':ap.error('sharp cuts are sound only for the strict-Q model')
    try:
        f=(build_pruned(selected,args.mirror,row,cells) if args.cut else
           build_terminal(selected,args.mirror,args.radius,row,cells))
    except ValueError as error:ap.error(str(error))
    header=('; Strict-Q root with a proved forbidden-chart cut; residual root still OPEN.\n' if args.cut else
            '; Sufficient sharp-terminal chart only; NOT a global packing cover.\n')
    text=header+f.smt2()
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(text)
    else:print(text,end='')

if __name__=='__main__':main()
