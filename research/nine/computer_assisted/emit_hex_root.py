#!/usr/bin/env python3
"""Append one canonical closed hex-cell root to the original unrestricted model.

No square-frame gauge is applied: fixing square 0 horizontal would not preserve
an already selected hex-cell root. The only extra real is the positive sqrt(3).
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
from emit_unrestricted_nine import build,op,add,mul,neg


def build_root(row: dict, cells: list, radius: str = 'strict'):
    if radius not in {'strict','closed'}:
        raise ValueError('radius must be strict or closed')
    if len(row['cells'])!=9 or len(set(row['cells']))!=9:
        raise ValueError('a root must specify nine distinct cells')
    f=build(n=9,radius=radius,gauge=False)
    k=f.variable('sqrt_three')
    f.require('sqrt_three_positive',op('>',k,0))
    f.require('sqrt_three_square',op('=',mul(k,k),3))
    for i,c in enumerate(row['cells']):
        q,r=cells[c]
        x,y=f'x_{i}',f'y_{i}'
        expressions=[
            (add(mul(200,y),mul(-49*(q+2*r),k)),49),
            (add(mul(200,k,x),mul(200,y),mul(-49*(4*q+2*r),k)),98),
            (add(mul(200,k,x),mul(-200,y),mul(-49*(2*q-2*r),k)),98)]
        for j,(value,bound) in enumerate(expressions):
            for sign in (-1,1):
                f.require(f'hex_{i}_{j}_{"minus" if sign<0 else "plus"}',
                          op('<=',mul(sign,value),mul(bound,k)))
    return f


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root',type=int,required=True)
    ap.add_argument('--radius',choices=('strict','closed'),default='strict')
    ap.add_argument('--manifest',type=Path,default=Path(__file__).with_name('hex_root_manifest.json'))
    ap.add_argument('--output',type=Path)
    args=ap.parse_args();manifest=json.loads(args.manifest.read_text())
    if not 0<=args.root<len(manifest['roots']):
        ap.error('root ID outside manifest')
    row=manifest['roots'][args.root]
    f=build_root(row,manifest['cells'],args.radius)
    text='; Positional root '+str(args.root)+'; manifest status '+row['status']+'\n'+f.smt2()
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(text)
    else:print(text,end='')

if __name__=='__main__':main()
