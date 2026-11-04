#!/usr/bin/env python3
"""Exact physical n=9 fixed-mask QF_NRA emitter; no solver or UNSAT claimed.

Common rotation places the existential witness cone frame at x/y.
Each physical square's side frame may independently be reparameterized
within [-pi/4,pi/4] by its own 90-degree symmetries. This is not a common
orientation or original positional-root gauge.
"""
import argparse
from itertools import combinations,product
from pathlib import Path
SIGNS=list(product((-1,1),repeat=2))
EDGES=[(0,1),(1,2),(2,3),(4,5),(5,6)]
def f(op,*args):
    atoms=[f'(- {-z})' if isinstance(z,int) and z<0 else str(z) for z in args]
    return '('+' '.join((op,*atoms))+')'
def add(*z):return f('+',*z)
def mul(*z):return f('*',*z)
def sub(x,y):return f('-',x,y)
def neg(x):return f('-',x)
def dot(u,v):return add(mul(u[0],v[0]),mul(u[1],v[1]))
def cmp(op,a,b):return f(op,a,b)
def emit(mask='000/01',radius='strict',n=9):
    if len(mask)!=6 or mask[3]!='/' or any(v not in '01' for v in mask[:3]+mask[4:]):
        raise ValueError('expected abc/de five-bit mask')
    if radius not in ('strict','closed') or n not in (7,9):
        raise ValueError('strict/closed; n=9 proof target or n=7 regression control')
    out=['; Exact all-nine-square physical fixed-mask model; no UNSAT proof.',
         '; n=7 is only a known SAT negative control.',
         '(set-logic QF_NRA)']
    def req(name,expr):out.append(f'(assert (! {expr} :named {name}))')
    for i in range(n):
        for z in 'xyabh':out.append(f'(declare-fun {z}_{i} () Real)')
    sq=[]
    for i in range(n):
        x,y,a,b,h=[f'{z}_{i}' for z in 'xyabh']
        u=(a,b);v=(neg(b),a);sq.append(((x,y),u,v,h))
        req(f'unit_{i}',cmp('=',add(mul(a,a),mul(b,b)),1))
        req(f'fold_pos_{i}',cmp('>=',a,b))
        req(f'fold_neg_{i}',cmp('>=',a,neg(b)))
        # 2h-a=|b|; the folding a>=|b| makes h the true x/y halfwidth.
        w=sub(mul(2,h),a)
        req(f'width_pos_{i}',cmp('>=',w,0))
        req(f'width_exact_{i}',cmp('=',mul(w,w),mul(b,b)))
        for k,(s,t) in enumerate(SIGNS):
            X=add(mul(2,x),mul(s,a),mul(-t,b))
            Y=add(mul(2,y),mul(s,b),mul(t,a))
            req(f'corner_{i}_{k}',cmp('<' if radius=='strict' else '<=',
                                       mul(64,add(mul(X,X),mul(Y,Y))),1105))
    for i,j in combinations(range(n),2):
        ci,ui,vi,_=sq[i];cj,uj,vj,_=sq[j]
        diff=(sub(cj[0],ci[0]),sub(cj[1],ci[1]))
        C=dot(ui,uj);S=dot(vi,uj)
        branches=[]
        for axis in (ui,vi,uj,vj):
            p=dot(axis,diff)
            for sign in (-1,1):
                bounds=[cmp('>=',mul(2*sign,p),add(1,mul(s,C),mul(t,S)))
                        for s,t in SIGNS]
                branches.append(f('and',*bounds))
        req(f'pair_{i}_{j}',f('or',*branches))
    for k,((i,j),bit) in enumerate(zip(EDGES,mask[:3]+mask[4:])):
        dx=sub(f'x_{j}',f'x_{i}');dy=sub(f'y_{j}',f'y_{i}')
        req(f'cone_{k}',f('and',cmp('>=',dx,dy),cmp('>=',dx,neg(dy))))
        req(f'edge_{k}_'+('actual' if bit=='0' else 'weak'),
            cmp('>=' if bit=='0' else '<',dx,add(f'h_{i}',f'h_{j}')))
    out+=['(check-sat)','']
    return '\n'.join(out)
def main():
    p=argparse.ArgumentParser()
    p.add_argument('--mask',default='000/01')
    p.add_argument('--radius',choices=['strict','closed'],default='strict')
    p.add_argument('--n',type=int,choices=[7,9],default=9)
    p.add_argument('--output',type=Path)
    a=p.parse_args()
    result=emit(a.mask,a.radius,a.n)
    if a.output:
        a.output.write_text(result)
        print('Wrote',a.output,len(result),'bytes; no solver called')
    else:print(result,end='')
if __name__=='__main__':main()
