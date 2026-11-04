#!/usr/bin/env python3
"""Exact rational regression evaluator for emitted SMT; not an UNSAT proof."""
from fractions import Fraction as F
import re
from emit_fixed_mask import emit
def parse(src):
    words=iter(re.findall(r'\(|\)|[^\s()]+','\n'.join(
        line for line in src.splitlines() if not line.startswith(';'))))
    def item(t):
        if t!='(':return t
        out=[]
        for token in words:
            if token==')':return out
            out.append(item(token))
        raise ValueError('unclosed sexpr')
    return [item(t) for t in words]
def evaluate(e,vals):
    if isinstance(e,str):
        if e in vals:return vals[e]
        return F(int(e))
    op=e[0]
    if op=='and':return all(evaluate(x,vals) for x in e[1:])
    if op=='or':return any(evaluate(x,vals) for x in e[1:])
    a=[evaluate(x,vals) for x in e[1:]]
    if op=='+':return sum(a,F(0))
    if op=='*':
        r=F(1)
        for x in a:r*=x
        return r
    if op=='-':return -a[0] if len(a)==1 else a[0]-a[1]
    if op=='=':return a[0]==a[1]
    if op=='<':return a[0]<a[1]
    if op=='<=':return a[0]<=a[1]
    if op=='>':return a[0]>a[1]
    if op=='>=':return a[0]>=a[1]
    raise ValueError(op)
def environment(poses):
    vals={}
    for i,((x,y),(a,b)) in enumerate(poses):
        assert a*a+b*b==1
        for n,v in [('x',x),('y',y),('a',a),('b',b),('h',(abs(a)+abs(b))/2)]:
            vals[f'{n}_{i}']=v
    return vals
def check(n,mask,radius,vals):
    stmts=parse(emit(mask,radius,n))
    assert sum(t[0]=='declare-fun' for t in stmts if isinstance(t,list))==5*n
    claims=[(t[1][3],t[1][1]) for t in stmts if isinstance(t,list) and t[0]=='assert']
    assert len(claims)==9*n+n*(n-1)//2+10
    return [name for name,expr in claims if not evaluate(expr,vals)]
one=F(1);zero=F(0)
seven=[
    ((-F(3,2),zero),(one,zero)),((-F(1,2),-one),(one,zero)),
    ((F(1,2),-one),(one,zero)),((F(3,2),zero),(one,zero)),
    ((-F(11,12),one),(one,zero)),((F(1,12),F(25,112)),(one,zero)),
    ((F(79,84),F(121,112)),(F(4,5),F(3,5)))]
nine=[((F(k,2),F(1,16)),(one,zero)) for k in (-3,-1,1,3)]+[
      ((F(k),-F(15,16)),(one,zero)) for k in (-1,0,1)]+[
      ((F(k,20),F(19,16)),(F(99,101),F(20,101))) for k in (-11,11)]
def main():
    s=environment(seven);a=environment(nine)
    assert check(7,'000/01','strict',s)==[]
    assert check(7,'000/00','strict',s)==['edge_4_actual']
    assert check(9,'000/00','closed',a)==[]
    errors=check(9,'000/00','strict',a)
    assert len(errors)==4 and all(x.startswith('corner_') for x in errors),errors
    assert check(9,'000/01','closed',a)==['edge_4_weak']
    print('PASS: exact SMT seven-square SAT strict 000/01, nine-square equality and four strict-corner negatives.')
    print('No nine-square UNSAT proof.')
if __name__=='__main__':main()
