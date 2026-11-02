#!/usr/bin/env python3
"""Fraction-only independent replay of fixed-seven 58-leaf dyadic certificate."""
from fractions import Fraction as F
from pathlib import Path
from collections import Counter
import re
Q=F(1105,256);RHO=F(91,60)
C=[(F(-3,2),F(0)),(F(-1,2),F(-1)),(F(1,2),F(-1)),
   (F(3,2),F(0)),(F(-11,12),F(1)),(F(1,12),F(25,112)),
   (F(79,84),F(121,112))]
U=[(F(1),F(0))]*6+[(F(4,5),F(3,5))]
def dot(x,y):return x[0]*y[0]+x[1]*y[1]
def check_existing():
    squares=[]
    for (x,y),(a,b) in zip(C,U):
        assert a*a+b*b==1
        u=(a,b);v=(-b,a)
        for s in (-1,1):
            for t in (-1,1):
                px=x+(s*a-t*b)/2;py=y+(s*b+t*a)/2
                assert px*px+py*py<F(273,64)<Q
        squares.append(((x,y),u,v))
    for i in range(7):
        for j in range(i+1,7):
            ci,ui,vi=squares[i];cj,uj,vj=squares[j]
            w=(cj[0]-ci[0],cj[1]-ci[1])
            def h(n,u,v):return (abs(dot(n,u))+abs(dot(n,v)))/2
            assert any(abs(dot(n,w))>=h(n,ui,vi)+h(n,uj,vj)
                       for n in (ui,vi,uj,vj)),('overlap',i,j)
def check_cap():
    xR,yR=C[6];u=U[6];v=(-u[1],u[0])
    ends=[(x,y) for x in (-F(1,12),F(1,12)) for y in (F(4,3),RHO)]
    umax=max(abs(dot(u,(x-xR,y-yR))) for x,y in ends)
    vmax=max(abs(dot(v,(x-xR,y-yR))) for x,y in ends)
    assert umax==F(1121,1680) and vmax==F(289,300)
    margin=F(1,4)-max(F(0),umax-F(1,2))**2-max(F(0),vmax-F(1,2))**2
    assert margin==F(518311,70560000)>0
def box(path):
    x0,x1,y0,y1=-RHO,RHO,-RHO,RHO
    for digit in path:
        assert digit in '01'
        if x1-x0>=y1-y0:
            mid=(x0+x1)/2
            if digit=='0':x1=mid
            else:x0=mid
        else:
            mid=(y0+y1)/2
            if digit=='0':y1=mid
            else:y0=mid
    return x0,x1,y0,y1
def check_leaf(path,reason):
    x0,x1,y0,y1=box(path)
    if reason=='cap':
        assert x0>=-F(1,12) and x1<=F(1,12) and y0>=F(4,3)
    elif reason=='outer':
        dx=max(x0,-x1,F(0));dy=max(y0,-y1,F(0))
        assert dx*dx+dy*dy>=RHO*RHO
    elif reason.startswith('center_'):
        i=int(reason[7:]);assert 0<=i<7
        a,b=C[i];dx=max(abs(x0-a),abs(x1-a));dy=max(abs(y0-b),abs(y1-b))
        assert dx*dx+dy*dy<1,(path,reason)
    else:raise AssertionError('unknown certificate rule')
def check_full_tree(rows):
    root={}
    for path,reason in rows:
        assert len(path)<=24 and all(d in '01' for d in path)
        node=root
        for digit in path:
            assert 'leaf' not in node
            node=node.setdefault(digit,{})
        assert not node,('duplicate or redundant row',path)
        node['leaf']=reason
        check_leaf(path,reason)
    def rec(node):
        if 'leaf' in node:
            assert len(node)==1
            return 1
        assert set(node)=={'0','1'},'uncovered dyadic child'
        return rec(node['0'])+rec(node['1'])
    assert rec(root)==len(rows)
def main():
    md=Path(__file__).with_name('NO_EIGHTH_FIXED_SEVEN_HAND_TABLE.md').read_text()
    pattern=r'^\| \x60([01]+)\x60 \| \x60(outer|cap|center_[0-6])\x60 \|$'
    rows=re.findall(pattern,md,re.M)
    assert len(rows)==58 and max(len(p) for p,r in rows)==13
    check_existing()
    assert RHO*RHO+RHO+F(1,2)-Q==F(31,57600)
    check_cap()
    check_full_tree(rows)
    print('PASS: 58 exact rational dyadic leaves, 57 internal nodes, cap margin 518311/70560000.')
    print('Reasons:',dict(Counter(r for p,r in rows)))
    for bad in (rows[:-1],rows+[rows[0]],[(p,'outer' if r=='center_1' else r)
                                         for p,r in rows]):
        try:check_full_tree(bad)
        except (AssertionError,ValueError):continue
        raise AssertionError('corrupted certificate accepted')
    print('PASS: negative-control leaf corruptions rejected')
if __name__=='__main__':main()
