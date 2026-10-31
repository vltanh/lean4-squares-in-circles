#!/usr/bin/env python3
"""Exact whole-angle certificate for the three-shared alternating C6 exit.

Standard library only. All arithmetic is in Q(sqrt(2)); no numerical
evaluation, pose search, external algebra package, Lean or CI is used.
Run with --write-certificate-dir DIR to regenerate the JSON, or without
arguments to verify its exact bytes after complete reconstruction.
"""
from fractions import Fraction as F
from math import comb
import json


def qa(a,b): return (a[0]+b[0],a[1]+b[1])
def qr(a,r): return (a[0]*r,a[1]*r)
def qm(a,b): return (a[0]*b[0]+2*a[1]*b[1],a[0]*b[1]+a[1]*b[0])
ZERO=(F(0),F(0)); ONE=(F(1),F(0))


def sign(a):
    x,y=a
    if x==0: return (y>0)-(y<0)
    if y==0: return (x>0)-(x<0)
    if x>0 and y>0: return 1
    if x<0 and y<0: return -1
    d=x*x-2*y*y
    return ((d>0)-(d<0))*(1 if x>0 else -1)


def const(a): return {(0,0):a} if a!=ZERO else {}
def scale(a,r): return {k:qr(v,r) for k,v in a.items() if qr(v,r)!=ZERO}
def qscale(a,r): return {k:qm(v,r) for k,v in a.items() if qm(v,r)!=ZERO}


def add(a,b):
    out=a.copy()
    for k,v in b.items():
        out[k]=qa(out.get(k,ZERO),v)
        if out[k]==ZERO: del out[k]
    return out


def sub(a,b): return add(a,scale(b,-1))


def mul(a,b):
    out={}
    for (i,j),u in a.items():
        for (k,l),v in b.items():
            key=(i+k,j+l)
            out[key]=qa(out.get(key,ZERO),qm(u,v))
    return {k:v for k,v in out.items() if v!=ZERO}


def sq(a): return mul(a,a)
def sum_polys(polys):
    out={}
    for p in polys: out=add(out,p)
    return out


def bernstein(a,n,m):
    out={}
    for i in range(n+1):
        for j in range(m+1):
            value=ZERO
            for (k,l),c in a.items():
                if k<=i and l<=j:
                    value=qa(value,qr(c,F(comb(i,k),comb(n,k))*F(comb(j,l),comb(m,l))))
            out[i,j]=value
    return out


def inverse(bs,n,m):
    out={}
    for k in range(n+1):
        for l in range(m+1):
            value=ZERO
            for i in range(k+1):
                for j in range(l+1):
                    factor=comb(n,i)*comb(n-i,k-i)*comb(m,j)*comb(m-j,l-j)*(-1)**(k+l-i-j)
                    value=qa(value,qr(bs[i,j],factor))
            if value!=ZERO: out[k,l]=value
    return out


def qfloor(value):
    a,b=value
    lo=(a-2*abs(b)).numerator//(a-2*abs(b)).denominator-1
    hi=(a+2*abs(b)).numerator//(a+2*abs(b)).denominator+2
    while hi-lo>1:
        mid=(lo+hi)//2
        if sign(qa(value,(-F(mid),F(0))))>=0: lo=mid
        else: hi=mid
    assert sign(qa(value,(-F(lo),F(0))))>=0
    assert sign(qa(value,(-F(lo+1),F(0))))<0
    return lo


one=const(ONE); x={(1,0):ONE}; y={(0,1):ONE}
k=const((F(-1),F(1)))
t=mul(k,x)
H=add(one,mul(sq(k),x))
j=mul(mul(k,sub(one,x)),y)
Da=add(one,sq(t)); Db=add(sq(H),sq(j))
ca=qscale(sub(sub(one,scale(t,2)),sq(t)),(F(0),F(1,2)))
sa=qscale(sub(add(one,scale(t,2)),sq(t)),(F(0),F(1,2)))
cb=qscale(sub(sub(sq(H),sq(j)),scale(mul(H,j),2)),(F(0),F(1,2)))
sb=qscale(add(sub(sq(H),sq(j)),scale(mul(H,j),2)),(F(0),F(1,2)))
S=add(mul(sa,cb),mul(ca,sb))
C=sub(mul(ca,cb),mul(sa,sb))
L=mul(Da,Db)
assert add(sq(ca),sq(sa))==sq(Da)
assert add(sq(cb),sq(sb))==sq(Db)
assert add(sq(S),sq(C))==sq(L)

# theta_0=pi-alpha, theta_1=pi-beta, theta_2=alpha+beta.
sines=[mul(sa,Db),mul(sb,Da),S]
cosines=[scale(mul(ca,Db),-1),scale(mul(cb,Da),-1),C]
Q=[]
for i in range(3):
    value=qscale(L,(F(-2),F(79,40)))
    value=sub(value,sines[i])
    value=add(value,scale(cosines[i],F(163,400)))
    value=sub(value,scale(cosines[(i+1)%3],F(237,400)))
    Q.append(value)
T=sum_polys(Q)
G=add(sub(scale(mul(L,T),F(711,400)),scale(sum_polys([sq(q) for q in Q]),3)),sq(T))
assert max(i for i,j in G)==8 and max(j for i,j in G)==4
bs=bernstein(G,8,4)
assert len(bs)==45
assert all(sign(qa(v,(-F(1,100),F(0))))>0 for v in bs.values())
assert inverse(bs,8,4)==G

# Exact independent expansion of the variance normalization:
# 3*variance = sum of the three pairwise squared differences.
pair_squares=sum_polys([sq(sub(Q[i],Q[(i+1)%3])) for i in range(3)])
assert pair_squares==sub(scale(sum_polys([sq(q) for q in Q]),3),sq(T))
assert G==sub(scale(mul(L,T),F(711,400)),pair_squares)

FLOORS=[
 [55,17,133,273,76],
 [149,73,117,185,50],
 [201,112,116,144,70],
 [212,135,127,143,122],
 [187,147,149,173,194],
 [141,148,177,220,271],
 [95,145,200,261,328],
 [81,140,200,259,319],
 [144,144,144,144,144],
]
assert [[qfloor(qr(bs[i,j],1000)) for j in range(5)] for i in range(9)]==FLOORS

# Every endpoint comparison used for the two elementary chord bounds.
assert 50**2*2-69**2==239>0
assert 569**2-2*400**2==3761>0
assert F(12)*F(79,40)*F(3,40)==F(711,400)
assert F(1)-F(3,10)*F(79,40)==F(163,400)


def encoded(poly):
    return [[i,j,str(v[0]),str(v[1])] for (i,j),v in sorted(poly.items())]


certificate={
 'title':'Exact whole-angle three-shared alternating C6 radius certificate',
 'field':'Q(sqrt(2)); every coefficient pair is r+s*sqrt(2)',
 'degree':[8,4],
 'normalization':'G=L^2*B, B=(711/400)*sum(q_i)-3*sum(q_i^2)+sum(q_i)^2',
 'strict_coefficient_lower_bound':'1/100',
 'construction':'Every defining polynomial is in the adjacent CHECK.py and theorem source.',
 'power_coefficients':encoded(G),
 'bernstein_coefficients':encoded(bs),
 'floor_1000_bernstein':FLOORS,
 'verified':['three full trigonometric polynomial identities',
             'full pairwise-variance polynomial identity',
             'complete Bernstein-to-power inverse identity',
             'all 45 strict coefficient signs and exact floor values',
             'every elementary endpoint reserve'],
}


if __name__=='__main__':
    import argparse
    from pathlib import Path
    parser=argparse.ArgumentParser()
    parser.add_argument('--write-certificate-dir',type=Path)
    args=parser.parse_args()
    filename='SIX_CYCLE_THREE_SHARED_MATCHING_CERTIFICATE.json'
    text=json.dumps(certificate,indent=2,ensure_ascii=True)+'\n'
    if args.write_certificate_dir:
        args.write_certificate_dir.mkdir(parents=True,exist_ok=True)
        path=args.write_certificate_dir/filename
        path.write_text(text)
        print('Wrote',path)
    else:
        path=Path(__file__).with_name(filename)
        if path.exists():
            assert path.read_text()==text,'Saved certificate differs from complete reconstruction'
            print('Saved certificate matches the exact reconstruction byte for byte.')
    print('PASS: all 45 coefficients >1/100; full inverse, variance and trigonometric identities; exact floors and reserves.')
