#!/usr/bin/env python3
"""Exact reconstruction for the whole doubly-shared side-channel C6 exit.

Uses only Python's standard library and Q(sqrt(2)) arithmetic. No floating
point value, pose sample, numerical optimizer, Lean or CI is used.

Run with --write-certificate-dir DIRECTORY to regenerate the JSON, or
without arguments to reconstruct every coefficient, inverse identity and
strict sign and compare the adjacent saved certificate when present.
"""
from fractions import Fraction as F
from math import comb
import json

def qa(a,b):return(a[0]+b[0],a[1]+b[1])
def qn(a):return(-a[0],-a[1])
def qm(a,b):return(a[0]*b[0]+2*a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def qr(a,r):return(a[0]*r,a[1]*r)
Q0=(F(0),F(0));Q1=(F(1),F(0));ROOT2=(F(0),F(1))
def sign(a):
    x,y=a
    if x==0:return (y>0)-(y<0)
    if y==0:return (x>0)-(x<0)
    if x>0 and y>0:return 1
    if x<0 and y<0:return -1
    d=x*x-2*y*y
    return ((d>0)-(d<0))*(1 if x>0 else -1)
def qi(a):
    dd=a[0]*a[0]-2*a[1]*a[1]
    return(a[0]/dd,-a[1]/dd)
def cn(a):return{(0,0):a}if a!=Q0 else{}
def ps(a,r):return{k:qr(v,r) for k,v in a.items() if qr(v,r)!=Q0}
def pa(a,b):
    c=a.copy()
    for k,v in b.items():
        c[k]=qa(c.get(k,Q0),v)
        if c[k]==Q0:del c[k]
    return c
def pn(a):return ps(a,-1)
def sub(a,b):return pa(a,pn(b))
def pm(a,b):
    c={}
    for (i,j),u in a.items():
        for (k,l),v in b.items():
            kl=(i+k,j+l)
            c[kl]=qa(c.get(kl,Q0),qm(u,v))
    return{k:v for k,v in c.items() if v!=Q0}
def sq(a):return pm(a,a)
def prod(*ls):
    a=cn(Q1)
    for b in ls:a=pm(a,b)
    return a
def qscale(a,q):return{k:qm(v,q) for k,v in a.items() if qm(v,q)!=Q0}
def bern(a,n=None,m=None):
    if n is None:n=max(i for i,j in a)
    if m is None:m=max(j for i,j in a)
    out={}
    for i in range(n+1):
        for j in range(m+1):
            b=Q0
            for (k,l),v in a.items():
                if k<=i and l<=j:b=qa(b,qr(v,F(comb(i,k),comb(n,k))*F(comb(j,l),comb(m,l))))
            out[i,j]=b
    return n,m,out
def ev(p,x,y):
    ans=Q0
    for(i,j),v in p.items():ans=qa(ans,qr(v,x**i*y**j))
    return ans
def pdiv(a,b):
    a=a.copy();quot={};rem={}
    lead=max(b);bv=b[lead]
    while a:
        la=max(a);av=a[la]
        if la[0]>=lead[0] and la[1]>=lead[1]:
            kk=(la[0]-lead[0],la[1]-lead[1]);vv=qm(av,qi(bv))
            quot[kk]=qa(quot.get(kk,Q0),vv)
            a=sub(a,pm({kk:vv},b))
        else:
            rem[la]=av;del a[la]
    return quot,rem

one=cn(Q1);x={(1,0):Q1};y={(0,1):Q1}
k=cn((F(-1),F(1)))
t=pm(k,x);H=pa(one,pm(sq(k),x));j=prod(k,sub(one,x),y)
Da=pa(one,sq(t));Dw=pa(sq(H),sq(j))
ca=qscale(sub(sub(one,ps(t,2)),sq(t)),(F(0),F(1,2)))
sa=qscale(sub(pa(one,ps(t,2)),sq(t)),(F(0),F(1,2)))
U=qscale(sub(sub(sq(H),sq(j)),ps(pm(H,j),2)),(F(0),F(1,2)))
V=qscale(pa(sub(sq(H),sq(j)),ps(pm(H,j),2)),(F(0),F(1,2)))
Sn=pa(pm(sa,U),pm(ca,V));Cn=sub(pm(ca,U),pm(sa,V))
# ell=En/(Da*V), with actual transmitter reserve exactly one.
En=sub(pm(sub(Da,ca),Dw),pm(Da,U))
base=prod(Da,Dw,V)
P=pa(pa(base,prod(Da,V,pa(U,V))),pm(V,Sn))
Q=sub(pa(base,prod(Da,V,sub(V,U))),pm(V,Cn))
RR=sub(pa(base,prod(Da,V,sub(U,V))),pm(Dw,En))
SS=pa(ps(base,2),prod(Da,V,pa(U,V)))
Dnum=sub(pm(P,SS),pm(Q,RR))
ABsq=pa(sq(P),sq(Q));CDsq=pa(sq(RR),sq(SS))
An=sub(pm(SS,ABsq),pm(Q,CDsq));Bn=sub(pm(P,CDsq),pm(RR,ABsq))
NF=pa(pm(Sn,pa(prod(Da,V,sub(An,Bn)),pm(En,Bn))),prod(En,Cn,An))
G=pn(NF)

# Exact positive normalization and its complete inverse identity.
factor=prod(Da,Dw,Dw,V)
G,rem=pdiv(G,factor)
assert not rem
assert pm(factor,G)==pn(NF)
assert max(i for i,j in G)==18 and max(j for i,j in G)==10
assert pa(sq(ca),sq(sa))==sq(Da)
assert pa(sq(U),sq(V))==sq(Dw)
assert pa(sq(Sn),sq(Cn))==sq(pm(Da,Dw))
n,m,bs=bern(G)
assert (n,m)==(18,10) and len(bs)==209
assert all(sign(qa(v,(-F(5,2),F(0))))>0 for v in bs.values())

# Reconstruct the entire power polynomial from the tensor Bernstein sum.
reconstructed={}
for kk in range(n+1):
    for ll in range(m+1):
        value=Q0
        for ii in range(kk+1):
            for jj in range(ll+1):
                scale=(comb(n,ii)*comb(n-ii,kk-ii)*comb(m,jj)*
                       comb(m-jj,ll-jj)*((-1)**(kk+ll-ii-jj)))
                value=qa(value,qr(bs[ii,jj],scale))
        if value!=Q0:reconstructed[kk,ll]=value
assert reconstructed==G

def qfloor(value):
    a,b=value
    lo=(a-2*abs(b)).numerator//(a-2*abs(b)).denominator-1
    hi=(a+2*abs(b)).numerator//(a+2*abs(b)).denominator+2
    while hi-lo>1:
        mid=(lo+hi)//2
        if sign(qa(value,(-F(mid),F(0))))>=0:lo=mid
        else:hi=mid
    assert sign(qa(value,(-F(lo),F(0))))>=0
    assert sign(qa(value,(-F(lo+1),F(0))))<0
    return lo

FLOORS = [
 [56,53,49,45,42,41,43,50,62,81,105],
 [54,51,47,44,41,41,44,51,63,81,104],
 [52,49,46,42,41,41,44,52,64,81,103],
 [49,47,44,41,40,41,45,53,65,82,103],
 [47,44,42,40,40,41,46,54,66,82,103],
 [44,41,40,39,39,42,47,56,67,83,103],
 [40,39,38,37,39,42,48,57,69,85,104],
 [37,36,36,36,39,43,50,59,71,86,104],
 [34,33,34,36,39,44,51,61,73,87,105],
 [31,31,33,36,40,46,53,63,75,89,105],
 [28,30,32,36,41,47,55,65,77,90,106],
 [26,29,32,37,43,50,58,68,79,92,106],
 [26,29,34,39,46,53,61,71,82,94,107],
 [27,32,37,43,49,57,65,74,84,95,107],
 [31,36,42,48,55,62,70,78,87,96,107],
 [39,44,50,55,62,68,75,82,90,97,106],
 [51,56,61,66,71,76,81,87,92,98,104],
 [70,73,76,80,83,86,89,92,95,98,101],
 [98,98,98,98,98,98,98,98,98,98,98],
]
assert [[qfloor(qr(bs[i,j],10)) for j in range(m+1)] for i in range(n+1)]==FLOORS

def encoded(poly):
    return [[i,j,str(v[0]),str(v[1])] for (i,j),v in sorted(poly.items())]

def scalar_check(x0,y0):
    # Recompute the normalized physical expressions in exact scalar
    # Q(sqrt(2)) arithmetic, independently of polynomial long division.
    da=ev(Da,x0,y0); dw=ev(Dw,x0,y0); vv=ev(V,x0,y0)
    ss=qm(ev(Sn,x0,y0),qi(qm(da,dw)))
    cc=qm(ev(Cn,x0,y0),qi(qm(da,dw)))
    ell=qm(ev(En,x0,y0),qi(qm(da,vv)))
    den=ev(base,x0,y0)
    pp,qq,rr,sside=[qm(ev(p,x0,y0),qi(den)) for p in (P,Q,RR,SS)]
    delta=qa(qm(pp,sside),qn(qm(qq,rr)))
    ab=qa(qm(pp,pp),qm(qq,qq));cd=qa(qm(rr,rr),qm(sside,sside))
    aa=qm(qa(qm(sside,ab),qn(qm(qq,cd))),qi(qr(delta,2)))
    bb=qm(qa(qm(pp,cd),qn(qm(rr,ab))),qi(qr(delta,2)))
    torque=qa(qm(ss,qa(aa,qn(qm(qa(Q1,qn(ell)),bb)))),qm(qm(ell,cc),aa))
    normalization=qr(qm(qm(qm(da,da),vv),ev(Dnum,x0,y0)),-2)
    assert qm(normalization,torque)==ev(G,x0,y0)

for xx,yy in [(F(0),F(0)),(F(1),F(0)),(F(0),F(1)),(F(1,2),F(1,3))]:
    scalar_check(xx,yy)

certificate={
 'title':'Exact whole-rectangle doubly-shared C6 torque certificate',
 'field':'Q(sqrt(2)); each coefficient pair is r+s*sqrt(2)',
 'degree':[n,m],
 'normalization':'G=-NF/(Da*Dw^2*V)=-2*Da^2*V*Dnum*F',
 'strict_coefficient_lower_bound':'5/2',
 'construction':'See the adjacent CHECK.py and theorem manuscript for every polynomial definition.',
 'power_coefficients':encoded(G),
 'bernstein_coefficients':encoded(bs),
 'floor_10_bernstein':FLOORS,
 'verified':['complete numerator-factor identity','three trigonometric polynomial identities',
             'complete Bernstein-to-power inverse identity','all 209 strict coefficient signs',
             'all 209 exact integer-floor bounds','four exact scalar normalization checks'],
}

if __name__=='__main__':
    import argparse
    from pathlib import Path
    parser=argparse.ArgumentParser()
    parser.add_argument('--write-certificate-dir',type=Path)
    args=parser.parse_args()
    filename='SIX_CYCLE_DOUBLE_SHARED_CHANNEL_CERTIFICATE.json'
    text=json.dumps(certificate,indent=2,ensure_ascii=True)+'\n'
    if args.write_certificate_dir:
        args.write_certificate_dir.mkdir(parents=True,exist_ok=True)
        path=args.write_certificate_dir/filename
        path.write_text(text)
        print('Wrote',path)
    else:
        path=Path(__file__).with_name(filename)
        if path.exists():
            assert path.read_text()==text,'Saved certificate differs from full reconstruction'
            print('Saved certificate matches the exact reconstruction byte for byte.')
    print('PASS: 209 coefficients >5/2; full polynomial and inverse identities; all exact floors.')
