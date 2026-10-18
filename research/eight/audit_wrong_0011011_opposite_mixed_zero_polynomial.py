"""Independent polynomial and data reconstruction for the opposite mixed-zero hand proof."""
from fractions import Fraction as F
from math import comb
from pathlib import Path
import hashlib, json

ROOT=Path("/workspace/scratch/6ea6bf046677")
D=ROOT/"proof_integration"
OUT=ROOT/"m5_agent/hand_conversion"
proof=D/"WRONG_0011011_OPPOSITE_MIXED_ZERO_HAND_PROOF.md"
checker=D/"verify_wrong_0011011_opposite_mixed_zero_hand.py"
record=D/"wrong_0011011_opposite_mixed_zero_hand_arithmetic.json"
labels=D/"wrong_0011011_labels.json"
data=json.loads(labels.read_text())
source=json.loads(record.read_text())
assert source["status"]=="PASS" and source["strict_comparisons"]==149

def clean(p):
    p=list(p)
    while len(p)>1 and not p[-1]:p.pop()
    return p
def plus(p,q):
    p,q=list(p),list(q)
    return clean([(p[i] if i<len(p) else F(0))+(q[i] if i<len(q) else F(0))
                  for i in range(max(len(p),len(q)))])
def times(p,q):
    z=[F(0)]*(len(p)+len(q)-1)
    for i,a in enumerate(p):
        for j,b in enumerate(q):z[i+j]+=a*b
    return clean(z)
def sc(p,s):return clean([a*F(s) for a in p])
def sub(p,q):return plus(p,sc(q,-1))
def power(p,n):
    z=[F(1)]
    for _ in range(n):z=times(z,p)
    return z
def deriv(p):return clean([F(i)*p[i] for i in range(1,len(p))])
def composition(p,l,h):
    z=[F(0)]
    for c in reversed(p):z=plus(times(z,[l,h]),[c])
    return z

q=F(9789,2500)
b=[F(0),F(1)]
v=plus(b,[F(1,2)])
x=plus(b,[F(-1,2)])
u2=sub([q],power(v,2))
k=F("1.89442")
h=F("2.99496")
j=F("4.80231")
lam=F(144,13)
N=sub(times([F(1,2),F(2)],v),[q])
# Independent differentiation of N/sqrt(U), using U'=-2v.
assert sub(plus(times(deriv(N),u2),times(N,v)),
           plus(sc(times(v,u2),2),sc(b,q)))==[F(0)]
A=plus(sc(times(x,[j,-h]),lam),[h])
B=sc(sub(sc(times(times(x,N),u2),lam),
         plus(sc(times(v,u2),2),sc(b,q))),k)
P=sub(times(power(A,2),power(u2,3)),power(B,2))
assert len(P)==11
assert P==list(map(F,source["corner_polynomial"]["power_coefficients"]))

# Solve the defining Bernstein basis triangular system, not the author's sum.
n=10
p=composition(P,F(1,2),F(2,5))
p += [F(0)]*(n+1-len(p))
beta=[]
for degree in range(n+1):
    residual=p[degree]
    for i,bi in enumerate(beta):
        residual-=bi*comb(n,i)*comb(n-i,degree-i)*((-1)**(degree-i))
    beta.append(residual/F(comb(n,degree)))
floors=[4,16,34,51,70,96,133,180,233,284,326]
assert all(z>m for z,m in zip(beta,floors))
# Direct reconstruction verifies every power coefficient of the basis identity.
rebuild=[F(0)]*(n+1)
for i,bi in enumerate(beta):
    for r in range(n-i+1):
        rebuild[i+r]+=bi*comb(n,i)*comb(n-i,r)*((-1)**r)
assert rebuild==p

def role(i,tag):
    if str(i) in data["independent_roles"]:
        raw=data["independent_roles"][str(i)][tag]
    else:
        sign="-" if tag[-1]=="+" else "+"
        raw=data["independent_roles"][str((2-i)%7)][tag[:-1]+sign]
    return [F(v,data["denominator"]) for v in raw]
named={
 "J":(role(1,"O-"),role(0,"C+")),
 "P":(role(0,"O+"),role(1,"C+")),
 "L":(role(4,"O+"),role(4,"C+")),
}
expected={
 "J":(["0","-.00026",".83194","-.11864",".17627"],[".00125","0","1.03981","0","0"]),
 "P":([".02478","0",".93015",".02363","-.11055"],[".19555","0",".63132","0","0"]),
 "L":([".03965","0","3.85510","-1.49748","-1.89442"],[".04970","0",".94831","0","0"]),
}
for name,(o,c) in named.items():
    assert o==list(map(F,expected[name][0]))
    assert c==list(map(F,expected[name][1]))
assert data["word"]==[0,0,1,1,0,1,1]
assert F(data["Q"])==q and F(data["gamma"])==F(17953,20000)
result={
 "status":"PASS",
 "independent_checks":{
    "fixed_author_replay_comparisons":149,
    "polynomial_identity":"exact rational equality",
    "polynomial_power_coefficients_match":True,
    "independent_triangular_Bernstein_reconstruction":True,
    "strict_Bernstein_coefficient_bounds":11,
    "label_coefficients_matched":30,
 },
 "files":{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
          for p in (proof,checker,record,labels)},
 "bernstein_coefficients":[str(z) for z in beta],
 "integer_floors":floors,
}
(OUT/"wrong_0011011_opposite_mixed_zero_independent_polynomial_audit.json").write_text(
 json.dumps(result,indent=2)+"\n")
print(json.dumps({"status":"PASS","independent_Bernstein_bounds":11,
                  "label_coefficients_matched":30}))
