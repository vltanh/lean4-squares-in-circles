"""Independent Fraction reconstruction of the two displayed M/M rows."""
from fractions import Fraction as F
from math import factorial,comb
import json

def add(*ps):
 n=max(map(len,ps)); r=[F(0)]*n
 for p in ps:
  for i,x in enumerate(p):r[i]+=x
 return r
def scale(p,a):return [x*F(a) for x in p]
def mul(p,q):
 r=[F(0)]*(len(p)+len(q)-1)
 for i,x in enumerate(p):
  for j,y in enumerate(q):r[i+j]+=x*y
 return r
def trig(parity,n):
 p=[F(0)]*(n+1)
 for i in range(parity,n+1,2):p[i]=F((-1)**((i-parity)//2),factorial(i))
 return p
def bern(p,l,r):
 l,r=F(l),F(r);n=len(p)-1
 d=[sum(p[i]*comb(i,j)*l**(i-j)*(r-l)**j for i in range(j,n+1)) for j in range(n+1)]
 return [sum(d[j]*F(comb(k,j),comb(n,j)) for j in range(k+1)) for k in range(n+1)]
Q=F('3.9156');p=F('1.489593');q=F('1.580219');cM=F('-2.143075');gamma=F('.8912')
s7,s9,c8,c10=trig(1,7),trig(1,9),trig(0,8),trig(0,10)
lam=F('.87');mF=F('.4555')-lam*F('.513966884')
KF=F('.09')+mF-cM+(p+q+lam)/2
TF=add([KF-gamma,F(1)],scale(s7,lam-F('.09')),scale(c8,F('-.09')))
VF=add([p*p+q*q+lam*lam],scale(s9,2*lam*p),scale(c10,-2*lam*q))
mP=-F('.455511')-F('1.199256062')
KP=F('.09')+mP-cM+(p+q+1)/2
TP=add([KP-gamma,F(1)],scale(s9,F('-.09')),scale(c8,F('-.91')))
VP=add([p*p+q*q+1],scale(c10,-2*p),scale(s7,-2*q))
rows=[('F',TF,VF,'.6','1.09',4,[97837,100029,101671,102928,103966,104945,106025,107361,109106,111414,114433,118313,123199,129239,136578,145361,155733]),('P',TP,VP,'1.57','1.85',3,[248977,257702,265257,271671,276972,281190,284354,286491,287630,287799,287024,285333,282752,279306,275022,269924,264037,257385,249991])]
count=0;report=[]
for name,T,V,l,r,tlo,nums in rows:
 P=add(mul(T,T),scale(V,-Q));bp=bern(P,l,r);bt=bern(T,l,r)
 assert len(bp)==len(nums)
 gaps=[x-F(n,10**6) for x,n in zip(bp,nums)]+[x-tlo for x in bt]
 assert min(gaps)>0
 count+=len(gaps)
 report.append({'row':name,'P_degree':len(P)-1,'P_bounds':len(bp),'T_degree':len(T)-1,'T_bounds':len(bt),'minimum_exact_gap':str(min(gaps))})
print(json.dumps({'status':'PASS','independent_bounds':count,'rows':report},indent=2))
