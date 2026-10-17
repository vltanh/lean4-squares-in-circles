from fractions import Fraction as F
from math import comb,factorial
import json
def add(a,b):
 c=[F(0)]*max(len(a),len(b))
 for i,x in enumerate(a):c[i]+=x
 for i,x in enumerate(b):c[i]+=x
 return c
def scale(a,s):return [x*s for x in a]
def mul(a,b):
 c=[F(0)]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return c
def trig(n,cosine):
 a=[F(0)]*(n+1)
 for i in range(0 if cosine else 1,n+1,2):a[i]=F((-1)**(i//2),factorial(i))
 return a
g=F("1.077372");u=F(".569472");v=F(".390886");beta=F(".18")
R=F("1.978788");k=F(355,452)+(u-v)*F(".899215");gam=F(".8833")
B=beta/2-k+(-u+v+g)/2-gam
B0=B+F(".914")*R;B2=beta/2+F(".35")*R;C0=g-F("1.204902")*R
S7=trig(7,False);S9=trig(9,False);C6=trig(6,True);C8=trig(8,True)
P=add(add(add(mul([B0,F(1)],S7),scale(mul(S9,S9),-B2)),scale(mul(S9,C8),-beta/2)),add([C0],scale(C6,13*g/12)))
n=18;l=F(3,4);w=F(3,4)
pt=[sum((P[j]*comb(j,i)*l**(j-i)*w**i for j in range(i,len(P))),F(0)) for i in range(n+1)]
bb=[]
for j in range(n+1):
 prior=sum((bb[i]*comb(n,i)*comb(n-i,j-i)*(-1)**(j-i) for i in range(j)),F(0))
 bb.append((pt[j]-prior)/comb(n,j))
listed=[34281,45678,53640,59000,62526,64903,66706,68387,70249,72436,74913,77453,79629,80800,80112,76492,68645,55061,34020]
assert all(x>F(y,10**7) for x,y in zip(bb,listed))
out={"status":"PASS","method":"Independent polynomial assembly from note formulas; direct triangular solving in the Bernstein basis, not author's coefficient-transform formula.","degree":n,"coefficients":list(map(str,bb)),"listed_lower_numerators":listed,"minimum":float(min(bb))}
print(json.dumps(out,indent=2))

