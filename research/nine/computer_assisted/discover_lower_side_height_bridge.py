from fractions import Fraction as F
from math import sqrt
import json,time
from pathlib import Path
class I:
 def __init__(self,l,u=None):self.l=float(l);self.u=self.l if u is None else float(u)
 def __add__(a,b):b=iv(b);return I(a.l+b.l,a.u+b.u)
 __radd__=__add__
 def __neg__(a):return I(-a.u,-a.l)
 def __sub__(a,b):return a+-iv(b)
 def __rsub__(a,b):return iv(b)+-a
 def __mul__(a,b):b=iv(b);v=[a.l*b.l,a.l*b.u,a.u*b.l,a.u*b.u];return I(min(v),max(v))
 __rmul__=__mul__
 def __truediv__(a,b):b=iv(b);assert b.l>0;return a*I(1/b.u,1/b.l)
 def __rtruediv__(a,b):return iv(b)/a
 def square(a):return I(0 if a.l<=0<=a.u else min(a.l*a.l,a.u*a.u),max(a.l*a.l,a.u*a.u))
 def rt(a):return I(sqrt(max(0,a.l)),sqrt(max(0,a.u)))
 def ab(a):return I(max(0,a.l,-a.u),max(abs(a.l),abs(a.u)))
def iv(a):return a if isinstance(a,I) else I(a)
def mn(*xs):xs=list(map(iv,xs));return I(min(a.l for a in xs),min(a.u for a in xs))
def mx(*xs):xs=list(map(iv,xs));return I(max(a.l for a in xs),max(a.u for a in xs))
def frame(H):
 k=(I(.5)-H.square()).rt();a=I(H.u+sqrt(.5-H.u**2),H.l+sqrt(.5-H.l**2));b=I(H.l-sqrt(.5-H.l**2),H.u-sqrt(.5-H.u**2));g=1/(4*H);eta=I(H.l+1/(4*H.l)-1,H.u+1/(4*H.u)-1);return a,b,g,eta

def vals(box,rid):
 h,K=[I(float(l),float(u))for l,u in box];a,b,g,e=frame(h);A,B,G,E=frame(K);V=e+E
 d=mn(61/30-h-K,h+K);s=1+(h-K).ab()
 gap=mx((s.square()-d.square()).rt(),mn(*[(s-c*d)/mx(z,1/40)for c,z in [(a,b),(b,a),(A,B),(B,A)]]))
 M=G+e-199/120+(32/9)*V
 target=3*h-2.11 if rid==0 else I(-.25)
 return [1/30-V,target-M-gap]

def main():
 roots=[[(F(57,100),F(31,50)),(F(1,2),F(13,20))],[(F(31,50),F(13,20)),(F(1,2),F(13,20))]]
 cert=[];reports=[]
 for rid,root in enumerate(roots):
  stack=[(root,0)];ev=[];leaves=0;maxdepth=0
  while stack:
   box,dep=stack.pop();maxdepth=max(dep,maxdepth);v=vals(box,rid);rule=min(range(2),key=lambda j:v[j].u)
   if v[rule].u < -1e-8:ev.append(-rule-1);leaves+=1;continue
   if dep>=70:raise Exception(('failed',box,[q.u for q in v]))
   widths=[float(u-l)for l,u in box];j=max(range(2),key=lambda j:widths[j]);l,u=box[j];mid=(l+u)/2;left=list(box);right=list(box);left[j]=(l,mid);right[j]=(mid,u);ev.append(j);stack.extend([(right,dep+1),(left,dep+1)])
  cert.append(ev);reports.append(dict(leaves=leaves,nodes=len(ev),depth=maxdepth));print(rid,reports[-1],flush=True)
 Path('lower_side_height_bridge.json').write_text(json.dumps(dict(schema='lower_side_height_bridge_v1',roots=[[[str(l),str(u)]for l,u in r]for r in roots],events=cert,discovery=reports),separators=(',',':'))+'\n')
if __name__=='__main__':main()
