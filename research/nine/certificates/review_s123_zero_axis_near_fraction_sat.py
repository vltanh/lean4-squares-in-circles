"""Independent exact-Fraction SAT audit of the three fixed occupied
rectangles. No author interval implementation is imported.
"""
from fractions import Fraction as F
from collections import Counter

class B:
    def __init__(self,lo,hi=None):
        self.lo=F(lo);self.hi=self.lo if hi is None else F(hi)
        assert self.lo<=self.hi
    def __add__(a,b):
        b=box(b);return B(a.lo+b.lo,a.hi+b.hi)
    __radd__=__add__
    def __neg__(a):return B(-a.hi,-a.lo)
    def __sub__(a,b):return a+-box(b)
    def __rsub__(a,b):return box(b)+-a
    def __mul__(a,b):
        b=box(b);p=[a.lo*b.lo,a.lo*b.hi,a.hi*b.lo,a.hi*b.hi]
        return B(min(p),max(p))
    __rmul__=__mul__
    def __truediv__(a,b):
        b=box(b);assert b.lo>0
        return a*B(1/b.hi,1/b.lo)
def box(x):return x if isinstance(x,B) else B(x)
rects=[
 (F(-99,100),0,F(-23,1000),F(3,4)),
 (F(1,7000),1,F(-1,2),F(1,2)),
 (F(-7,4),F(-199,200),F(-9,20),F(-1,4))]
def check(row):
    a,b,z=[B(*v) for v in row]
    c=B((1-z.hi*z.hi)/(1+z.hi*z.hi),(1-z.lo*z.lo)/(1+z.lo*z.lo))
    s=B(2*z.lo/(1+z.lo*z.lo),2*z.hi/(1+z.hi*z.hi))
    X=a*c-b*s;Y=a*s+b*c;r=(c+s)/2
    for i,(xl,xh,yl,yh) in enumerate(rects):
        ru0=xl*c+yl*s;ru1=xh*c+yh*s
        rv0=yl*c-xh*s;rv1=yh*c-xl*s
        gaps=[X+r-xl,xh-X+r,Y+r-yl,yh-Y+r,a+F(1,2)-ru0,ru1-a+F(1,2),b+F(1,2)-rv0,rv1-b+F(1,2)]
        low=min(v.lo for v in gaps)
        if low>0:return i,low
    return None
def run():
    root=((F(-5,8),F(5,8)),(F(-5,8),F(5,8)),(F(0),F(1)))
    stack=[(root,0)];count=Counter();mins=[F(1)]*3;depth=visited=0
    while stack:
        row,dep=stack.pop();visited+=1;res=check(row)
        if res is not None:
            i,low=res;count[i]+=1;mins[i]=min(mins[i],low);depth=max(depth,dep);continue
        assert dep<70
        widths=[row[0][1]-row[0][0],row[1][1]-row[1][0],F(5,4)*(row[2][1]-row[2][0])]
        j=max(range(3),key=lambda i:widths[i])
        lo,hi=row[j];mid=(lo+hi)/2
        left=list(row);right=list(row);left[j]=(lo,mid);right[j]=(mid,hi)
        stack.append((tuple(right),dep+1));stack.append((tuple(left),dep+1));count['split']+=1
    assert count==Counter({'split':876,0:92,1:388,2:397})
    assert visited==1753 and depth==27
    floor48=[(v.numerator*(1<<48))//v.denominator for v in mins]
    print('PASS exact Fraction',dict(count),'visited',visited,'depth',depth)
    print('positive lower numerators over2^48',floor48)
    return count,mins
if __name__=='__main__':run()

