import math
from fractions import Fraction

def family(q,t,sqrt=math.sqrt):
 r=sqrt(q-Fraction(1,4))-Fraction(1,2)
 w=sqrt(q-Fraction(9,4))-Fraction(1,2)
 v=2*(w-1)/(3+sqrt(9+4*w*(w-1)))
 ca=(1-t*t)/(1+t*t);sa=2*t/(1+t*t)
 cd=(1-v*v)/(1+v*v);sd=2*v/(1+v*v)
 cb=ca*cd-sa*sd;sb=sa*cd+ca*sd
 ka=(1+ca+sa)/2;kb=(1+cb+sb)/2
 kd=(1+cd+sd)/2
 z=(w-kd+(1-r)*sd)/cd
 a=kb-r*sb
 b=sqrt(q-(a+Fraction(1,2))**2)-Fraction(1,2)
 d=sqrt(q-(a+Fraction(3,2))**2)-Fraction(1,2)
 e=sqrt(q-(d-Fraction(3,2))**2)-Fraction(1,2)
 f=sqrt(q-(b-Fraction(7,2))**2)-Fraction(1,2)
 g=Fraction(1,2)-sqrt(q-(f-Fraction(3,2))**2)
 p7=(-r*ca,-r*sa)
 p8=((1-r)*ca-z*sa,(1-r)*sa+z*ca)
 p9=(-cb-w*sb,-sb+w*cb)
 p10=(-r*sb,r*cb)
 p=[(a,b),(Fraction(12,37),b-1),(a+1,d),(e,d-1),(e-1,b-2),(f,b-3),(f-1,g),p7,p8,p9,p10]
 F=(e-1-ka-p8[0],sa*(f-1)-ca*g-ka)
 return F,p,((ca,sa),(cb,sb)),(r,w,v,z)
