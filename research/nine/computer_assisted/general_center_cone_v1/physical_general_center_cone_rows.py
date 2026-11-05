"""General rational center support from the four original physical corners.
See GENERAL_CENTER_CONE_HAND_PROOF.md. Independent decoder is separate.
"""
from fractions import Fraction as F
from itertools import product
PREFIX='physical_general_center_cone_'
PARAMETERS=((F(31,32),F(31,32)),(F(5,4),F(1,2)),(F(9,8),F(3,4)),(F(11,8),F(3,8)))
def guard(interval,axis,sign,nx,ny,r,s):
 lo,hi=map(F,interval);nx,ny,r,s=map(F,(nx,ny,r,s))
 assert -1<=lo<=hi<=1 and axis in(0,1)and sign in(-1,1)and r>=s>=0
 k=(2*s+1)/(2*r+1)
 major=(sign*nx,sign*ny)if axis==0 else(sign*ny,-sign*nx)
 minor=(ny,-nx)if axis==0 else(nx,ny)
 return all(major[0]+major[1]*z>0 and abs(minor[0]+minor[1]*z)<=k*(major[0]+major[1]*z)for z in(lo,hi))
def row(angles,owner,axis,sign,nx,ny,r,s):
 assert type(owner)is int and 0<=owner<9
 nx,ny,r,s=map(F,(nx,ny,r,s));assert(nx,ny)!=(0,0)
 assert guard(angles[owner],axis,sign,nx,ny,r,s)
 cap=(F(977,256)+r*r+s*s)/(2*r+1)
 a,b=(sign*nx,sign*ny)if axis==0 else(sign*ny,-sign*nx)
 terms={2*owner:nx,2*owner+1:ny,18+owner:-cap*a,27+owner:-cap*b}
 return tuple((j,c)for j,c in sorted(terms.items())if c),F(0),PREFIX+'_'.join(map(str,(owner,axis,sign,nx,ny,r,s)))
def generate(angles):
 directions=set()
 for j in range(-8,9):
  q=F(j,8);directions.update(((F(1),q),(-q,F(1)),(F(-1),-q),(q,F(-1))))
 answer=[]
 for owner,interval in enumerate(angles):
  lo,hi=map(F,interval);mid=(lo+hi)/2
  choices=directions|{(F(1),mid),(-mid,F(1)),(F(-1),-mid),(mid,F(-1))}
  for r,s in PARAMETERS:
   for nx,ny in sorted(choices):
    for axis,sign in product((0,1),(-1,1)):
     if guard((lo,hi),axis,sign,nx,ny,r,s):answer.append(row(angles,owner,axis,sign,nx,ny,r,s))
 return answer
