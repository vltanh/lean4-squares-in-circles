"""Necessary support rows for the center of an original unit square.
See HAND_PROOF.md. Rational discovery only; independent verification separate.
"""
from fractions import Fraction as F
from itertools import product
PREFIX='physical_rotating_frame_center_cone_'
K=F(30,121)
CAP=F(352321,232320)

def guard(interval,axis,sign,nx,ny):
 lo,hi=map(F,interval)
 assert -1<=lo<=hi<=1 and axis in (0,1) and sign in (-1,1)
 nx,ny=F(nx),F(ny)
 major=(sign*nx,sign*ny) if axis==0 else (sign*ny,-sign*nx)
 minor=(ny,-nx) if axis==0 else (nx,ny)
 return all(major[0]+major[1]*z>0 and abs(minor[0]+minor[1]*z)<=K*(major[0]+major[1]*z) for z in (lo,hi))

def row(angles,owner,axis,sign,nx,ny):
 assert type(owner)is int and 0<=owner<9 and axis in (0,1) and sign in (-1,1)
 nx,ny=F(nx),F(ny);assert (nx,ny)!=(0,0) and guard(angles[owner],axis,sign,nx,ny)
 a,b=(sign*nx,sign*ny) if axis==0 else (sign*ny,-sign*nx)
 coefficients={2*owner:nx,2*owner+1:ny,18+owner:-CAP*a,27+owner:-CAP*b}
 return tuple((j,c)for j,c in sorted(coefficients.items())if c),F(0),PREFIX+'_'.join(map(str,(owner,axis,sign,nx,ny)))

def generate(angles):
 directions=set()
 for j in range(-8,9):
  q=F(j,8);directions.update(((F(1),q),(-q,F(1)),(F(-1),-q),(q,F(-1))))
 answer=[]
 for owner,(lo,hi)in enumerate(angles):
  midpoint=(lo+hi)/2
  candidates=directions|{(F(1),midpoint),(-midpoint,F(1)),(F(-1),-midpoint),(midpoint,F(-1))}
  for nx,ny in sorted(candidates):
   for axis,sign in product((0,1),(-1,1)):
    if guard((lo,hi),axis,sign,nx,ny):answer.append(row(angles,owner,axis,sign,nx,ny))
 return answer
