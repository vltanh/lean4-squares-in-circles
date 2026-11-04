"""Numerical suggestions for exact shared-normal center-gap square rows."""
from fractions import Fraction as F
import numpy as np
import physical_projection_squares as P

def gram(point,pair,choice,slot,differences):
    i,j=pair;owner,axis,sign=choice;aa,bb=point[18+owner],point[27+owner]
    nx,ny=(sign*aa,sign*bb)if axis==0 else(-sign*bb,sign*aa)
    dx,dy=point[2*j]-point[2*i],point[2*j+1]-point[2*i+1]
    upper=sum(float(lo+hi)*v-float(lo*hi)for(lo,hi),v in zip(differences[pair],(dx,dy)))
    z=54+6*slot;projection=point[z]+point[z+1]
    return np.array(((1,0,nx,dx),(0,1,ny,dy),(nx,ny,1,projection),(dx,dy,projection,upper)))

def violated_parameters(point,choices,differences,tolerance=5e-5,denominator=1<<14):
    result=[]
    for slot,(pair,choice)in enumerate(P.selections(choices)):
        eigenvalues,eigenvectors=np.linalg.eigh(gram(point,pair,choice,slot,differences))
        if eigenvalues[0]>=-tolerance:continue
        q=tuple(F(int(round(float(v)*denominator)),denominator)for v in eigenvectors[:,0])
        row=P.row(choices,differences,slot,q)
        violation=sum(float(v)*point[k]for k,v in row[0])-float(row[1])
        if violation>tolerance:result.append((slot,q,float(eigenvalues[0]),violation))
    return result
