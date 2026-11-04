"""Untrusted numerical suggestions for exact physical frame square rows."""
from fractions import Fraction as F
import numpy as np
import physical_pair_frame_squares as S

def gram(point,pair,slot):
    i,j=pair;z=54+6*slot;c=point[z+2]+point[z+3];s=point[z+4]-point[z+5]
    g=np.eye(6)
    for u,o in((2,i),(4,j)):
        a,b=point[18+o],point[27+o]
        for x,y,v in((0,u,a),(1,u,b),(0,u+1,-b),(1,u+1,a)):g[x,y]=g[y,x]=v
    for x,y,v in((2,4,c),(2,5,-s),(3,4,s),(3,5,c)):g[x,y]=g[y,x]=v
    return g

def violated_parameters(point,choices,tolerance=5e-5,denominator=1<<14):
    result=[]
    for slot,pair in enumerate(S.selected(choices)):
        eigenvalues,eigenvectors=np.linalg.eigh(gram(point,pair,slot))
        if eigenvalues[0]>=-tolerance:continue
        q=tuple(F(int(round(float(v)*denominator)),denominator)for v in eigenvectors[:,0])
        row=S.row(choices,slot,q)
        violation=sum(float(v)*point[k]for k,v in row[0])-float(row[1])
        if violation>tolerance:result.append((slot,q,float(eigenvalues[0]),violation))
    return result
