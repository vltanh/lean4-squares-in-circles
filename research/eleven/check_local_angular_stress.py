#!/usr/bin/env python3
"""Exact first-order angular stress margins for the physical local problem.

Proof and scope: LOCAL_OPTIMALITY.md. No floating-point feasibility is used.
"""
from fractions import Fraction as F
from contact_family import family
from isolate_contact_root import I, certificate
from check_fixed_orientation_stress import stress_certificate

if not __debug__:
    raise RuntimeError('Run without -O: this certificate uses assertions.')


def angular_certificate():
    weight_bounds=stress_certificate()
    weights=[I(z.lo,z.hi) for z in weight_bounds]
    box=certificate()
    _,p,angles,extra=family(box[0],box[1],lambda x:x.sqrt())
    (ca,sa),(cb,sb)=angles
    r,_,_,_=extra
    a,b=p[0];k=(1+ca+sa)/2
    H=(k+1-r-sa*(b-1))/ca
    # A slightly larger interval than the entire slider range; this also
    # supports the endpoint argument in the local equality proof.
    p[1]=(I(H.lo-F(1,10000),a.hi+F(1,10000)),b-1)
    ex,ey=(I(1),I(0)),(I(0),I(1))
    ua,va=(ca,sa),(-sa,ca);ub,vb=(cb,sb),(-sb,cb)
    frames=[(ex,ey)]*7+[(ua,va)]*2+[(ub,vb)]*2
    dot=lambda x,y:sum(u*v for u,v in zip(x,y))
    rot=lambda x:(-x[1],x[0])
    neg=lambda x:tuple(-z for z in x)
    angular=[I(0) for _ in range(11)]
    disks=[(0,1,1),(2,1,1),(3,1,-1),(5,1,-1),(6,-1,-1),(7,-1,-1),(7,-1,1),(9,-1,1),(10,-1,1),(10,1,1)]
    assert len(disks)==10
    for weight,(i,eps,eta) in zip(weights[:10],disks):
        u,v=frames[i]
        offset=tuple((eps*u[k]+eta*v[k])/2 for k in range(2))
        vertex=tuple(p[i][k]+offset[k] for k in range(2))
        contribution=weight*(-2*dot(vertex,rot(offset)))
        angular[i]+=contribution
    # i, j, owner, owner axis, sign, common frame?
    edges=[(0,1,0,1,-1,True),(0,2,0,0,1,True),
           (0,10,0,0,-1,False),(1,4,1,1,-1,True),
           (2,3,2,1,-1,True),(3,4,3,0,-1,True),
           (4,5,4,1,-1,True),(4,8,4,0,-1,False),
           (5,6,5,0,-1,True),(6,7,7,1,1,False),
           (7,8,7,0,1,True),(7,9,7,1,1,False),
           (8,9,9,1,1,False),(9,10,9,0,1,True)]
    capacities={}
    alternate_count=0
    for weight,(i,j,owner,axis,sign,parallel) in zip(weights[10:],edges):
        n=tuple(sign*z for z in frames[owner][axis])
        delta=tuple(p[j][k]-p[i][k] for k in range(2))
        tau=dot(rot(n),delta)
        if parallel:
            angular[i]+=weight*tau/2;angular[j]+=weight*tau/2
            assert tau.abs_upper()<1
            capacities[i,j]=weight*(1-abs(tau))/2
        else:
            cosine=dot(frames[i][0],frames[j][0])
            sine=dot(frames[i][1],frames[j][0])
            assert cosine.lo>0 and sine.lo>0
            width_derivative=(cosine-sine)/2
            angular[i]+=weight*width_derivative
            angular[j]-=weight*width_derivative
            angular[owner]+=weight*tau
            # The selected owner axis is the only possible physical axis
            # at the contact. Every alternative unoriented owner axis fails.
            for k in [i,j]:
                for ell in [0,1]:
                    if (k,ell)==(owner,axis):continue
                    alternate=frames[k][ell]
                    support=sum(abs(dot(alternate,vector)) for l in [i,j] for vector in frames[l])/2
                    slack=abs(dot(alternate,delta))-support
                    assert slack.hi < -F(1,100),(i,j,k,ell)
                    alternate_count+=1
    flow={(0,1):-angular[0],(0,2):I(0),(1,4):-angular[0]-angular[1],
          (2,3):-angular[2],(3,4):-angular[2]-angular[3],
          (4,5):angular[5]+angular[6],(5,6):angular[6],
          (7,8):angular[8],(9,10):angular[10]}
    assert flow.keys()==capacities.keys() and len(flow)==9 and alternate_count==15
    for edge in flow:
        assert capacities[edge].lo-flow[edge].abs_upper() > F(1,100),edge
    # These balances are exact consequences of the dual equations and global
    # rotation invariance, as proved in the note; interval containment is a
    # consistency check, not a substitute for that algebraic argument.
    for group in [range(7),range(7,9),range(9,11)]:
        balance=sum(angular[i] for i in group)
        assert balance.lo<=0<=balance.hi
    print('PASS: all nine parallel-contact angular flow margins exceed 1/100.')
    print('PASS: all fifteen alternative axes for the five nonparallel contacts have slack < -1/100.')
    print('PASS: every parallel pair shares a positive edge segment throughout the enlarged slider interval.')
    print('Exact group-balance identities come from the dual equations and rotation invariance.')
    print('Conclusion requires the directional-derivative and compactness argument in LOCAL_OPTIMALITY.md.')


if __name__=='__main__':angular_certificate()
