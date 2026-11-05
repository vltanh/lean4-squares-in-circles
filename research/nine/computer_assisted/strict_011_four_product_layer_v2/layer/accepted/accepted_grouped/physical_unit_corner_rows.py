"""Original corner rows expanded using the same physical unit frame."""
from fractions import Fraction as F
Q=F(1105,256)
PREFIX='physical_unit_corner_'

def interval(raw):
    lo,hi=map(F,raw);assert lo<=hi
    return lo,hi

def projection(bx,by,a,b):
    return (min(a*bx[0],a*bx[1])+min(b*by[0],b*by[1]),
            max(a*bx[0],a*bx[1])+max(b*by[0],b*by[1]))

def row(positions,scalar,original,epsilon,tau,px,py,alpha_side,beta_side):
    assert len(positions)==18 and len(scalar)==36
    assert type(original)is int and 0<=original<9
    assert epsilon in(-1,1)and tau in(-1,1)
    assert alpha_side in(0,1)and beta_side in(0,1)
    px,py=F(px),F(py)
    bx,by=interval(positions[2*original]),interval(positions[2*original+1])
    alpha,beta=interval(scalar[original]),interval(scalar[9+original])
    rb,sb=projection(bx,by,epsilon,tau),projection(bx,by,-tau,epsilon)
    a0,r0=alpha[alpha_side],rb[alpha_side];b0,s0=beta[beta_side],sb[beta_side]
    co={2*original:2*px+epsilon*a0-tau*b0,2*original+1:2*py+tau*a0+epsilon*b0,
        18+original:r0,27+original:s0}
    rhs=Q-F(1,2)+px*px+py*py+a0*r0+b0*s0
    name=f'{PREFIX}{original}_{epsilon}_{tau}_{px}_{py}_{alpha_side}_{beta_side}'
    return tuple((k,v)for k,v in sorted(co.items())if v),rhs,name
