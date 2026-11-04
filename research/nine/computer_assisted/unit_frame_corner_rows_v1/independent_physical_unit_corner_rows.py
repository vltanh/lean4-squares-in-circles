"""Direct rectangle-residual expansion, with no producer imports."""
from fractions import Fraction as F
from itertools import product
PREFIX='physical_unit_corner_'

def verify_literal(literal,positions,scalar):
    co,rhs,name=literal;assert name.startswith(PREFIX)
    fields=name[len(PREFIX):].split('_');assert len(fields)==7
    i,e,t=map(int,fields[:3]);px,py=map(F,fields[3:5]);aside,bside=map(int,fields[5:])
    assert 0<=i<9 and e in(-1,1)and t in(-1,1)and aside in(0,1)and bside in(0,1)
    assert len(positions)==18 and len(scalar)==36
    boxes=[tuple(map(F,z))for z in(positions[2*i],positions[2*i+1],scalar[i],scalar[9+i])]
    assert all(len(z)==2 and z[0]<=z[1]for z in boxes)
    bx,by,alpha,beta=boxes
    rv=[e*x+t*y for x,y in product(bx,by)];sv=[e*y-t*x for x,y in product(bx,by)]
    a0=alpha[aside];b0=beta[bside];r0=min(rv)if aside==0 else max(rv);s0=min(sv)if bside==0 else max(sv)
    answer={}
    for k,v in((2*i,2*px),(2*i+1,2*py),(2*i,a0*e),(2*i+1,a0*t),(18+i,r0),
               (2*i+1,b0*e),(2*i,-b0*t),(27+i,s0)):
        answer[k]=answer.get(k,F(0))+v
    expected=tuple((k,v)for k,v in sorted(answer.items())if v)
    assert co==expected
    assert F(rhs)-px*px-py*py-a0*r0-b0*s0==F(977,256)
    return literal
