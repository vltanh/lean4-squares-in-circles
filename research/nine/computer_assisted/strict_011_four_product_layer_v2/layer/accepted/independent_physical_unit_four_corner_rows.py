"""Independent four-rectangle residual expansion on the original caller."""
from fractions import Fraction as F
PREFIX='physical_unit_four_corner_'

def verify_literal(literal,positions,scalar):
    coefficients,rhs,name=literal;assert name.startswith(PREFIX)
    fields=name[len(PREFIX):].split('_');assert len(fields)==9
    i,e,t=map(int,fields[:3]);px,py=map(F,fields[3:5]);bits=tuple(map(int,fields[5:]))
    assert 0<=i<9 and e in(-1,1)and t in(-1,1)and all(k in(0,1)for k in bits)
    assert len(positions)==18 and len(scalar)==36
    x=tuple(map(F,positions[2*i]));y=tuple(map(F,positions[2*i+1]))
    alpha=tuple(map(F,scalar[i]));beta=tuple(map(F,scalar[9+i]))
    assert all(len(b)==2 and b[0]<=b[1]for b in(x,y,alpha,beta))
    signed_boxes=[sorted(e*z for z in x),sorted(t*z for z in y),
                  sorted(e*z for z in y),sorted(-t*z for z in x)]
    frame_boxes=[alpha,alpha,beta,beta]
    frame_columns=[18+i,18+i,27+i,27+i]
    coordinate_columns=[2*i,2*i+1,2*i+1,2*i]
    coordinate_signs=[e,t,e,-t]
    answer={2*i:2*px,2*i+1:2*py};constant=px*px+py*py
    for j in range(4):
        chosen=bits[j];f0=frame_boxes[j][chosen];g0=signed_boxes[j][chosen]
        c=coordinate_columns[j];f=frame_columns[j]
        answer[c]=answer.get(c,F(0))+coordinate_signs[j]*f0
        answer[f]=answer.get(f,F(0))+g0;constant+=f0*g0
    expected=tuple((k,v)for k,v in sorted(answer.items())if v)
    assert tuple(coefficients)==expected
    assert F(rhs)-constant==F(977,256)
    return literal
