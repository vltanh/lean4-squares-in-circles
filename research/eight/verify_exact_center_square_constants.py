#!/usr/bin/env python3
"""Check the fixed rational sums in HAND_EXACT_CENTER_SQUARE_COMPLETION.

No interval cover, optimizer, root solver, or external proof-code import.
The geometric identities and Taylor bounds are proved in the companion note.
"""
from fractions import Fraction as F
import json


def main():
    w=F(4209,5000)
    X1,X4,Y2,X3,H1=F(17649,10000),F(19049,10000),F(221,200),F(6793,5000),F(14263,10000)
    zp=F(81,1000)
    sm=F(40,401)
    sp=2*zp/(1+zp*zp)
    cm=(1-zp*zp)/(1+zp*zp)
    tp=2*zp/(1-zp*zp)
    assert sm==2*F(1,20)/(1+F(1,20)**2)
    C2_terms=[w*X4/(2*sm),w*X1*tp/2,w*sp/2,w/2,3*w/4]
    C3_terms=[w*X1/cm/6,w*Y2/6,w*X3/6,w*H1/6,w/6,w/6,7*w/15]
    C2=sum(C2_terms)
    C3=sum(C3_terms)
    assert C2==F(26453303561590200213,2850910772000000000)<F(232,25)
    assert C3==F(25398850783,17277200000)<F(3,2)
    assert F(232,25)+F(3,2)/500==F(9283,1000)<F(93,10)
    midpoint=list(map(F,['.0345','.3633','.3211','.4102','.0760','.0425','.0238','.0371','.0549']))
    derivative=list(map(F,['2.04','2.16','1.27','1.51','1.53','1.52','.26','.33','.35']))
    inherited=[a-F(31,4000)*b for a,b in zip(midpoint,derivative)]
    printed=list(map(F,['.01869','.34656','.3112575','.3984975','.0641425','.03072','.021785','.0345425','.0521875']))
    assert inherited==printed
    assert min(inherited)==F(1869,100000)
    assert F(1869,100000)-F(93,10)/500==F(9,100000)>0
    # Width-sector and elementary center bounds used by the statement.
    assert F(1,10)-F(1,500)>0
    assert F(4,25)+F(1,500)<F(3,2)
    assert 2-F(1,2)==F(3,2)
    result={
        'status':'PASS',
        'scope':'fixed exact rational constants; geometry and Taylor bounds are in the hand note',
        'quadratic_terms':[str(x) for x in C2_terms],
        'cubic_terms':[str(x) for x in C3_terms],
        'quadratic_sum':str(C2),
        'cubic_sum':str(C3),
        'uniform_loss':'93/10 S^2 for S<=1/500',
        'minimum_inherited_reserve':str(min(inherited)),
        'final_positive_coefficient':'9/100000',
    }
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
