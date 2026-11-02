"""Exact reconstruction of the central-transfer quartic and all 15 row entries."""
from fractions import Fraction as F
from math import comb
from pathlib import Path
import json

def verify():
    k=F(133,64)-F(29,27)
    assert k==F(1735,1728)
    right=[k,F(8,9),k-F(1,9)]
    square=[sum((right[i]*right[j] for i in range(3) for j in range(3) if i+j==n),F(0)) for n in range(5)]
    left=list(map(F,[1,2,2,2,1]))
    coefficients=[a-b for a,b in zip(left,square)]
    assert [a*2985984 for a in coefficients]==list(map(F,[-24241,642048,-1741538,1231872,605135]))
    rows=[(F(1,16),F(1,4),195689447424,[615651791,1965435452,2740609520,3090554816,3213668096]),
          (F(1,4),F(1,2),2293235712,[37660173,39583818,36781796,34765128,40860240]),
          (F(1,2),F(1),143327232,[2553765,3315654,6105488,14586480,34237248])]
    report=[]
    for a,b,den,num in rows:
        q=[sum((coefficients[m]*comb(m,j)*a**(m-j)*(b-a)**j for m in range(j,5)),F(0))for j in range(5)]
        beta=[sum((q[j]*F(comb(i,j),comb(4,j))for j in range(i+1)),F(0))for i in range(5)]
        assert beta==[F(n,den)for n in num] and min(beta)>0
        report.append(dict(interval=[str(a),str(b)],denominator=den,numerators=num))
    reserves={
        'both_large_at_2':F(2)**2+4-(F(7,9)+2*k)**2,
        'both_large_at_16':F(16)**2+32-(F(7,9)+16*k)**2,
        'small_u':F(1,9)-(F(7,1728)+F(1,512))*F(257,16),
        'mixed_negative_sum_16':F(1,9)-F(7,1728)*16,
        'large_tail':F(31,540)*16-F(8,9),
    }
    assert reserves['both_large_at_2']==F(178319,746496)
    assert reserves['both_large_at_16']==F(50471,11664)
    assert reserves['small_u']==F(3245,221184)
    assert reserves['mixed_negative_sum_16']==F(5,108)
    assert reserves['large_tail']==F(4,135)
    assert min(reserves.values())>0
    return dict(status='PASS',quartic_numerators=[-24241,642048,-1741538,1231872,605135],
                quartic_denominator=2985984,bernstein_rows=report,
                positive_reserves={k:str(v)for k,v in reserves.items()},
                scope='Exact scalar arithmetic only; full physical and unbounded-case coverage is in the reviewed hand manuscript')

if __name__=='__main__':
    result=verify()
    Path(__file__).with_name('piecewise_central_bernstein_replay.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
