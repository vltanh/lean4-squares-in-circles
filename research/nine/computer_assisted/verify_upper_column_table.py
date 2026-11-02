"""Exact arithmetic reconstruction of the five-row upper-column theorem."""
import json
from fractions import Fraction as F
from pathlib import Path

def verify():
    Q=F(1105,256)
    rho=F(91,60)
    assert rho*rho+rho+F(1,2)-Q==F(31,57600)>0
    assert F(133,64)**2-Q==F(9,4096)>0
    assert F(17,24)**2>F(1,2)
    endpoints=list(map(F,['1/2','23/40','3/5','5/8','13/20','17/24']))
    expected=list(map(F,['14693/952200','1643/184320','13319/921600','3232367/155750400','1917191/266342400']))
    rows=[]
    for a,b,res in zip(endpoints,endpoints[1:],expected):
        assert a<b
        g=1/(4*b)
        ymax=min(rho,F(133,64)-a)
        dx=max(F(29,60)-g,F(0))
        dy=max(ymax-F(3,5)-g,F(0))
        actual=F(1,4)-dx*dx-dy*dy
        assert actual==res and actual>0
        rows.append(dict(h_interval=[str(a),str(b)],g_lower=str(g),center_height_upper=str(ymax),reserve=str(actual)))
    assert rho-F(3,5)==F(11,12)<1
    return dict(status='PASS',arithmetic='Python Fraction exact rational arithmetic',rows=rows,scope='Upper-column pair theorem and arithmetic constants; not a mask closure')

if __name__=='__main__':
    result=verify()
    path=Path(__file__).with_name('upper_column_table_replay.json')
    path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result))
