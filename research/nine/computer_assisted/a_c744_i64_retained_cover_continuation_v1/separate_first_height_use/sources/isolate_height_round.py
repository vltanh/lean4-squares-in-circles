"""Exact proposal construction using one accepted height row and current box rows.

The independent unchanged CORE verifies each resulting ordinary certificate.
"""
from copy import deepcopy
from fractions import Fraction as F
import attachment as A
import original_i64_bound_rows as PRODUCER

def construct(state,adapter,eps=F(1,2000)):
    K=adapter.K
    base,bounds,pos,scalar,diffs,guards=K.rebuild(state['path'],state['angles'],state['positions'],state['choices'],state['scalar'],state['differences'])
    _,actual_bounds,physical=adapter.rebuild(state,[])
    assert tuple(bounds)==tuple(actual_bounds)
    assert tuple(pos)==physical['positions']and tuple(scalar)==physical['scalar']and diffs==physical['differences']
    height=PRODUCER.necessary_height_row(state)
    assert height==(((3,F(1)),(7,F(1)),(17,F(-2))),F(-16,25),A.ROWS.HEIGHT_NAME)
    rows=list(base)+[height];height_index=len(base)
    endpoints={}
    for index,(co,rhs,name)in enumerate(base):
        canonical={}
        for k,v in co:canonical[k]=canonical.get(k,F(0))+F(v)
        co=tuple((k,v)for k,v in sorted(canonical.items())if v)
        if len(co)==1 and co[0][1]in(-1,1):
            key=co[0];candidate=(F(rhs),index)
            if key not in endpoints or candidate<endpoints[key]:endpoints[key]=candidate
    positions=[list(x)for x in physical['positions']];proposals=[];used=set()
    for target,a in height[0]:
        multiplier=1/abs(a);weights={height_index:multiplier}
        for k,c in height[0]:
            if k==target:continue
            sign=-1 if c>0 else 1
            rhs,index=endpoints[k,F(sign)]
            assert rhs<=(-physical['positions'][k][0]if sign<0 else physical['positions'][k][1])
            weights[index]=weights.get(index,F(0))+abs(c)*multiplier
        exact_weights=[];co={};rhs=F(0)
        for index,lam in sorted(weights.items()):
            integer=lam*A.CORE.DENOMINATOR;assert integer.denominator==1 and integer>0
            exact_weights.append([index,integer.numerator]);row,bound,_=rows[index];rhs+=lam*bound
            for k,c in row:co[k]=co.get(k,F(0))+lam*c
        sign=1 if a>0 else-1;objective=[[target,sign]]
        assert {k:v for k,v in co.items()if v}=={target:F(sign)}
        upper=A.CORE.ceiling_grid(rhs)
        previous=physical['positions'][target][1]if sign>0 else-physical['positions'][target][0]
        if previous-upper<eps:continue
        proposals.append(dict(kind='scalar',key=target,sign=sign,objective=objective,upper=str(upper),proved_upper=str(rhs),
            weights=exact_weights,summed_rhs=str(rhs),residual_coefficients=[],residual_correction='0'))
        used.update(weights)
        if sign>0:positions[target][1]=min(positions[target][1],upper)
        else:positions[target][0]=max(positions[target][0],-upper)
    printed=[dict(index=k,coefficients=[[i,str(c)]for i,c in rows[k][0]],rhs=str(rows[k][1]),name=rows[k][2])for k in sorted(used)]
    record=dict(before=A.CORE.state_view(state),propagated=A.CORE.state_view(physical),proposals=proposals,
        printed_rows=printed,absolute_variable_bounds=list(map(str,bounds)),numeric_failures=0,
        exact_height_row_isolation=True,numerical_solves=0)
    positions=tuple(map(tuple,positions));scalar=physical['scalar']
    assert all(lo<=hi for lo,hi in positions+scalar)
    angles,terminal,identities=adapter.infer_angles(state['angles'],scalar);assert terminal is None
    record['physical_frame_inferences']=identities
    scalar=tuple((max(a,c),min(b,d))for(a,b),(c,d)in zip(scalar,adapter.analytic(angles)))
    assert all(lo<=hi for lo,hi in scalar)
    after=dict(deepcopy(physical),positions=positions,scalar=scalar,angles=angles)
    record['after']=A.CORE.state_view(after)
    return record,after
