"""Exact guards for the established positive-D two-link row terminal.

Prerequisite: the unchanged strict original-nine 001/00 caller, normalized
with y_D-y_C >= 2/3, and exact ancestry for every supplied bound.  This helper
checks the existing theorem's quantitative hypotheses, not caller ancestry
or complete original coverage.  The existing theorem allows every original
frame angle and every physical separating owner.
"""
from fractions import Fraction as F
from itertools import product

EXTRAS=(7,8)
THRESHOLD=F(1,2)

def box(raw):
    ans=tuple(tuple(F(x)for x in pair)for pair in raw)
    assert all(len(p)==2 and p[0]<=p[1]for p in ans)
    return ans

def unpack(state):
    p=box(state['positions']); a=box(state['angles']); s=box(state['scalar'])
    assert len(p)==18 and len(a)==9 and len(s)==36
    raw=state.get('differences',{})
    d=({tuple(r['pair']):box(r['intervals'])for r in raw}if isinstance(raw,list)
       else {tuple(k):box(v)for k,v in raw.items()})
    return p,a,s,d

def diff(p,d,i,j,axis):
    lo=p[2*j+axis][0]-p[2*i+axis][1]
    hi=p[2*j+axis][1]-p[2*i+axis][0]
    if i<j and(i,j)in d:
        x,y=d[i,j][axis];lo=max(lo,x);hi=min(hi,y)
    elif i>j and(j,i)in d:
        x,y=d[j,i][axis];lo=max(lo,-y);hi=min(hi,-x)
    assert lo<=hi
    return lo,hi

def upper(terms,p):
    return sum(v*p[k][1 if v>0 else 0]for k,v in terms)

def height_expressions(extra):
    assert extra in EXTRAS
    ans=[]
    for s,t in product((-1,1),repeat=2):
        co={3:-F(s),2*extra+1:F(s-t),7:F(t)}
        ans.append(tuple(sorted((k,v)for k,v in co.items()if v)))
    return tuple(ans)

def complement_rows(extra):
    assert extra in EXTRAS
    out=[(((2*extra,F(1)),(2,F(-1))),F(0),'positive_D_row_X_left_'+str(extra)),
         (((6,F(1)),(2*extra,F(-1))),F(0),'positive_D_row_X_right_'+str(extra))]
    for n,terms in enumerate(height_expressions(extra)):
        out.append((tuple((k,-v)for k,v in terms),-THRESHOLD,'positive_D_row_height_'+str(extra)+'_'+str(n)))
    assert len(out)==6
    return tuple(out)

def evaluate(state,extra):
    p,a,s,d=unpack(state)
    assert extra in EXTRAS
    xleft=diff(p,d,1,extra,0);xright=diff(p,d,extra,3,0)
    yfirst=diff(p,d,1,extra,1);ylast=diff(p,d,extra,3,1)
    expressions=height_expressions(extra)
    bounds=[upper(c,p)for c in expressions]
    # Two telescoping signed sums are exact B-D differences.
    bd=diff(p,d,1,3,1)
    bounds[0]=min(bounds[0],-bd[0])
    bounds[3]=min(bounds[3],bd[1])
    variation=min(max(bounds),max(map(abs,yfirst))+max(map(abs,ylast)))
    nonnegative_D=a[3][0]>=0 or s[12][0]>=0
    passed=nonnegative_D and xleft[0]>=0 and xright[0]>=0 and variation<=THRESHOLD
    return dict(status='PASS_POSITIVE_D_TWO_LINK_TERMINAL'if passed else'GUARD_NOT_IMPLIED',
        extra=extra,D_sign_proved=nonnegative_D,angle_D=list(map(str,a[3])),beta_D=list(map(str,s[12])),
        horizontal_orders=[list(map(str,xleft)),list(map(str,xright))],
        certified_height_variation_upper=str(variation),variation_limit='1/2',
        full_original_ancestry_required=True,whole_original_cover_checked=False,
        new_original_cells=0,new_masks=0)

def evaluate_any(state):
    ans=[evaluate(state,i)for i in EXTRAS]
    for x in ans:
        if x['status']=='PASS_POSITIVE_D_TWO_LINK_TERMINAL':return x
    return dict(status='NO_POSITIVE_D_ROW_GUARD_IMPLIED',results=ans)
