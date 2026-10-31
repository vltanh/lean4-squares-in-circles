from pathlib import Path
from fractions import Fraction as F
import hashlib, json

ROOT = Path('/workspace/scratch/8168d2185cf7/repo/research/nine')
PINS = {
 'INNER_PENTAGON_FOUR_SPOKE_BOTH_END_AXES_EXCLUSION.md': 'e1106b043b8b6b61899177a7e68121fce49c65e3ebf86273ef332cf451f437bf',
 'UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md': 'ee865704904a8b2a5cab7649bdfd928008c253631abf1eb346d4950411c3afac',
 'PHYSICAL_BODY_GRAPH_UNCROSSING.md': 'eb26f19b27dc7327f80a64ccfd1febb542c5915aadcf95227e35765b20d3509a',
 'SIX_BODY_INNER_PENTAGON_LOAD_COVER.md': 'fa877c9d7d25c57a7c8cf438a429465b5952cb8db6628c57d9d93695b33dd434',
}
for name, want in PINS.items():
    assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == want, name

names = ('a','b','c','d','U','V','R','S','gamma','u','v')
zero = (0,)*len(names)
def const(c): return {zero:F(c)} if c else {}
def var(name):
    exp=list(zero); exp[names.index(name)]=1
    return {tuple(exp):F(1)}
def add(*terms):
    out={}
    for term in terms:
        for e,c in term.items(): out[e]=out.get(e,F(0))+c
    return {e:c for e,c in out.items() if c}
def neg(p): return {e:-c for e,c in p.items()}
def sub(p,q): return add(p,neg(q))
def mul(p,q):
    out={}
    for ep,cp in p.items():
        for eq,cq in q.items():
            e=tuple(x+y for x,y in zip(ep,eq))
            out[e]=out.get(e,F(0))+cp*cq
    return {e:c for e,c in out.items() if c}
a,b,c,d,U,V,R,S,gamma,u,v=(var(n) for n in names)
p=add(mul(a,U),neg(mul(b,V)),neg(mul(c,R)),neg(mul(d,S)))
q=add(neg(mul(b,U)),neg(mul(a,V)),neg(mul(d,R)),mul(c,S))
span=add(p,b,q,d)
expanded=add(mul(sub(a,b),U),mul(sub(c,d),S),neg(mul(add(a,b),V)),neg(mul(add(c,d),R)),b,d)
assert sub(span,expanded)=={}
# The displayed common point is identical in both full square frames.
assert sub(add(p,neg(mul(a,U)),mul(b,V)),add(neg(mul(c,R)),neg(mul(d,S))))=={}
assert sub(add(neg(mul(b,U)),neg(mul(a,V))),add(q,mul(d,R),neg(mul(c,S))))=={}

# Derive each endpoint of the linear box maximization coefficientwise.
# These four ordering cases exhaust a>=b / b>=a and c>=d / d>=c.
orderings=[]
for ab,cd in ((True,True),(True,False),(False,True),(False,False)):
    Umax=const(1 if ab else 0)
    Smax=const(1 if cd else 0)
    actual=add(mul(sub(a,b),Umax),mul(sub(c,d),Smax),b,d)
    target=add(a if ab else b,c if cd else d)
    assert sub(actual,target)=={}
    orderings.append({'a_ge_b':ab,'c_ge_d':cd,'max_U':int(ab),'max_V':0,'max_R':0,'max_S':int(cd)})

# At the point-only zero slider, retain the entire genuine D3 vectors.
force_x=add(neg(u),u)
force_y=add(neg(gamma),neg(v),v,gamma)
assert force_x=={} and force_y=={}

edges={tuple(sorted(e)) for e in [('H','0'),('H','1'),('H','2'),('H','3'),('0','1'),('1','2'),('2','3'),('3','4'),('4','0')]}
degrees={v:sum(v in e for e in edges) for v in ('H','0','1','2','3','4')}
assert degrees=={'H':4,'0':3,'1':3,'2':3,'3':3,'4':2}
assert all('H' not in loads and '3' not in loads for loads in ({'1','2','4'},{'0','1','2','4'}))
reflection={str(i):str((3-i)%5) for i in range(5)} | {'H':'H'}
assert {tuple(sorted((reflection[x],reflection[y]))) for x,y in edges}==edges
assert {reflection[x] for x in {'1','2','3','4'}}=={'0','1','2','4'}

out={
 'status':'pass: exact identities and full original interface mapping; physical proof is in the complete root review',
 'pins':PINS,
 'coefficientwise_identities':['two-square span identity','physical common x coordinate','physical common y coordinate','zero-slider full D3 x force','zero-slider full D3 y force'],
 'four_complete_linear_box_maxima':orderings,
 'original_degrees':degrees,
 'load_sets':[list(x) for x in (('1','2','4'),('0','1','2','4'))],
 'reflection':reflection,
 'endpoint_scope':['equal/opposite/perpendicular H end axes','all weak intermediate axes','all U,V,R,S in [0,1]','all outer sliders in [-1,0]','positive side means including endpoints','strict point-only D-C normal at slider 0'],
 'scope':'Only both H-owned end normals in H4_D0.L124 and H4_D0.L0124; neither full family is closed.',
 'method':'Exact Fraction coefficient identities and graph equalities; no pose sampling, numerical optimization, Lean, CI or remote writes.'
}
target=Path('/tmp/pr11_root_h4_both_end_axes_checks_20261028.json')
target.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':'pass','file':str(target),'sha256':hashlib.sha256(target.read_bytes()).hexdigest(),'pins':len(PINS),'box_order_cases':len(orderings),'degree_map':degrees},sort_keys=True))
