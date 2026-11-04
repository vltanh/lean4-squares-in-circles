"""Independent finite arithmetic review; continuous theorem is separately cited."""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
import hashlib,importlib.util,json
HERE=Path(__file__).resolve().parent
source=HERE.parent/'shared_terminal/positive_d_row_guard.py'
spec=importlib.util.spec_from_file_location('reviewed_positive_d',source)
G=importlib.util.module_from_spec(spec);spec.loader.exec_module(G)
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
original=sha(source)
count=0
for extra in (7,8):
 rows=G.complement_rows(extra)
 expected=[({2*extra:F(1),2:F(-1)},F(0)),({6:F(1),2*extra:F(-1)},F(0))]
 for s,t in product((-1,1),repeat=2):
  co={3:F(s),2*extra+1:F(t-s),7:-F(t)}
  expected.append(({i:v for i,v in co.items()if v},F(-1,2)))
 assert len(rows)==6
 for row,(co,rhs)in zip(rows,expected):
  assert dict(row[0])==co and row[1]==rhs;count+=1
 for b,x,d in product((F(-3,4),F(0),F(1,4)),repeat=3):
  pos=[(F(0),F(0))for _ in range(18)]
  pos[3]=(b,b);pos[2*extra+1]=(x,x);pos[7]=(d,d)
  observed=[G.upper(c,pos)for c in G.height_expressions(extra)]
  assert observed==[s*(x-b)+t*(d-x)for s,t in product((-1,1),repeat=2)]
  assert max(observed)==abs(x-b)+abs(d-x);count+=1
  constraints=[sum(v*pos[k][0]for k,v in row[0])<=row[1]for row in rows[2:]]
  assert any(constraints)==(abs(x-b)+abs(d-x)>=F(1,2));count+=1
 # Direct and reversed interval orientation, including telescoping bounds.
 p=[(F(0),F(0))for _ in range(18)]
 p[2]=(F(-1,2),F(-1,2));p[6]=(F(3,2),F(3,2));p[2*extra]=(F(1,2),F(1,2))
 for b,x,d in product((F(-3,4),F(0),F(1,4)),repeat=3):
  p[3]=(b,b);p[2*extra+1]=(x,x);p[7]=(d,d)
  diffs={(i,j):((p[2*j][0]-p[2*i][0],)*2,(p[2*j+1][0]-p[2*i+1][0],)*2)for i in range(9)for j in range(i+1,9)}
  for i,j in [(1,extra),(extra,3),(1,3)]:
   for axis in (0,1):assert G.diff(p,diffs,i,j,axis)==(p[2*j+axis][0]-p[2*i+axis][0],)*2;count+=1
  state=dict(positions=p,angles=[(F(0),F(0))]*9,scalar=[(F(0),F(0))]*36,differences=diffs)
  report=G.evaluate(state,extra)
  assert F(report['certified_height_variation_upper'])==abs(x-b)+abs(d-x)
  assert (report['status']=='PASS_POSITIVE_D_TWO_LINK_TERMINAL')==(abs(x-b)+abs(d-x)<=F(1,2));count+=1
# Reject negative D when both exact sign sources exclude nonnegative beta.
p=[(F(0),F(0))for _ in range(18)];p[2]=(F(-1,2),)*2;p[6]=(F(3,2),)*2;p[16]=(F(1,2),)*2
angles=[(F(0),F(0))]*9;angles[3]=(F(-1),F(-1,2));scalar=[(F(0),F(0))]*36;scalar[12]=(F(-1),F(-1,2))
assert G.evaluate(dict(positions=p,angles=angles,scalar=scalar),8)['status']=='GUARD_NOT_IMPLIED';count+=1
assert sha(source)==original
out=dict(status='PASS_INDEPENDENT_POSITIVE_D_GUARD_ARITHMETIC_AND_SOURCE_REVIEW',exact_checks=count,
 helper_sha256=original,reviewer_sha256=sha(__file__),all_twelve_complement_rows_checked=True,
 both_original_extra_labels_retained=True,telescoping_and_reversed_differences_checked=True,
 physical_theorem='WEAK_OUTER_NUMERIC_POSITIVE_D_TOTAL_VARIATION_ROW_HAND_TERMINAL.md sections 1-4',
 conditional_scope_only=True,source_unchanged=True,new_original_cells=0,new_masks=0)
(HERE/'POSITIVE_D_ROW_GUARD_INDEPENDENT_REVIEW.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
