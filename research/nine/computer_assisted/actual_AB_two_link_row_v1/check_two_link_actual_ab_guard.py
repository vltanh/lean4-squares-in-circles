"""Independent literal implication and closed-complement reconstruction."""
from fractions import Fraction as Q
from itertools import permutations,product

def evaluate(state):
 p=[tuple(map(Q,v))for v in state['positions']];a=[tuple(map(Q,v))for v in state['angles']];s=[tuple(map(Q,v))for v in state['scalar']]
 assert len(p)==18 and len(a)==9 and len(s)==36
 assert all(lo<=hi for lo,hi in p+a+s)
 raw=state['differences'];raw=raw if isinstance(raw,list)else[{'pair':pair,'intervals':intervals}for pair,intervals in raw.items()]
 edges={}
 for e in raw:
  i,j=e['pair'];assert 0<=i<j<9 and len(e['intervals'])==2
  for axis,(lo,hi)in enumerate(e['intervals']):
   lo,hi=Q(lo),Q(hi);assert lo<=hi
   edges[i,j,axis]=(lo,hi);edges[j,i,axis]=(-hi,-lo)
 def delta(i,j,axis):
  options=[(p[2*j+axis][0]-p[2*i+axis][1],p[2*j+axis][1]-p[2*i+axis][0])]
  if(i,j,axis)in edges:options.append(edges[i,j,axis])
  lo=max(x[0]for x in options);hi=min(x[1]for x in options);assert lo<=hi;return(lo,hi)
 def upper(coeff):
  answer=sum(v*p[k][1 if v>0 else 0]for k,v in coeff)
  positive=[];negative=[]
  for k,v in coeff:
   assert k%2==1
   (positive if v>0 else negative).extend([k//2]*abs(v))
  for order in set(permutations(positive)):
   answer=min(answer,sum(delta(i,j,1)[1]for i,j in zip(negative,order)))
  return answer
 forms=[[(3,-1),(7,1)],[(3,1),(7,-1)],[(3,-1),(7,-1),(17,2)],[(3,1),(7,1),(17,-2)]]
 heights=[upper(c)for c in forms];variation=max(heights);assert variation>=0
 dx=delta(3,6,0);dy=delta(3,6,1);orders=[delta(1,8,0),delta(8,3,0)]
 angle=not(a[3][0]<0 and s[12][0]<0);reserve=min(1+dx[0],1-dx[1]);premises=angle and dy[0]>=0 and reserve>0
 passed=premises and min(v[0]for v in orders)>=0 and variation<=Q(3,5)
 return dict(status='PASS_ACTUAL_AB_TWO_LINK_TERMINAL_GUARD'if passed else'GUARD_NOT_IMPLIED',
             theorem='actual_AB_full_angle_two_link_row_3_5_v1',variation_limit='3/5',premises_proved=bool(premises),
             D_nonnegative_angle_proved=bool(angle),D_angle_interval=list(map(str,a[3])),
             D_signed_beta_interval=list(map(str,s[12])),DG_x_interval=list(map(str,dx)),
             DG_y_interval=list(map(str,dy)),strict_DG_horizontal_reserve=str(reserve),
             BI_ID_order_intervals=[list(map(str,v))for v in orders],
             four_signed_height_upper_bounds=list(map(str,heights)),two_link_variation_upper=str(variation),
             original_actual_AB_EF_FG_required=True,all_nine_original_00100_ancestry_required=True,
             whole_original_cover_checked=False,new_original_cells=0,new_masks=0)

def reduced_complement(state):
 g=evaluate(state);assert g['premises_proved']and Q(g['BI_ID_order_intervals'][1][0])>0
 answer=[(((16,Q(1)),(2,Q(-1))),Q(0),'two_link_actual_AB_escape_0')]
 forms=[{3:-1,7:1},{3:1,7:-1},{3:-1,7:-1,17:2},{3:1,7:1,17:-2}]
 for index,form in enumerate(forms,1):
  answer.append((tuple((k,Q(-v))for k,v in sorted(form.items())),-Q(3,5),'two_link_actual_AB_escape_'+str(index)))
 return answer,g
