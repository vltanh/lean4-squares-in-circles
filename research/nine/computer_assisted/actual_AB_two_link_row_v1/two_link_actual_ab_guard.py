"""Exact quantitative guards and the full closed D821 two-link complement.
The physical original-nine caller and exact mask remain external prerequisites.
"""
from fractions import Fraction as F
LIMIT=F(3,5)
THEOREM='actual_AB_full_angle_two_link_row_3_5_v1'

def box(values):
 ans=tuple(tuple(map(F,p))for p in values)
 assert all(len(p)==2 and p[0]<=p[1]for p in ans)
 return ans

def unpack(state):
 pos=box(state['positions']);angles=box(state['angles']);scalar=box(state['scalar'])
 assert len(pos)==18 and len(angles)==9 and len(scalar)==36
 raw=state['differences']
 diffs={tuple(e['pair']):box(e['intervals'])for e in raw}if isinstance(raw,list)else{tuple(k):box(v)for k,v in raw.items()}
 assert all(0<=i<j<9 and len(ds)==2 for(i,j),ds in diffs.items())
 return pos,angles,scalar,diffs

def difference(pos,diffs,i,j,axis):
 lo=pos[2*j+axis][0]-pos[2*i+axis][1];hi=pos[2*j+axis][1]-pos[2*i+axis][0]
 if i<j and(i,j)in diffs:
  a,b=diffs[i,j][axis];lo=max(lo,a);hi=min(hi,b)
 if i>j and(j,i)in diffs:
  a,b=diffs[j,i][axis];lo=max(lo,-b);hi=min(hi,-a)
 assert lo<=hi
 return lo,hi

def evaluate(state):
 p,a,s,d=unpack(state)
 gd_x=difference(p,d,3,6,0);gd_y=difference(p,d,3,6,1)
 orders=[difference(p,d,1,8,0),difference(p,d,8,3,0)]
 positive=a[3][0]>=0 or s[12][0]>=0
 horizontal=F(1)-max(map(abs,gd_x))
 premises=positive and gd_y[0]>=0 and horizontal>0
 heights=[difference(p,d,1,3,1)[1],difference(p,d,3,1,1)[1],
          difference(p,d,1,8,1)[1]+difference(p,d,3,8,1)[1],
          difference(p,d,8,1,1)[1]+difference(p,d,8,3,1)[1]]
 variation=max(heights);assert variation>=0
 passed=premises and all(lo>=0 for lo,hi in orders)and variation<=LIMIT
 return dict(status='PASS_ACTUAL_AB_TWO_LINK_TERMINAL_GUARD'if passed else'GUARD_NOT_IMPLIED',
             theorem=THEOREM,variation_limit=str(LIMIT),premises_proved=bool(premises),
             D_nonnegative_angle_proved=bool(positive),D_angle_interval=list(map(str,a[3])),
             D_signed_beta_interval=list(map(str,s[12])),DG_x_interval=list(map(str,gd_x)),
             DG_y_interval=list(map(str,gd_y)),strict_DG_horizontal_reserve=str(horizontal),
             BI_ID_order_intervals=[list(map(str,v))for v in orders],
             four_signed_height_upper_bounds=list(map(str,heights)),two_link_variation_upper=str(variation),
             original_actual_AB_EF_FG_required=True,all_nine_original_00100_ancestry_required=True,
             whole_original_cover_checked=False,new_original_cells=0,new_masks=0)

def reduced_complement(state):
 guard=evaluate(state)
 assert guard['premises_proved']is True
 assert F(guard['BI_ID_order_intervals'][1][0])>0
 rows=[(((16,F(1)),(2,F(-1))),F(0),'two_link_actual_AB_escape_0'),
       (((3,F(1)),(7,F(-1))),-LIMIT,'two_link_actual_AB_escape_1'),
       (((3,F(-1)),(7,F(1))),-LIMIT,'two_link_actual_AB_escape_2'),
       (((3,F(1)),(7,F(1)),(17,F(-2))),-LIMIT,'two_link_actual_AB_escape_3'),
       (((3,F(-1)),(7,F(-1)),(17,F(2))),-LIMIT,'two_link_actual_AB_escape_4')]
 return rows,guard
