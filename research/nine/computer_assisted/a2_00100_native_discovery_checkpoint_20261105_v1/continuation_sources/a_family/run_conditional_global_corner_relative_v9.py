import setup_runtime as S
import argparse,runpy,sys,json,hashlib
from math import hypot
from itertools import product
import fast_exact_area_moments as FAST
import fast_sparse_dual_terms as SPARSE
from pathlib import Path
import conditional_a3_runtime as STRONG
CONE_DIR=Path(__file__).resolve().parent/"rotating_center_cone"
sys.path.insert(0,str(CONE_DIR))
import physical_rotating_frame_center_rows as CONE
import fast_coupled_energy_cache as ENERGY
CONE_SOURCES=json.loads((CONE_DIR/"INPUT_MANIFEST.json").read_text())["files"]
def check_cone_sources():
 for f in CONE_SOURCES:assert hashlib.sha256(Path(f["path"]).read_bytes()).hexdigest()==f["sha256"]
check_cone_sources()
INCIRCLE_DIR=Path(__file__).resolve().parent/"incircle_center_rows"
sys.path.insert(0,str(INCIRCLE_DIR))
import physical_incircle_chords as INCIRCLE
import physical_incircle_l1_rows as INCIRCLE_L1
INCIRCLE_SOURCES=json.loads((INCIRCLE_DIR/"INPUT_MANIFEST.json").read_text())["files"]
def check_incircle_sources():
 for f in INCIRCLE_SOURCES:assert hashlib.sha256(Path(f["path"]).read_bytes()).hexdigest()==f["sha256"]
check_incircle_sources()
RELATIVE_DIR=Path(__file__).resolve().parent/"relative_support_chords_v1"
sys.path.insert(0,str(RELATIVE_DIR))
import physical_relative_support_chords as RELATIVE
import owner_free_relative_support_snapshot as RELATIVE_PRODUCTS
RELATIVE_SOURCES=json.loads((RELATIVE_DIR/"INPUT_MANIFEST.json").read_text())["files"]
def check_relative_sources():
 for f in RELATIVE_SOURCES:assert hashlib.sha256(Path(f["path"]).read_bytes()).hexdigest()==f["sha256"]
 expected=next(f["sha256"]for f in RELATIVE_SOURCES if Path(f["path"]).name=="owner_free_relative_support_snapshot.py")
 assert hashlib.sha256(Path(RELATIVE_PRODUCTS.__file__).read_bytes()).hexdigest()==expected
check_relative_sources()
ap=argparse.ArgumentParser(add_help=False)
ap.add_argument('--h-component',type=int,choices=(0,3,4))
ap.add_argument('--policy',choices=('original','I-owned'),default='original')
ap.add_argument('--angle-cover-only',action='store_true')
args,rest=ap.parse_known_args();STRONG.configure(args.h_component)
script=S.runtime/'d_work/resume_a_component3_post_a1_bounds_round_tree_v11.py'
g=runpy.run_path(str(script),run_name='frozen_driver')
g=g['main'].__globals__
SPARSE_SHA='e53a9e02775ae4cc14a4ead913e48775e3f9afadb35e3f506a89e5120486d619'
assert STRONG.E.SCALE==1<<40
assert hashlib.sha256(Path(SPARSE.__file__).read_bytes()).hexdigest()==SPARSE_SHA
SPARSE.install(STRONG.E)
FAST_SHA='9afb26cad3032731902679f67a3ff166d44ba5d2a5684cf31f832da767edd071'
assert hashlib.sha256(Path(FAST.__file__).read_bytes()).hexdigest()==FAST_SHA
class FastContext(STRONG.Context):
 def __init__(self,*a,**k):
  super().__init__(*a,**k)
  import ac_physical_context as PHYSICAL
  FAST.install(PHYSICAL.AREA)
  ENERGY.install(PHYSICAL.CT)
 def collect(self,state):
  rows,bounds,physical,terminal=super().collect(state)
  if terminal is None:
   rows+=CONE.cone_rows(physical["angles"])
   rows+=INCIRCLE.generate(physical["differences"])+INCIRCLE_L1.generate(physical["differences"])
   rows+=RELATIVE.generate(physical["scalar"],physical["differences"])
  return rows,bounds,physical,terminal
g['Context']=FastContext
oldsplit=g['SPLIT'].split_choice
if args.policy=='I-owned':
 def split(state,point):
  lo,hi=state['angles'][8]
  for cut in(-STRONG.F(3,5),STRONG.F(3,5)):
   if lo<cut<hi:
    return dict(kind='closed_angle_bisection',owner=8,cut=str(cut),selection='complete_conditional_I_three_slope_cover')
  if args.angle_cover_only:return None
  sat_count=sum(kind=='sat'for pair,kind,choice in state['choices'])
  proxy_count=sum(kind=='proxy'for pair,kind,choice in state['choices'])
  if sat_count>=2 or proxy_count>=5:
   corner_candidates=[]
   for owner,(lower,upper)in enumerate(state['angles']):
    if upper-lower<=STRONG.F(1,16):continue
    aa,bb=point[18+owner],point[27+owner];norm=hypot(aa,bb)
    if norm<=1e-12:continue
    aa,bb=aa/norm,bb/norm;x,y=point[2*owner],point[2*owner+1]
    error=max((x+(e*aa-t*bb)/2)**2+(y+(e*bb+t*aa)/2)**2-1105/256 for e,t in product((-1,1),repeat=2))
    corner_candidates.append((error,float(upper-lower),owner))
   error,width,owner=max(corner_candidates,default=(0.,0.,0))
   if error>.12:
    lower,upper=state['angles'][owner]
    cut=STRONG.F(0)if lower<0<upper else g['SPLIT'].BASE.radial_cut(state,point,owner)
    if not lower<cut<upper:cut=(lower+upper)/2
    return dict(kind='closed_angle_bisection',owner=owner,cut=str(cut),normalized_corner_excess=error,selection='global_normalized_corner_before_extra_pair')
  priority=(1,4,5,6,3,2)if args.h_component==0 else(6,5,3,2,1,4)
  raw=[e for e in STRONG.E.best_pairs(state,point) if 8 in e[1] and e[0]<-1e-7]
  candidates=sorted([e for e in raw if min(e[1]) in priority],key=lambda e:priority.index(min(e[1])))
  if not candidates:candidates=raw
  h_neighbors={0:(0,1,4),3:(1,2,3,4,5,6,8),4:(0,1,2,3,4,8)}[args.h_component]
  h_pairs=[e for e in STRONG.E.best_pairs(state,point) if 7 in e[1] and (e[1][0] if e[1][1]==7 else e[1][1]) in h_neighbors and e[0]<-.1]
  if h_pairs and (not candidates or h_pairs[0][0]<candidates[0][0]-.1):candidates=h_pairs+candidates
  selected=[(pair,ch)for pair,kind,ch in state['choices']if kind=='sat' and(8 in pair or 7 in pair)]
  worst=None
  for (i,j),ch in selected:
   owner,axis,sg=ch;dx=point[2*j]-point[2*i];dy=point[2*j+1]-point[2*i+1]
   a,b=point[18+i],point[27+i];c,d=point[18+j],point[27+j]
   required=(1+abs(a*c+b*d)+abs(a*d-b*c))/2
   a,b=point[18+owner],point[27+owner]
   sep=sg*(a*dx+b*dy if axis==0 else-b*dx+a*dy)
   item=(sep-required,(i,j),ch)
   if worst is None or item[0]<worst[0]:worst=item
  newgap=candidates[0][0]if candidates else 0.
  if worst and worst[0]<-.03 and worst[0]<newgap-.05:
   pair=worst[1];owner=max(pair,key=lambda k:(float(state['angles'][k][1]-state['angles'][k][0]),k==8))
   lo,hi=state['angles'][owner]
   if hi-lo>STRONG.F(1,16):
    cut=STRONG.F(0)if lo<0<hi else(lo+hi)/2
    return dict(kind='closed_angle_bisection',owner=owner,cut=str(cut),diagnostic_pair=list(pair),diagnostic_gap=worst[0],selection='targeted_extra_cavity_owned_axis_frame_refinement')
  if candidates and candidates[0][0]<-1e-7:
   return dict(kind='complete_physical_sat',pair=list(candidates[0][1]),diagnostic_gap=candidates[0][0],selection='targeted_extra_cavity_complete_owned_axes')
  return oldsplit(state,point)
 g['SPLIT'].split_choice=split
old_dump=g['dump']
def dump(p,x):
 if p.name=='manifest.json':
  x['stronger_scope']=dict(STRONG.scope(),rotating_center_cone_only=True,incircle_center_rows=dict(l1_secants=True,square_root_chords=True),relative_support_chords=dict(signed=True,folded=True,support_upper="121/100",new_case_premise=False))
  check_cone_sources()
  check_incircle_sources()
  check_relative_sources()
  x['source_sha256'].update({f['path']:f['sha256']for f in RELATIVE_SOURCES})
  x['source_sha256'][str((RELATIVE_DIR/'INPUT_MANIFEST.json').resolve())]=STRONG.E.sha(RELATIVE_DIR/'INPUT_MANIFEST.json')
  x['source_sha256'].update({f['path']:f['sha256']for f in INCIRCLE_SOURCES})
  x['source_sha256'][str((INCIRCLE_DIR/'INPUT_MANIFEST.json').resolve())]=STRONG.E.sha(INCIRCLE_DIR/'INPUT_MANIFEST.json')
  x['source_sha256'].update({f['path']:f['sha256']for f in CONE_SOURCES})
  x['source_sha256'][str((CONE_DIR/'INPUT_MANIFEST.json').resolve())]=STRONG.E.sha(CONE_DIR/'INPUT_MANIFEST.json')
  x['source_sha256'].update(STRONG.sources())
  assert hashlib.sha256(Path(FAST.__file__).read_bytes()).hexdigest()==FAST_SHA
  x['source_sha256'][str(Path(FAST.__file__).resolve())]=FAST_SHA
  assert hashlib.sha256(Path(SPARSE.__file__).read_bytes()).hexdigest()==SPARSE_SHA
  x['source_sha256'][str(Path(SPARSE.__file__).resolve())]=SPARSE_SHA
  x['source_sha256'][str(Path(__file__).resolve())]=STRONG.E.sha(__file__)
 old_dump(p,x)
g['dump']=dump
sys.argv=[str(script),*rest]
g['main']()
