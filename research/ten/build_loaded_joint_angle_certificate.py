"""Use floating proposals, then construct a fully exact rational certificate."""
import sys,math,json,time
from pathlib import Path
import numpy as np
sys.path.insert(0,str(Path(__file__).resolve().parent))
import check_loaded_joint_angle_bound as C
F=C.F
beta=np.linspace(-2*math.atan(2/7),math.pi/2,2501)
sb,cb=np.sin(beta),np.cos(beta)
def rad(sn,cs):
 w=np.abs(sn)+np.abs(cs);return (np.sqrt(16+w*w)-w)/2

def critical(alpha):
 sa,ca=math.sin(alpha),math.cos(alpha);rr=float(rad(sa,ca));A=rr*sb-(np.abs(sb*ca+cb*sa)+np.abs(cb*ca-sb*sa))/2
 kinks=[z for z in [-alpha,math.pi/2-alpha] if beta[0]<=z<=beta[-1]]
 def vmax(delta):
  sd,cd=math.sin(delta),math.cos(delta);sg=sd*cb-cd*sb;cg=cd*cb+sd*sb
  values=np.where(beta<=delta,A+rad(sg,cg)*sg-.5,A-math.sqrt(2)*(sb*cd-cb*sd)-.5)
  answer=float(np.max(values))
  for z in kinks+[delta]:
   aa=rr*math.sin(z)-(abs(math.sin(z+alpha))+abs(math.cos(z+alpha)))/2
   if z<=delta:
    g=delta-z;f=aa+float(rad(math.sin(g),math.cos(g)))*math.sin(g)-.5
   else:f=aa-math.sqrt(2)*math.sin(z-delta)-.5
   answer=max(answer,f)
  return answer
 lo,hi=math.radians(35),2*math.atan(.5)
 for _ in range(30):
  mid=(lo+hi)/2
  if vmax(mid)>=0:hi=mid
  else:lo=mid
 return lo

bounds={}
for i in range(C.FRAME_COUNT+1):
 a=2*math.atan(i/C.FRAME_DEN)
 for sign in [-1,1]:bounds[(i,sign)]=critical(sign*a)
print('Floating proposals complete; all subsequent leaf bounds exact.',flush=True)
meta=dict(schema_version=1,frame_count=C.FRAME_COUNT,frame_denominator=C.FRAME_DEN,radical_scale=C.RADICAL_SCALE,margin_scale=C.MARGIN_SCALE,rows=[],leaf_count=0)
all_leaves=[];started=time.monotonic()
for i in range(C.FRAME_COUNT):
 row=dict(i=i)
 for side,sign,field in [('G',-1,'good'),('B',1,'bad')]:
  d=min(bounds[(i,sign)],bounds[(i+1,sign)])-math.radians(.03)
  delta=F(math.floor(math.tan(d/2)*100000),100000)
  for trial in range(150):
   try:leaves=C.build_pair(i,side,delta);break
   except C.CannotCertify:delta-=F(1,100000)
  else:raise RuntimeError(('Cannot certify',i,side))
  row[field]=str(delta);all_leaves.extend(leaves)
 assert C.gap_margin(F(row['good']),F(row['bad']))>0,('Coupled target fails',row)
 own=[r for r in all_leaves if r[0]==i];row['leaves']=len(own);row['minimum_margin']=min(r[-1] for r in own);meta['rows'].append(row)
 if i%20==0:print('Frame',i,'leaves',len(all_leaves),'seconds',round(time.monotonic()-started,1),flush=True)
meta['leaf_count']=len(all_leaves)
C.META.write_text(json.dumps(meta,indent=2)+'\n')
C.LEAVES.write_text('# i\tside\ttask\tsegment\tclosed-binary-path\tmargin/10^9\n'+''.join('\t'.join(map(str,row))+'\n' for row in all_leaves))
print('Written',len(all_leaves),'leaves; exact validation begins.',flush=True)
print('VALIDATED',C.validate(meta,all_leaves),flush=True)
