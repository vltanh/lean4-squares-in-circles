"""Floating discovery helpers for a wider, owner-complete outer cap.

No floating result is a proof. All normals and physical-square variables
are retained in the support dual. Exact proof routines, if completed,
must evaluate the rational multipliers independently.
"""
from pathlib import Path
import sys, math
import numpy as np
from scipy.optimize import minimize_scalar, minimize

HERE=Path(__file__).resolve().parent
BASE=(HERE if (HERE/'joint_center_support.py').is_file()
      else HERE.parent/'pr11/research/nine/computer_assisted')
sys.path.insert(0,str(BASE))
from joint_center_support import center_support,face_certificate,plain_support
from explore_fork_dual import min_support,support

Q=1105/256;R=math.sqrt(Q);RHO=math.sqrt(Q-.25)-.5
A=46.;B=13.5;K=207/16;T=211/4;DEN=4096
EBOX=(89/60,91/60,-1/8,1/8)
SBOX=(0.,13/12,3/5,91/60)
EFRAME=(-math.atan(.07),math.atan(.07))

def target(z):
    return T+14.5*z if z>=0 else T+max(16*z,14.5*z-1.5)

def normal(w,chart):
    if chart=='up': return np.array([-w,1.]), math.atan(w)
    assert chart=='left'
    return np.array([-1.,w]), -math.atan(w)

def boxtoll(face,box):
    xl,xh,yl,yh=box
    return -xl*face[0]+xh*face[1]-yl*face[2]+yh*face[3]

def boxed_plain(q,theta,box,face):
    moved=q+np.array([face[0]-face[1],face[2]-face[3]])
    return plain_support(moved,theta)+boxtoll(face,box)

def free_bound(q,costs,box,frame=None,face=None):
    xl,xh,yl,yh=box
    if frame is None: frame=(-math.pi/4,math.pi/4)
    penalty=min_support(costs,frame)
    if face is None: face=np.zeros(4)
    moved=q+np.array([face[0]-face[1],face[2]-face[3]])
    toll=boxtoll(face,box)
    return min(R*np.linalg.norm(moved)-min_support([moved,*costs],frame)+toll,
               RHO*np.linalg.norm(moved)-penalty+toll,
               max(xl*q[0],xh*q[0])+max(yl*q[1],yh*q[1])-penalty)

def raw(w,z,k,chart,owner,faces=None):
    n,theta=normal(w,chart);m=np.array([1.,z]);e=np.array([1.,0.])
    ve=A*e-k*n;vs=B*m+k*n
    ec=[A*e,k*n];sc=[B*m,k*n]
    if owner=='S':
        ep=free_bound(ve,ec,EBOX,EFRAME)
        sh=center_support(vs,theta,SBOX)-sum(support(v,theta) for v in sc)
    else:
        assert owner=='E'
        ep=center_support(ve,theta,EBOX)-sum(support(v,theta) for v in ec)
        sh=free_bound(vs,sc,SBOX,face=faces)
    return ep+sh

def proposal(w,z,chart,owner):
    n,theta=normal(w,chart)
    if owner=='S':
        objective=lambda k:raw(w,z,k,chart,owner)-target(z)
        fit=minimize_scalar(objective,bounds=(0,256),method='bounded',options={'xatol':1e-7,'maxiter':110})
        ks=[0.,K/np.linalg.norm(n),float(fit.x),B*max(-z,0.)]
        k=min(ks,key=objective);kn=max(0,round(k*DEN));k=kn/DEN
        vs=B*np.array([1.,z])+k*n
        fac=face_certificate(vs,theta,SBOX,DEN)['lambda']
        cert={'den':DEN,'k':kn,'faces':fac}
        return objective(k),cert
    def face(v):
        return np.array([max(v[1],0),max(-v[1],0),max(v[2],0),max(-v[2],0)])
    def objective(v):return raw(w,z,v[0],chart,owner,face(v))-target(z)
    seeds=[np.array([K/np.linalg.norm(n),0.,0.]),np.array([0.,0.,B*max(-z,0)])]
    for cx,cy in [(0,0),(0,1),(1,0),(1,1)]:
        def vfrom(k):
            vv=B*np.array([1.,z])+k*n
            return np.array([k,cx*max(-vv[0],0),cy*max(-vv[1],0)])
        fit=minimize_scalar(lambda k:objective(vfrom(k)),bounds=(0,256),method='bounded',options={'maxiter':100,'xatol':1e-7})
        seeds.append(vfrom(fit.x))
    v=min(seeds,key=objective)
    if objective(v)>=-.01:
        fits=[minimize(objective,seed,method='Powell',bounds=[(0,256),(-256,256),(-1024,1024)],options={'maxiter':150,'ftol':1e-9,'xtol':1e-7}) for seed in [v,seeds[0]]]
        v=min([v,*(f.x for f in fits)],key=objective)
    kn=max(0,round(v[0]*DEN));fac=np.maximum(0,np.round(face(v)*DEN)).astype(int).tolist()
    efaces=face_certificate(A*np.array([1.,0.])-(kn/DEN)*n,theta,EBOX,DEN)['lambda']
    cert={'den':DEN,'k':kn,'faces':fac,'efaces':efaces}
    return raw(w,z,kn/DEN,chart,owner,np.array(fac)/DEN)-target(z),cert

if __name__=='__main__':
    import argparse,json,time
    ap=argparse.ArgumentParser();ap.add_argument('--owner',choices=['E','S'],required=True);ap.add_argument('--chart',choices=['up','left'],required=True);args=ap.parse_args()
    ws=np.linspace(-1,1,17) if args.owner=='S' else np.linspace(-.07,.07,7)
    zs=[-57,-30,-16,-10,-6,-3,-2,-1,-.5,-.1,0,.1,.5,1,2,4,8,16,24]
    results=[];start=time.monotonic();worst=(-1e9,None)
    out=Path(__file__).with_name(f'wider_outer_{args.owner}_{args.chart}_discovery.json')
    for w in ws:
        row=[]
        for z in zs:
            value,cert=proposal(w,z,args.chart,args.owner)
            result={'w':float(w),'z':float(z),'residual':value,'certificate':cert};row.append(result);results.append(result)
            if value>worst[0]:worst=(value,(w,z))
        out.write_text(json.dumps({'proof_status':'floating_discovery_only','owner':args.owner,'chart':args.chart,'results':results},indent=2)+'\n')
        print(args.owner,args.chart,'w',round(float(w),4),'rowmax',max(r['residual']for r in row),'worst',worst,'seconds',round(time.monotonic()-start,1),flush=True)
