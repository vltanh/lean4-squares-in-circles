#!/usr/bin/env python3
"""DISCOVERY ONLY: complete-domain all-nine 001/00 v>=5/8 LP search.

All nine independent orientation intervals, all original physical pairs,
corner containment through valid support halfplanes, marked cone bits, and
the interchangeable extras are retained. Farkas leaves need separate exact
replay. A nonempty frontier is expressly not a proof.
"""
from itertools import combinations
from pathlib import Path
from math import sqrt,gcd
import argparse,json,time
import numpy as np
from scipy.optimize import linprog
from weak_outer_hand_G_order_search import supportlo,hbounds,nbounds,reqlo,mulup

Q=1105/256;R=sqrt(Q);rho=91/60;a=46.;b=13.5
DIRS=[(x,y) for x in range(-3,4) for y in range(-3,4) if (x or y) and gcd(x,y)==1]
EDGES=[(0,1,0),(1,2,0),(2,3,1),(4,5,0),(5,6,0)]
IMPLIED={(0,1),(0,2),(0,3),(1,2),(1,3),(4,5),(4,6),(5,6)}
PAIRS=[p for p in combinations(range(9),2) if p not in IMPLIED]

def beta_lo(T):
    l,u=T;m=0 if l<=0<=u else min(abs(l),abs(u));return m/sqrt(1+m*m)-1e-12

def center_bounds(box,pos,choices):
    hs=[hbounds(T) for T in box];gs=[.25/h[1] for h in hs]
    X=[list(pos[2*i]) for i in range(9)];Y=[list(pos[2*i+1]) for i in range(9)]
    X[2][0]=max(X[2][0],hs[2][0]-1/60);X[3][0]=max(X[3][0],4/3)
    # Accepted complete G-order theorem and its physical scalar reductions.
    X[2][1]=min(X[2][1],hs[2][1]+5/64)
    X[6][0]=max(X[6][0],hs[6][0]+101/432)
    for repeat in range(16):
        for i,j,bit in EDGES:
            g=gs[i]+gs[j] if bit else hs[i][0]+hs[j][0]
            X[j][0]=max(X[j][0],X[i][0]+g);X[i][1]=min(X[i][1],X[j][1]-g)
        X[7][1]=min(X[7][1],X[8][1]);X[8][0]=max(X[8][0],X[7][0])
        for pair,kind,ch in choices:
            if kind!='proxy':continue
            i,j=pair;axis,sgn=ch;coords=(X,Y)[axis]
            if sgn<0:i,j=j,i
            g=gs[i]+gs[j]
            coords[j][0]=max(coords[j][0],coords[i][0]+g);coords[i][1]=min(coords[i][1],coords[j][1]-g)
        for axis in (0,1):
          along,across=(X,Y) if axis==0 else (Y,X)
          for i in range(9):
            hlo,hhi=hs[i];klo=sqrt(max(0,.5-hhi*hhi));xl,xu=along[i]
            xlo=0 if xl<=0<=xu else min(abs(xl),abs(xu))
            aa=Q-(xlo+hlo)**2;bb=Q-(xlo+klo)**2
            if aa<0 and bb<0:
                across[i]=[1.,-1.];continue
            cap=min(max(sqrt(max(0,aa))-klo,sqrt(max(0,bb))-hlo),sqrt(max(0,rho*rho-xlo*xlo)))+1e-10
            across[i][0]=max(across[i][0],-cap);across[i][1]=min(across[i][1],cap)
        Y[3][0]=max(Y[3][0],Y[2][0]+5/8);Y[2][1]=min(Y[2][1],Y[3][1]-5/8)
        dg_clearance=8/15+(7/8)*(hs[3][0]+hs[6][0]-1)
        Y[6][0]=max(Y[6][0],Y[3][0]+dg_clearance);Y[3][1]=min(Y[3][1],Y[6][1]-dg_clearance)
        for i,j,bit in EDGES:
            dxhi=X[j][1]-X[i][0]
            Y[j][0]=max(Y[j][0],Y[i][0]-dxhi);Y[j][1]=min(Y[j][1],Y[i][1]+dxhi)
            Y[i][0]=max(Y[i][0],Y[j][0]-dxhi);Y[i][1]=min(Y[i][1],Y[j][1]+dxhi)
    return [tuple(v) for i in range(9) for v in (X[i],Y[i])],hs,gs

def matrix(box,pos,choices):
    CB,hs,gs=center_bounds(box,pos,choices);rows=[];rhs=[];names=[]
    def add(entries,rv,name):
        co=np.zeros(18)
        for k,v in entries:co[k]+=v
        rows.append(co);rhs.append(rv);names.append(name)
    for k,(l,u) in enumerate(CB):
        add([(k,1)],u,'bound_up_'+str(k));add([(k,-1)],-l,'bound_lo_'+str(k))
    for i in range(9):
        for p,q in DIRS:
            add([(2*i,p),(2*i+1,q)],sqrt(Q*(p*p+q*q))-supportlo(box[i],(p,q)),f'circle_{i}_{p}_{q}')
    for i,j,bit in EDGES:
        for sy in (-1,1):add([(2*i,1),(2*j,-1),(2*i+1,sy),(2*j+1,-sy)],0,f'cone_{i}_{j}_{sy}')
        low=gs[i]+gs[j] if bit else hs[i][0]+hs[j][0]
        add([(2*i,1),(2*j,-1)],-low,f'chain_{i}_{j}')
    add([(6,1),(4,-1)],hs[2][1]+hs[3][1],'CD_weak')
    add([(5,1),(7,-1)],-5/8,'CD_big_transverse')
    add([(14,1),(16,-1)],0,'extras_x_order')
    add([(4,-a),(12,-b)],-6.75-a*hs[2][0]-b*hs[6][0],'left_cap_and_chains')
    add([(6,1),(12,-1)],1459/1728,'DG_horizontal_cap')
    add([(6,-1),(12,1)],1459/1728,'DG_horizontal_cap_other')
    add([(0,-a),(8,-b)],211/4+a*hs[0][1]+b*hs[4][1]-4*beta_lo(box[0]),'left_endpoint_cap')
    add([(6,a),(12,b)],211/4+a*hs[3][1]+b*hs[6][1]-4*beta_lo(box[3]),'right_endpoint_cap')
    # The accepted physical pair cap is direction- and label-independent.
    # Every ordered original pair retains its own folded main-angle toll.
    for i in range(9):
      for j in range(9):
        if i==j:continue
        rhs_cap=211/4+a*hs[i][1]+b*hs[j][1]-4*beta_lo(box[i])
        for axis in (0,1):
          for sg in (-1,1):
            add([(2*i+axis,sg*a),(2*j+axis,sg*b)],rhs_cap,f'all_pair_cap_{i}_{j}_{axis}_{sg}')
    etaC=hs[2][0]+.25/hs[2][0]-1
    budget=a*(hs[3][1]-.25/hs[3][1])-2*a*(hs[1][0]-.5)-a*etaC-2*b*(hs[5][0]-.5)-4*beta_lo(box[0])-4*beta_lo(box[3])
    add([],budget,'orientation_budget')
    for pair,knd,ch in choices:
        i,j=pair
        if knd=='proxy':
            axis,sgn=ch
            add([(2*i+axis,sgn),(2*j+axis,-sgn)],-gs[i]-gs[j],f'proxy_{i}_{j}_{axis}_{sgn}')
        else:
            owner,ax,sgn=ch;nn=nbounds(box[owner],ax,sgn)
            nm=np.array([round((v[0]+v[1])/2*2**30)/2**30 for v in nn]);error=0
            for xy in (0,1):
                v=nn[xy];ee=(v[0]-nm[xy],v[1]-nm[xy]);dr=(CB[2*j+xy][0]-CB[2*i+xy][1],CB[2*j+xy][1]-CB[2*i+xy][0])
                if pair==(2,3):
                    dr=(max(dr[0],gs[2]+gs[3]),min(dr[1],31/30)) if xy==0 else (max(dr[0],5/8),min(dr[1],31/30))
                if pair==(3,6) and xy==0:dr=(max(dr[0],-1459/1728),min(dr[1],1459/1728))
                error+=mulup(ee,dr)
            add([(2*i,nm[0]),(2*i+1,nm[1]),(2*j,-nm[0]),(2*j+1,-nm[1])],-reqlo(box[i],box[j])+error,f'sep_{i}_{j}_{owner}_{ax}_{sgn}')
    return np.array(rows),np.array(rhs),names,CB,hs,gs

def solve(box,pos,ch):
    A,B,names,CB,hs,gs=matrix(box,pos,ch)
    rr=linprog(np.r_[np.zeros(18),1.],A_ub=np.c_[A,-np.ones(len(B))],b_ub=B,bounds=[(None,None)]*19,method='highs',options={'presolve':True})
    if not rr.success:return None,None,(A,B,names,CB,hs,gs)
    if rr.x[-1]>1e-7:
        lam=-rr.ineqlin.marginals;terms=[(int(i),int(round(v*2**40))) for i,v in enumerate(lam) if round(v*2**40)>0]
        ll=np.zeros(len(B))
        for i,v in terms:ll[i]=v/2**40
        reserve=-ll@B-rho*sum(abs(ll@A))
        if reserve>1e-8:return {'weights':terms,'power':40,'discovery_reserve':float(reserve)},rr.x[:18],(A,B,names,CB,hs,gs)
    return None,rr.x[:18],(A,B,names,CB,hs,gs)

def select(box,pos,ch,point,data):
    A,B,names,CB,hs,gs=data
    if point is None:return ('angle',int(np.argmax([u-l for l,u in box])))
    c=point.reshape(9,2);ts=np.array([(l+u)/2 for l,u in box]);alpha=1/np.sqrt(1+ts*ts);beta=ts*alpha
    u=np.stack((alpha,beta),axis=1);v=np.stack((-beta,alpha),axis=1)
    selected={(p,k):val for p,k,val in ch}
    # Inscribed aligned-square disjunctions have no uncertain normals.
    candidates=[]
    for p in PAIRS:
        i,j=p;d=c[j]-c[i];gap=gs[i]+gs[j]-max(abs(d))
        if (p,'proxy') not in selected and gap>1e-6:candidates.append((gap,p))
    if candidates:return ('proxy',max(candidates)[1])
    bad=[]
    for p in PAIRS:
        i,j=p;d=c[j]-c[i];normals=np.array([u[i],v[i],u[j],v[j]])
        req=.5*(1+abs(u[i]@u[j])+abs(v[i]@u[j]));gap=req-max(abs(normals@d))
        if gap>1e-6:bad.append((gap,p))
    if bad:
        gap,p=max(bad);i,j=p
        if (p,'sat') not in selected:
            if max(box[i][1]-box[i][0],box[j][1]-box[j][0])<=.5:return ('sat',p)
            return ('angle',max((i,j),key=lambda k:box[k][1]-box[k][0]))
        owner=selected[(p,'sat')][0]
        # The owned normal error dominates; the other frame controls support.
        candidates=[owner,i,j]
        k=max(candidates,key=lambda k:box[k][1]-box[k][0])
        if box[k][1]-box[k][0]>.0078125:return ('angle',k)
        indices=[2*i,2*i+1,2*j,2*j+1]
        k=max(indices,key=lambda k:CB[k][1]-CB[k][0])
        if CB[k][1]-CB[k][0]>.015625:return ('position',k)
        return ('angle',max(candidates,key=lambda k:box[k][1]-box[k][0]))
    # Feasible midpoint poses may still violate original corners or exact widths.
    scores=[]
    for i in range(9):
        worst=max(np.sum((c[i]+.5*(ss*u[i]+tt*v[i]))**2)-Q for ss in (-1,1) for tt in (-1,1))
        scores.append(max(worst,0)*(box[i][1]-box[i][0]))
    if max(scores)>1e-9:return ('angle',int(np.argmax(scores)))
    return ('angle',int(np.argmax([u-l for l,u in box])))

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True);ap.add_argument('--nodes',type=int,default=2000);ap.add_argument('--depth',type=int,default=100);ap.add_argument('--resume',type=Path);args=ap.parse_args()
    start=time.time();rootbox=tuple([(-1.,1.)]*9);rootpos=tuple([(-rho,rho)]*18)
    stack=[(rootbox,rootpos,(),0,[])];leaves=[];front=[];nodes=0;maxdep=0;actions={};minres=1e9
    if args.resume:
        old=json.loads(args.resume.read_text());leaves=old['leaves'];nodes=old['nodes'];maxdep=old['max_depth'];actions=old['actions'];stack=[]
        for ff in old['frontier']:
            ch=tuple((tuple(p),k,tuple(v)) for p,k,v in ff['choices'])
            stack.append((tuple(map(tuple,ff['box'])),tuple(map(tuple,ff['position'])),ch,ff['depth'],ff['path']))
    while stack and nodes<args.nodes:
        box,pos,ch,dep,path=stack.pop();nodes+=1;maxdep=max(maxdep,dep)
        hit,point,data=solve(box,pos,ch)
        if hit:
            minres=min(minres,hit['discovery_reserve']);leaves.append({'box':box,'position':pos,'choices':ch,'path':path,**hit})
        elif dep>=args.depth:front.append({'box':box,'position':pos,'choices':ch,'depth':dep,'path':path})
        else:
            kind,k=select(box,pos,ch,point,data);actions[kind]=actions.get(kind,0)+1
            if kind=='proxy':
                for ax in (0,1):
                    for sg in (-1,1):
                        val=(ax,sg);cc=ch+((k,'proxy',val),);stack.append((box,pos,cc,dep+1,path+[['proxy',list(k),list(val)]]))
            elif kind=='sat':
                for owner in k:
                    for ax in (0,1):
                        for sg in (-1,1):
                            val=(owner,ax,sg);cc=ch+((k,'sat',val),);stack.append((box,pos,cc,dep+1,path+[['sat',list(k),list(val)]]))
            else:
                source=box if kind=='angle' else pos;l,u=source[k]
                # Use full box midpoint; child union retains every boundary face.
                m=(l+u)/2
                for side,(ll,uu) in enumerate(((l,m),(m,u))):
                    new=list(source);new[k]=(ll,uu)
                    stack.append((tuple(new) if kind=='angle' else box,pos if kind=='angle' else tuple(new),ch,dep+1,path+[[kind,k,side]]))
        if nodes%100==0:print(nodes,'leaves',len(leaves),'stack',len(stack),'front',len(front),'depth',maxdep,'seconds',round(time.time()-start,1),'actions',actions,flush=True)
    front.extend({'box':bo,'position':po,'choices':ch,'depth':dep,'path':path} for bo,po,ch,dep,path in stack)
    out={'proof':False,'scope':'Floating original full-nine remaining bulk; exact replay required; frontier must be empty','target_transverse':globals().get('TARGET_TRANSVERSE','5/8'),'nodes':nodes,'max_depth':maxdep,'seconds':time.time()-start,'actions':actions,'leaves':leaves,'frontier':front,'minimum_discovery_reserve':minres,'directions':DIRS}
    args.out.write_text(json.dumps(out,separators=(',',':'))+'\n')
    print('DONE',nodes,len(leaves),len(front),'depth',maxdep,'seconds',time.time()-start,flush=True)

if __name__=='__main__':main()
