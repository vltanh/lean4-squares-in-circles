#!/usr/bin/env python3
"""Independent 64-bit dyadic replay of each widened outer support cover.

Imports no wider producer or floating proposal code. All roots, physical
boxes, target branches, multiplier constraints and normal charts are
reconstructed here.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,sys,time

HERE=Path(__file__).resolve().parent
BASE=(HERE if (HERE/'verify_joint_five_dyadic.py').is_file()
      else HERE.parent/'pr11/research/nine/computer_assisted')
sys.path.insert(0,str(BASE))
import verify_joint_five_dyadic as ar

def initial(owner,chart):
    assert owner in('E','S') and chart in('up','left')
    width=F(1)if owner=='S'else F(7,100)
    return [(-width,width,F(-57),F(24))]

def free_bound(vector,penalties,box,endpoint=False,face=None):
    if face is None:face=[F(0)]*4
    lx,hx,ly,hy=face;xl,xh,yl,yh=box
    moved=[vector[0]+lx-hx,vector[1]+ly-hy]
    shift=-xl*lx+xh*hx-yl*ly+yh*hy
    cost=ar.orientation_min(penalties,endpoint)
    rectangle=((xl+xh)*vector[0]+(yl+yh)*vector[1]
               +(xh-xl)*vector[0].absolute()+(yh-yl)*vector[1].absolute())/2
    return ar.least([ar.R*ar.length(moved)-ar.orientation_min([moved,*penalties],endpoint)+shift,
                     ar.CENTER_RADIUS*ar.length(moved)-cost+shift,rectangle-cost])

def evaluate(box,row,owner,chart):
    assert row['den']==4096 and isinstance(row['k'],int)and row['k']>=0
    assert len(row['faces'])==4 and all(isinstance(v,int)and v>=0 for v in row['faces'])
    if owner=='E':assert len(row['efaces'])==4 and all(isinstance(v,int)and v>=0 for v in row['efaces'])
    w=ar.A(ar.I(box[0],box[1]),[1,0,0,0]);z=ar.A(ar.I(box[2],box[3]),[0,1,0,0])
    if chart=='up':normal=[-w,ar.A(1)];axis=[ar.A(1),w]
    else:normal=[ar.A(-1),w];axis=[ar.A(1),-w]
    k=F(row['k'],4096);b=F(27,2)
    ev=[46-k*normal[0],-k*normal[1]]
    sv=[b+k*normal[0],b*z+k*normal[1]]
    epens=[[ar.A(46),ar.A(0)],ar.times(k,normal)]
    spens=[[ar.A(b),b*z],ar.times(k,normal)]
    ebox=(F(89,60),F(91,60),F(-1,8),F(1,8))
    sbox=(F(0),F(13,12),F(3,5),F(91,60))
    if owner=='S':
        endpoint=free_bound(ev,epens,ebox,True)
        shoulder=ar.boxed_bound(sv,axis,sbox,[F(v,4096)for v in row['faces']])-ar.support_total(spens,axis)
    else:
        endpoint=ar.boxed_bound(ev,axis,ebox,[F(v,4096)for v in row['efaces']])-ar.support_total(epens,axis)
        shoulder=free_bound(sv,spens,sbox,face=[F(v,4096)for v in row['faces']])
    slope=F(29,2)*z+F(3,2)*ar.least([ar.A(0),ar.greatest([ar.A(-1),z])])
    return endpoint+shoulder-F(211,4)-slope

def upper(box,row,owner,chart):
    wide=evaluate(box,row,owner,chart);m=[(box[0]+box[1])/2,(box[2]+box[3])/2]
    center=evaluate(tuple(t for mm in m for t in(mm,mm)),row,owner,chart).x
    for j,mm in enumerate(m):center+=wide.der[j]*ar.I(box[2*j]-mm,box[2*j+1]-mm)
    return F(min(wide.x.hi,center.hi),ar.SCALE)

def verify(data,progress=False):
    assert data['type']=='wider_outer_support_cover_v1'
    assert data['proof_status']=='producer_complete_pending_independent_replay'
    assert data['Q']=='1105/256'and data['T']=='211/4'and data['b']=='27/2'
    assert data['local_epsilon']=='1/80'and data['shoulder_box']==['0','13/12','3/5','91/60']
    assert data['root_indices']==[0]and data['remaining']==0 and data['pending']==[]
    owner,chart=data['owner'],data['chart'];roots=initial(owner,chart)
    nodes,rows=data['nodes'],data['certificates'];todo=[(0,roots[0],0)]
    seen=set();numeric=analytic=0;maxdepth=0;largest=None;start=last=time.monotonic()
    while todo:
        i,expected,depth=todo.pop();assert isinstance(i,int)and 0<=i<len(nodes)and i not in seen
        seen.add(i);maxdepth=max(maxdepth,depth);node=nodes[i];box=tuple(map(F,node['box']));assert box==expected
        kinds=sum(name in node for name in('children','certificate','terminal'));assert kinds==1
        if 'children'in node:
            j=node['split'];assert isinstance(j,int)and j in(0,1)
            kids=node['children'];assert len(kids)==2 and kids[0]!=kids[1]
            mid=(box[2*j]+box[2*j+1])/2;left,right=list(box),list(box);left[2*j+1]=mid;right[2*j]=mid
            todo.extend([(kids[0],tuple(left),depth+1),(kids[1],tuple(right),depth+1)])
        elif 'terminal'in node:
            assert chart=='up'and node['terminal']=='local_unboxed_1_80'
            assert -F(1,80)<=box[0]<=box[1]<=F(1,80)and -F(1,80)<=box[2]<=box[3]<=F(1,80)
            analytic+=1
        else:
            index=node['certificate'];assert isinstance(index,int)and 0<=index<len(rows)
            u=upper(box,rows[index],owner,chart);assert u<0,(i,str(u),box)
            numeric+=1;largest=u if largest is None else max(largest,u)
        now=time.monotonic()
        if progress and now-last>=25:
            print('WIDER REPLAY',owner,chart,'numeric',numeric,'analytic',analytic,'seconds',round(now-start,1),flush=True);last=now
    assert len(seen)==len(nodes)and numeric+analytic==data['closed']
    return {'owner':owner,'chart':chart,'nodes':len(seen),'interval_leaves':numeric,'analytic_leaves':analytic,'maximum_depth':maxdepth,'largest_replayed_upper':None if largest is None else str(largest),'complete':True,'seconds':time.monotonic()-start}

def main():
    path=Path(sys.argv[1]);raw=path.read_bytes();answer=verify(json.loads(raw),True)
    answer.update(proof_status='independent_wider_outer_replay_passed',certificate_sha256=hashlib.sha256(raw).hexdigest(),checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),arithmetic_sha256=hashlib.sha256(Path(ar.__file__).read_bytes()).hexdigest())
    path.with_name(path.stem+'_replay.json').write_text(json.dumps(answer,indent=2)+'\n');print(json.dumps(answer),flush=True)

if __name__=='__main__':main()
