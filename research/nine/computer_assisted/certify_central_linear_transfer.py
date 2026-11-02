"""Exact two-variable central transfer for outer slopes29/2 and16.

Only rational arithmetic and directed square-root bounds certify leaves.
This is independent of all endpoint/central normal-owner choices.
"""
import argparse,json,time
from fractions import Fraction as F
from pathlib import Path
from joint_five_interval import D,V,S,minimum,maximum,choose_hull

ROOTS=[(F(-6),F(0),F(-6),F(0)),(F(-6),F(0),F(0),F(6)),(F(0),F(6),F(0),F(6))]
def formula(box):
    x=D(V(box[0],box[1]),[1,0,0,0]);y=D(V(box[2],box[3]),[0,1,0,0])
    ax=x.abs();ay=y.abs();ss=x+y;s=ss.abs();p=(x+ax+y+ay)/2;n=(-x+ax-y+ay)/2
    qx=1+x.square();qy=1+y.square();dx=qx.sqrt();dy=qy.sqrt();ap=(x*y-1).abs()
    m2=minimum([(qx+ap+s)/(2*dx),(qy+ap+s)/(2*dy)])
    m3=minimum([1+maximum([p,n]),(qx+ap+s*(2+ax))/(2*dx),(qy+ap+s*(2+ay))/(2*dy)])
    target=1+F(29,27)*p-F(32,27)*n
    pos=maximum([m3+ss/10-target,m3+ss/10-F(61,60)*(dx+dy)])
    neg=maximum([m3-F(133,64)*s,m2-F(91,60)*s])-target
    if ss.v.l>=0:return pos
    if ss.v.h<=0:return neg
    # The actual function switches at S=0. Its two branch values agree
    # there; a hull encloses its values and one-sided derivatives on a
    # crossing box. Taking their minimum would describe another function
    # whose midpoint value could not be mixed with this branch selection.
    return choose_hull([pos,neg])
def lower(box):
    whole=formula(box);mid=[(box[0]+box[1])/2,(box[2]+box[3])/2]
    center=formula(tuple(t for m in mid for t in[m,m])).v
    for j,m in enumerate(mid):center+=whole.g[j]*V(box[2*j]-m,box[2*j+1]-m)
    return max(whole.v.l,center.l),whole

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--max-nodes',type=int,default=200000);ap.add_argument('--resume',action='store_true');ap.add_argument('--out');args=ap.parse_args()
    out=Path(args.out) if args.out else Path(__file__).with_name('central_linear_transfer_compact.json');nodes=[{'box':list(map(str,bb))}for bb in ROOTS];stack=[(i,b,0)for i,b in reversed(list(enumerate(ROOTS)))];processed=closed=0;start=last=time.monotonic()
    if args.resume:
        d=json.loads(out.read_text());nodes=d['nodes'];processed=d['processed'];closed=d['closed'];stack=[(p['node'],tuple(map(F,nodes[p['node']]['box'])),p['depth'])for p in d['pending']]
    stop=processed+args.max_nodes
    def save(status):
        out.write_text(json.dumps({'type':'central_linear_transfer_cover_v1','proof_status':status,'positive_outer_coefficient':'29/2','negative_outer_coefficient':'16','Q':'1105/256','r_upper':'133/64','rho_upper':'91/60','floor':'1/10','root_indices':[0,1,2],'nodes':nodes,'pending':[{'node':i,'depth':dep}for i,bb,dep in stack],'remaining':len(stack),'processed':processed,'closed':closed},separators=(',',':'))+'\n')
    while stack and processed<stop:
        idx,box,depth=stack.pop();processed+=1
        if box[1]+box[3]<=0:
            nodes[idx]['terminal']='nonpositive_signed_sum';closed+=1;continue
        if box[1]<=0<=box[2] or box[3]<=0<=box[0]:
            nodes[idx]['terminal']='mixed_sign_triangle';closed+=1;continue
        if box[0]+box[2]>=-1 and box[1]+box[3]<=1:
            nodes[idx]['terminal']='signed_sum_strip';closed+=1;continue
        lo,dd=lower(box)
        if lo>0:nodes[idx]['lower']=str(F(lo,S));closed+=1
        else:
            if depth>=60:
                stack.append((idx,box,depth));save('incomplete_depth_limit');print('UNRESOLVED',box,float(F(lo,S)),flush=True);return
            widths=[float(box[2*j+1]-box[2*j])*max(abs(dd.g[j].l),abs(dd.g[j].h))/S for j in range(2)];dim=max(range(2),key=lambda j:widths[j]);m=(box[2*dim]+box[2*dim+1])/2;left=list(box);right=list(box);left[2*dim+1]=m;right[2*dim]=m;li=len(nodes);ri=li+1;nodes.extend([{'box':list(map(str,left))},{'box':list(map(str,right))}]);nodes[idx].update(split=dim,children=[li,ri]);stack.extend([(ri,tuple(right),depth+1),(li,tuple(left),depth+1)])
        now=time.monotonic()
        if now-last>20:save('incomplete_checkpoint');print('CENTRAL',processed,'closed',closed,'pending',len(stack),'seconds',round(now-start,1),flush=True);last=now
    save('producer_complete_pending_independent_replay'if not stack else'incomplete_node_budget');print('FINISH CENTRAL',processed,'closed',closed,'pending',len(stack),'seconds',round(time.monotonic()-start,1),flush=True)

if __name__=='__main__':main()
