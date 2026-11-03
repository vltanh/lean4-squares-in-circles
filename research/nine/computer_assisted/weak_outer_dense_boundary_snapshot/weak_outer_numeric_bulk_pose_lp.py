#!/usr/bin/env python3
"""DISCOVERY ONLY: coupled original-frame LP relaxation for the full bulk.

Unlike scalar width boxes, each original cos/sin and abs(sin) is a shared
LP variable in every corner, chain, pair cap and chosen physical separator.
Finite proofs require an independent rational reconstruction and replay.
"""
from math import sqrt
import numpy as np
from scipy.optimize import linprog
import weak_outer_numeric_bulk_lp as base

Q=base.Q;rho=base.rho;a=base.a;b=base.b;N=54
CONTEXT_VERSION='left_angles_7_40_v1'
base.TARGET_TRANSVERSE='2/3'
AL=lambda i:18+i
BE=lambda i:27+i
AB=lambda i:36+i
GI=lambda i:45+i
DENSE_HALF_TANGENTS=(0,1609,3220,4834,6455,8083,9721,11372,13036,14717,
    16416,18136,19880,21650,23449,25280,27146,29050,30996,32988,
    35030,37126,39281,41500,43790,46156,48605,51145,53784,56532,59398,62395)
def dense_directions():
    # Exact Pythagorean unit directions; the checker uses rational arithmetic.
    den=1<<16;ans=[]
    for turn in range(4):
        for num in DENSE_HALF_TANGENTS:
            ss=den*den+num*num;p=(den*den-num*num)/ss;q=2*den*num/ss
            for _ in range(turn):p,q=-q,p
            ans.append((p,q))
    return tuple(ans)
DENSE_DIRS=dense_directions()

def matrix(box,pos,choices):
    N=54+6*sum(kind=='sat' for pair,kind,ch in choices)
    # Derived sign restrictions use the ORIGINAL strict weak CD bit, not
    # the closed LP relaxation of that bit. Every omitted owner has the
    # explicit pen-and-paper impossibility proof in CONE_SEPARATOR_SIGNS.
    effective=list(box);forbidden=None
    # This changes interval coefficients, so every new leaf carries an
    # explicit context version. Old leaves retain their original context in
    # the independent verifier. Actual main spans give h_A+h_B<=R-1,
    # hence |tan(theta_A)|,|tan(theta_B)|<7/40.
    for owner in (0,1):
        l,u=effective[owner];ll=max(l,-7/40);uu=min(u,7/40)
        if ll>uu:forbidden='accepted_left_main_angle_bound'
        else:effective[owner]=(ll,uu)
    product_cursor=54
    def product_rows(z,U,V,UB,VB,name):
        ul,uu=UB;vl,vu=VB
        def scale(E,c):return [(i,c*v) for i,v in E]
        add([(z,-1)]+scale(V,ul)+scale(U,vl),ul*vl,name+'_lower_ll')
        add([(z,-1)]+scale(V,uu)+scale(U,vu),uu*vu,name+'_lower_uu')
        add([(z,1)]+scale(V,-uu)+scale(U,-vl),-uu*vl,name+'_upper_ul')
        add([(z,1)]+scale(V,-ul)+scale(U,-vu),-ul*vu,name+'_upper_lu')
    for pair,kind,ch in choices:
        if kind!='sat':continue
        owner,axis,sg=ch
        if pair==(2,3):
            if sg<0:forbidden='weak_cone_backward_or_downward_steep'
            elif effective[3][0]>=0 and owner==2:
                if axis==1:forbidden='accepted_positive_D_excludes_steep_C_owner'
                elif effective[2][1]<=0:forbidden='accepted_positive_D_excludes_downward_C_owner'
            elif axis==1:
                l,u=effective[owner]
                if l>=0:forbidden='weak_cone_upward_steep_requires_negative_tilt'
                else:effective[owner]=(l,min(u,0.))
        if pair==(3,6):
            if axis==1 and sg<0:forbidden='accepted_DG_normal_upward'
            elif axis==0:
                l,u=effective[owner]
                if sg>0:
                    if u<=0:forbidden='accepted_DG_normal_upward'
                    else:effective[owner]=(max(l,0.),u)
                else:
                    if l>=0:forbidden='accepted_DG_normal_upward'
                    else:effective[owner]=(l,min(u,0.))
    box=tuple(effective)
    if forbidden:
        hs=[base.hbounds(T) for T in box];gs=[.25/h[1] for h in hs]
        return np.zeros((1,N)),np.array([-1.]),[forbidden],list(pos),hs,gs
    CB,hs,gs=base.center_bounds(box,pos,choices);rows=[];rhs=[];names=[]
    def add(entries,rv,name):
        co=np.zeros(N)
        for k,v in entries:co[k]+=v
        rows.append(co);rhs.append(rv);names.append(name)
    for k,(l,u) in enumerate(CB):
        add([(k,1)],u,'bound_up_'+str(k));add([(k,-1)],-l,'bound_lo_'+str(k))
    for i,(tl,tu) in enumerate(box):
        aa,bb=base.nbounds(box[i],0,1)
        for var,rr in ((AL(i),aa),(BE(i),bb),(AB(i),(max(0,base.beta_lo(box[i])),max(abs(bb[0]),abs(bb[1])))),(GI(i),(gs[i],.25/hs[i][0]))):
            add([(var,1)],rr[1],f'pose_up_{var}');add([(var,-1)],-rr[0],f'pose_lo_{var}')
        add([(AL(i),-1),(AB(i),-1)],-2*hs[i][0],f'width_lower_{i}')
        add([(AL(i),1),(AB(i),1)],2*hs[i][1],f'width_upper_{i}')
        add([(AB(i),1),(AL(i),-1)],0,f'fold_order_{i}')
        for ax in (0,1):
          for sg in (-1,1):
            add([(2*i+ax,sg),(AL(i),.5),(AB(i),.5)],sqrt(Q)+1e-12,f'axis_support_shared_width_{i}_{ax}_{sg}')
        # Convex hull of the original |beta| graph on this beta interval.
        add([(BE(i),1),(AB(i),-1)],0,f'abs_pos_{i}')
        add([(BE(i),-1),(AB(i),-1)],0,f'abs_neg_{i}')
        if tl>=0:add([(AB(i),1),(BE(i),-1)],0,f'abs_equal_pos_{i}')
        elif tu<=0:add([(AB(i),1),(BE(i),1)],0,f'abs_equal_neg_{i}')
        else:
            bl,bu=bb;slope=(bu+bl)/(bu-bl);intercept=-2*bu*bl/(bu-bl)
            add([(AB(i),1),(BE(i),-slope)],intercept+1e-11,f'abs_chord_{i}')
        for p,q in base.DIRS:
            add([(AL(i),p),(BE(i),q)],sqrt(p*p+q*q)+1e-12,f'unit_disk_{i}_{p}_{q}')
        ul=np.array([1.,tl])/sqrt(1+tl*tl);uu=np.array([1.,tu])/sqrt(1+tu*tu)
        nm=np.round((ul+uu)*2**30)/2**30
        low=min(nm@ul,nm@uu)-1e-11
        add([(AL(i),-nm[0]),(BE(i),-nm[1])],-low,f'arc_chord_{i}')
        # g=1/[2(alpha+|beta|)] lies above every reciprocal tangent.
        for ss in (1.,9/8,5/4,11/8,3/2):
            co=-1/(2*ss*ss)
            add([(GI(i),-1),(AL(i),co),(AB(i),co)],-1/ss,f'inset_tangent_{i}_{ss}')
        for p,q in base.DIRS:
            bound=sqrt(Q*(p*p+q*q))+1e-12
            for s in (-1,1):
              for t in (-1,1):
                add([(2*i,p),(2*i+1,q),(AL(i),(s*p+t*q)/2),(BE(i),(s*q-t*p)/2)],bound,f'corner_support_{i}_{p}_{q}_{s}_{t}')
    for i,j,bit in base.EDGES:
        for sy in (-1,1):add([(2*i,1),(2*j,-1),(2*i+1,sy),(2*j+1,-sy)],0,f'cone_{i}_{j}_{sy}')
        widths=[(GI(i),1),(GI(j),1)] if bit else [(AL(i),.5),(AB(i),.5),(AL(j),.5),(AB(j),.5)]
        add([(2*i,1),(2*j,-1)]+widths,0,f'chain_{i}_{j}')
    add([(6,1),(4,-1),(AL(2),-.5),(AB(2),-.5),(AL(3),-.5),(AB(3),-.5)],0,'CD_weak')
    add([(5,1),(7,-1)],-5/8,'CD_big_transverse')
    add([(7,1),(13,-1)],0,'accepted_G_above_D')
    add([(7,1),(13,-1),(AL(3),7/16),(AB(3),7/16),(AL(6),7/16),(AB(6),7/16)],41/120,'DG_width_clearance')
    add([(12,-1),(AL(6),.5),(AB(6),.5)],-101/432,'accepted_G_edge')
    add([(4,1),(AL(2),-.5),(AB(2),-.5)],5/64,'accepted_C_edge')
    add([(14,1),(16,-1)],0,'extras_x_order')
    add([(4,-a),(12,-b),(AL(2),a/2),(AB(2),a/2),(AL(6),b/2),(AB(6),b/2)],-6.75,'left_cap_and_chains')
    add([(6,1),(12,-1)],1459/1728,'DG_horizontal_cap')
    add([(6,-1),(12,1)],1459/1728,'DG_horizontal_cap_other')
    for i in range(9):
      for j in range(9):
        if i==j:continue
        pose=[(AL(i),-a/2),(AB(i),-a/2+4),(AL(j),-b/2),(AB(j),-b/2)]
        for axis in (0,1):
          for sg in (-1,1):
            add([(2*i+axis,sg*a),(2*j+axis,sg*b)]+pose,211/4,f'all_pair_cap_{i}_{j}_{axis}_{sg}')
    budget=[(AL(1),a),(AB(1),a),(AL(2),a/2),(AB(2),a/2),(GI(2),a),(AL(5),b),(AB(5),b),(AB(0),4),(AB(3),4),(AL(3),-a/2),(AB(3),-a/2),(GI(3),a)]
    add(budget,2*a+b,'orientation_budget')
    if box[3][0]>=0:
        # Complete signed cap after the accepted G>D order theorem.
        k=207/16
        add([(6,a),(12,b),(AL(3),a/2),(BE(3),a/2-k),(AL(6),-b/2),(AB(6),-b/2)],211/4+a,'signed_right_cap')
        signedbudget=[(j,c) for j,c in budget]+[(AB(3),-4),(AL(3),a),(BE(3),a-k)]
        add(signedbudget,3*a+b,'signed_orientation_budget')
    for pair,kind,ch in choices:
        i,j=pair
        if kind=='proxy':
            ax,sg=ch;add([(2*i+ax,sg),(2*j+ax,-sg),(GI(i),1),(GI(j),1)],0,f'proxy_{i}_{j}_{ax}_{sg}')
        else:
            owner,ax,sg=ch;nn=base.nbounds(box[owner],ax,sg)
            nm=np.round(np.array([(l+u)/2 for l,u in nn])*2**30)/2**30
            dr=[]
            for xy in (0,1):
                lo=CB[2*j+xy][0]-CB[2*i+xy][1];hi=CB[2*j+xy][1]-CB[2*i+xy][0]
                if pair==(2,3):lo=max(lo,gs[2]+gs[3] if xy==0 else 5/8);hi=min(hi,31/30)
                if pair==(3,6) and xy==0:lo=max(lo,-1459/1728);hi=min(hi,1459/1728)
                if pair==(3,6) and xy==1:lo=max(lo,0)
                dr.append((lo,hi))
            d0=np.round(np.array([(l+u)/2 for l,u in dr])*2**30)/2**30
            upper=sum(base.mulup(nn[k],dr[k]) for k in (0,1))
            add([],upper-base.reqlo(box[i],box[j]),f'sep_projection_upper_{i}_{j}_{owner}_{ax}_{sg}')
            error=sum(base.mulup((nn[k][0]-nm[k],nn[k][1]-nm[k]),(dr[k][0]-d0[k],dr[k][1]-d0[k])) for k in (0,1))
            pose=[(AL(owner),-sg*d0[0]),(BE(owner),-sg*d0[1])] if ax==0 else [(BE(owner),sg*d0[0]),(AL(owner),-sg*d0[1])]
            if pair==(3,6):
                add([(BE(owner),-sg)] if ax==0 else [(AL(owner),-sg)],0,f'accepted_DG_normal_up_{owner}_{ax}_{sg}')
            add([(2*i,nm[0]),(2*i+1,nm[1]),(2*j,-nm[0]),(2*j+1,-nm[1])]+pose,-base.reqlo(box[i],box[j])+error-d0@nm,f'sep_{i}_{j}_{owner}_{ax}_{sg}')
            # Full McCormick envelopes preserve shared original frame and
            # center variables in both separator projection and pair support.
            z=list(range(product_cursor,product_cursor+6));product_cursor+=6
            normal=[[(AL(owner),sg)],[(BE(owner),sg)]] if ax==0 else [[(BE(owner),-sg)],[(AL(owner),sg)]]
            for xy in (0,1):
                diff=[(2*j+xy,1),(2*i+xy,-1)]
                product_rows(z[xy],normal[xy],diff,nn[xy],dr[xy],f'product_nd_{i}_{j}_{xy}')
            ai,bi=base.nbounds(box[i],0,1);aj,bj=base.nbounds(box[j],0,1)
            for target,U,V,UB,VB,label in (
                (z[2],AL(i),AL(j),ai,aj,'aa'),(z[3],BE(i),BE(j),bi,bj,'bb'),
                (z[4],AL(i),BE(j),ai,bj,'ab'),(z[5],BE(i),AL(j),bi,aj,'ba')):
                product_rows(target,[(U,1)],[(V,1)],UB,VB,f'product_frame_{i}_{j}_{label}')
            for signed in (-1,1):
                add([(z[0],-2),(z[1],-2),(z[2],1),(z[3],1),(z[4],signed),(z[5],-signed)],-1,f'full_physical_sep_{i}_{j}_{signed}')
            add([(z[0],-1),(z[1],-1)],-base.reqlo(box[i],box[j]),f'full_physical_sep_req_{i}_{j}')
            add([(z[2],-1),(z[3],-1)],0,f'relative_cos_nonnegative_{i}_{j}')
            add([(z[2],1),(z[3],1)],1,f'relative_cos_upper_{i}_{j}')
            for signed in (-1,1):add([(z[4],signed),(z[5],-signed)],1,f'relative_sin_bound_{i}_{j}_{signed}')
    # Append-only strengthening: the ORIGINAL folded pair (alpha,|beta|)
    # lies on the quarter-circle, even when the signed beta box crosses zero.
    # The rational chord follows by concavity: its endpoint values are 1 and
    # 17/(12*sqrt(2))>1.  Previous leaf row indices remain unchanged.
    for i in range(9):
        add([(AL(i),-1),(AB(i),-5/12)],-1,f'folded_rational_chord_{i}')
        for p,q in base.DIRS:
            if p>=0 and q>=0:
                add([(AL(i),p),(AB(i),q)],sqrt(p*p+q*q)+1e-12,f'folded_unit_support_{i}_{p}_{q}')
    # Accepted left-main inset barrier: g_A-|y_A|>3/40.
    add([(1,1),(GI(0),-1)],-3/40,'left_main_inset_barrier_up')
    add([(1,-1),(GI(0),-1)],-3/40,'left_main_inset_barrier_down')
    # Every original center is in the radius-rho disk. Every two original
    # centers have Euclidean distance at least 1 (inscribed radius-1/2 disks).
    for i in range(9):
        for p,q in base.DIRS:
            add([(2*i,p),(2*i+1,q)],rho*sqrt(p*p+q*q)+1e-12,f'original_center_disk_{i}_{p}_{q}')
        for j in range(i+1,9):
            ll,uu=CB[2*j][0]-CB[2*i][1],CB[2*j][1]-CB[2*i][0]
            vv,ww=CB[2*j+1][0]-CB[2*i+1][1],CB[2*j+1][1]-CB[2*i+1][0]
            # z^2 <= (lower+upper)z-lower*upper on each true interval.
            add([(2*i,ll+uu),(2*j,-ll-uu),(2*i+1,vv+ww),(2*j+1,-vv-ww)],-1-ll*uu-vv*ww,f'original_center_distance_secant_{i}_{j}')
    # Original D/G aligned insets cannot separate horizontally; G>D fixes
    # their vertical order. This complements the affine width clearance.
    add([(7,1),(13,-1),(GI(3),1),(GI(6),1)],0,'DG_original_inset_clearance')
    # Both original D-chirality low-gap proofs now cover v<=2/3.
    # Retain old weaker rows/intervals to preserve all earlier leaf indices.
    add([(5,1),(7,-1)],-2/3,'remaining_bulk_transverse_two_thirds')
    # Accepted positive-D owner reduction: a surviving C-owned shallow
    # axis points upward, so its original abs-beta graph has positive sign.
    if box[3][0]>=0 and any(pair==(2,3) and kind=='sat' and ch==(2,0,1) for pair,kind,ch in choices):
        add([(BE(2),-1)],0,'positive_D_C_owned_normal_upward')
        add([(AB(2),1),(BE(2),-1)],0,'positive_D_C_owned_abs_sign')
    # Append a dense exact-rational unit-direction family for EVERY original
    # corner. Sparse primitive directions alone leave a fixed polygon error
    # which orientation refinement cannot remove.
    for i in range(9):
        for direction,(p,q) in enumerate(DENSE_DIRS):
            for s in (-1,1):
                for t in (-1,1):
                    add([(2*i,p),(2*i+1,q),(AL(i),(s*p+t*q)/2),(BE(i),(s*q-t*p)/2)],sqrt(Q)+1e-12,f'dense_original_corner_{i}_{direction}_{s}_{t}')
    return np.array(rows),np.array(rhs),names,CB,hs,gs

def solve(box,pos,ch):
    A,B,names,CB,hs,gs=matrix(box,pos,ch)
    N=A.shape[1]
    rr=linprog(np.r_[np.zeros(N),1.],A_ub=np.c_[A,-np.ones(len(B))],b_ub=B,bounds=[(None,None)]*(N+1),method='highs',options={'presolve':True,'threads':1})
    if not rr.success:return None,None,(A,B,names,CB,hs,gs)
    if rr.x[-1]>1e-7:
        lam=-rr.ineqlin.marginals
        terms=[(int(i),int(round(v*2**40))) for i,v in enumerate(lam) if round(v*2**40)>0]
        ll=np.zeros(len(B))
        for i,v in terms:ll[i]=v/2**40
        bounds=np.r_[np.full(18,rho),np.ones(36),np.tile([2*rho,2*rho,1,1,1,1],(N-54)//6)]
        reserve=-ll@B-bounds@abs(ll@A)
        if reserve>1e-8:return {'weights':terms,'power':40,'context_version':CONTEXT_VERSION,'discovery_reserve':float(reserve)},rr.x[:18],(A,B,names,CB,hs,gs)
    return None,rr.x[:18],(A,B,names,CB,hs,gs)

if __name__=='__main__':
    original_select=base.select
    def select(box,pos,ch,point,data):
        if box[3][0]<0<box[3][1]:return ('angle',3)
        selected={(p,k) for p,k,val in ch}
        for pair in ((2,3),(3,6),(2,6)):
            if (pair,'sat') not in selected:return ('sat',pair)
        return original_select(box,pos,ch,point,data)
    base.matrix=matrix;base.solve=solve;base.select=select;base.main()
