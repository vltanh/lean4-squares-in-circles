# Closed boundary-side applications preserve the full adjacent tip-owned near-origin theorem

Date: October 28, 2026 UTC. Author: root continuation.

**Status: complete proposed local hand theorem and continuous closed-domain scalar extension, submitted for full independent review.** The physical boundary application Q is allowed to be the endpoint of its W side. Its original normal may then be free; no W-side normal is substituted in any force equation. The full original U3 and V2 are retained. A uniform scalar reserve, proved again in Appendix A, closes the only formerly strict side-length inequality needed for the near-origin conclusion.

## 1. Full original statement, geometric side chart and actual normal distinction

Put Q_*=1105/256 and assume 2<=R<=sqrt(Q_*). Retain the same actual pairwise interior-disjoint closed unit squares in D_R about the unchanged origin O, all their full original equations, true degrees, positive forces, physical circle corners, individual zero coefficients, directed normals, applications and full means.

U is unloaded true degree three with precisely the positive neighbors V,W,T. V is positively loaded true degree two with precisely the positive neighbors U,W. W is physically boundary with arbitrary true degree and load. T is any actual contained third neighbor, with arbitrary degree/load and no required boundary status.

In an actual own frame of U obtained by rotating or reflecting the whole packing about O, suppose

    U=[x-1,x] x [p-1,p],
    P=P_UV=(x,p), Q=P_UW=(x,p-1),
    n=n_UV=(a,b), a,b>0, a^2+b^2=1,
    m_0=n_UW=(c_0,-d_0), c_0,d_0>0, c_0^2+d_0^2=1.

The original UV normal is owned by V, and P is in that actual side's relative interior. Write k=Jn=(-b,a). The original VW normal is -k, with its actual application M in the relative interior of V's minimum-k side. The actual W geometry is assumed to have the following full chart:

    f=K*n+L*k, g=L*n-K*k,
    K,L>0, K^2+L^2=1,
    W=M+[-1,0]f+[0,1]g,
    M=Q+sigma*f, 0<sigma<=1.                        (1)

Thus Q is on the actual closed minimum-g side of W. At sigma=1 it is the actual vertex M-f. The vector g is a geometric inward W axis in this chart. It is not asserted to be the original UW normal m_0. If Q is in the side interior then support geometry forces m_0=g; at the newly included vertex m_0 may be a strict free normal. In either situation only m_0 occurs in the actual U force and torque equations. No new positive force or supporting normal is inserted.

**Local theorem.** The complete physical-mask domain satisfies

    0<x<61/60, 0<p<26/25,
    dist(O,U)<13/300,
    every actual U vertex has norm>7/100.           (3)

For unique physical V, every vertex in fact has norm>1/10. The complete physical-two V domain has

    0<p<1, dist(O,U)<1/60,                          (4)

with every original individual coefficient endpoint retained. The actual U lies wholly in the open disk of radius 3/2 and is physically circle-clear.

**Conditional near-three consequence.** This U cannot coexist with two other distinct actual units H,E satisfying

    dist(O,H),dist(O,E)<=1/40,
    every H and E vertex has norm>19/300.           (5)

No central or channel occupancy is inferred by the local theorem.

This theorem has an explicit physical side-chart premise (1); it does not yet classify every possible original VW normal. Its endpoint sigma=1 will be derived from the actual geometry in the free-UW application. The proof treats the closed endpoint algebraically, without approximating the packing by a family of unproved neighboring equilibria.

## 2. Full actual U3 gives a horizontal third force at every original feature

Let mu,nu,lambda>0 be the original UV,UW,UT magnitudes. The entire actual U force equation is

    mu*n+nu*m_0+lambda*r_T=0.

Its first component makes r_T=(-e,f_0) with e>0. The original third U support has horizontal coordinate x-1. If f_0=0 the normal is West and e=1; its actual side application or full shared mean remains unchanged.

If f_0>0 the original application is S=(x-1,p). Full torque about S gives mu*b+nu*(c_0-d_0)=0, and vertical force gives lambda*f_0=nu*c_0. Horizontal force gives lambda*e=mu*a+nu*c_0>lambda*f_0.

If f_0<0 write f_0=-h_0 with h_0>0. The original application is S=(x-1,p-1). Full torque gives mu*(b-a)-nu*d_0=0, and vertical force gives lambda*h_0=mu*a. Horizontal force gives lambda*e=mu*a+nu*c_0>lambda*h_0.

Thus the complete actual domain has

    e>|f_0|, e>1/sqrt(2)>7/10.                     (6)

The actual original m_0, rather than the geometric g from (1), occurs in every displayed equation. No force or mean at the possibly endpoint-valued Q was replaced.

## 3. Exact unit-support reach and a replacement for the West-side premise

We use the following force-free geometric fact.

**Unit-support translation lemma.** If S is any actual minimum-r support point of a unit square T and r is a unit vector, then

    S+r belongs to T.                               (7)

For a side-interior point, r is the inward own normal and translating by the full unit crosses to the opposite side at the same tangent parameter. This includes every actual side mean and both endpoints.

For a vertex, choose its two inward orthonormal own axes u,v. The support condition gives the nonnegative own-axis coordinates

    r=alpha*u+beta*v,
    alpha,beta>=0, alpha^2+beta^2=1.

Both alpha and beta lie in [0,1], so S+r is in the same actual unit. This also includes a normal-cone boundary. These two cases exhaust all actual support points and prove (7).

Apply (7) with the unchanged original S=P_UT and r=r_T. It is an actual minimum-r_T support point of T, even if its occurrence on T is an original shared-feature mean, a side point, a vertex, or a strict free vertex normal. Section 2 gives S_x=x-1. Containment of S+r_T therefore gives

    x-1-e>=-R,
    x>=1+e-R> -2/5.                                (8)

For the last strict comparison, use e>7/10 from (6) and

    R<21/10,
    (21/10)^2-Q_*=599/6400>0.

Equation (8) requires only actual containment at T. It replaces the earlier West-side horizontal-width estimate. No artificial support point, counterfactual terminal square, or smaller graph is introduced.

We record the resulting coordinate mechanism for later use. Suppose additionally that

    D=a*x+b*p>5/7, 0<p<26/25,
    Q=(x,p-1) belongs to a physical boundary unit.

If x<=0 then D=a*x+b*p<p, since 0<b<1. Hence

    5/7<p<26/25,
    |p-1|<2/7,
    |x|<2/5

by (8). The same unchanged Q would satisfy

    |Q|^2<4/25+4/49
          =1/4-41/4900<1/4.                       (9)

On the other hand a physical circle corner of its actual unit is at distance at most sqrt(2) from Q. Thus

    |Q|>=R-sqrt(2)>=2-sqrt(2)>1/2,

contradicting (9). Therefore

    x>0.                                           (10)

This mechanism preserves every physical boundary mask, including zero-weight corners. It uses no circle resultant or force equation at that boundary neighbor.

## 4. The entire closed geometric side chart and full physical V mask

The actual relative-interior UV point gives

    V=P+[0,1]n+[-rho,1-rho]k, 0<rho<1.

The actual VW point is

    M=P-rho*k+tau*n, 0<tau<1.                       (11)

This is the unchanged original application on V's minimum-k side. Compare it with M=Q+sigma*f and Q=P-North. Since North=b*n+a*k, exact coordinates give

    sigma*K=b+tau,
    sigma*L=a-rho,
    rho=a-(L/K)*(b+tau),
    0<tau<=K-b<K.                                  (12)

In particular rho<a and

    (a-rho)^2+(b+tau)^2=sigma^2<=1.                 (13)

All weak signs are intentional. The endpoint sigma=1 gives tau=K-b and is not discarded. Define the geometric global components g=(c,-d), where

    c=L*a+K*b>0,
    d=K*a-L*b=K*rho+L*tau>0,
    c^2+d^2=1.

These are coordinates of g, not a renaming of the original m_0. They imply K=ad+bc, L=ac-bd and kappa=d/K=a-(L/K)b>0 when those scalar symbols are used below. In the following inherited scalar notation, m=g and l=f denote only these two geometric W axes. No equilibrium equation is imposed with g or m in place of the original m_0.

Let omega>0 be the original VW magnitude, distinct from nu. The full true V2 force is

    F_V=mu*n+omega*k,

with both own components strictly positive. Its physical farthest coordinates therefore satisfy

    V=[X-1,X] times [Y-1,Y],
    X,Y>=1/2, X^2+Y^2=R^2,

    P=(D,E)=(X-1,Y-1+rho),
    M=(X-1+tau,Y-1).                                (14)

If one own center coordinate is zero, the two corresponding physical circle corners remain. Both cannot be zero because R>=2.

The mask X=1/2 is impossible here without a West-terminal hypothesis. Indeed Y-1=sqrt(R^2-1/4)-1>1/2, so the original world coordinate satisfies

    x=-a/2-b*(Y-1+rho)<-(a+b)/2<-1/2.

This contradicts (8). Thus the only physical-two possibility is Y=1/2. The unique mask has X,Y>1/2.

In the unique mask the full original V2 equation and torque give

    F_V=Lambda*(X,Y),
    mu*E=omega*(X-1+tau),

hence, with s=1-tau and r=Y/X,

    rho=1-r*s,
    E=Y*(1-s/X).                                    (15)

No equality (15) is imposed on the physical-two mask.

### 4.1. The complete W-face proof has no terminal premise

The full physical-mask entry 1e9e597a, Section 4, applies to the actual scalar data (12),(14): it uses only X,Y>=1/2, X^2+Y^2>=4, 0<tau<K, K,L>0, K^2+L^2=1, and W's physical boundary status.

For exact scope, M is strictly inside the circle because it is in the relative interior of V's own side. The other endpoint M-l has deficit

    R^2-|M-l|^2=2A X+2B Y-A^2-B^2,
    A=1+K-tau in(1,1+K), B=1+L.

The complete circle-arc and A-interval concavity proof there reduces the minimum at R=2 to

    (1+L)*(sqrt(15)-1-L),
    sqrt(15)-1-L-L^2,
    sqrt(15)-2-K+(sqrt(15)-2)*L,
    sqrt(15)-2-L+(sqrt(15)-2)*K,

all strictly positive. Convexity of squared norm puts the entire actual face [M-l,M] strictly inside. Thus the physical W mask is exactly among its opposite face endpoints,

    Z_+=M+m, Z_-=M-l+m.

Put

    C=1+L*(X-s)-K*(Y-1)>1/2,
    t=K*(X-s)+L*(Y-1).

The exact alternatives are

    Z_+ physical only if t>=1/2,  C^2+t^2=R^2;
    Z_- physical only if t<=1/2,  C^2+(t-1)^2=R^2.   (16)

Both physical endpoints are retained when t=1/2. No individual corner coefficient chooses the alternative.

Section 5 of the same source proves the force-free whole-domain consequence X>Y for every mask in (16). Its proof uses only this actual W-face chart, X,Y>=1/2 and R>=2; it uses neither a third U normal nor a terminal point. Its complete four circle-arc endpoint comparisons also include the physical ties.

Thus

    X>Y>=1/2, X>sqrt(2).                            (17)

The earlier X=1/2 exit above was printed independently to ensure that no historical terminal-West argument is being transferred.

### 4.2. Exact scope of the two unique-mask scalar imports

For a unique V mask with Z_+ physical, Section 6 of 1e9e597a proves

    X>sqrt(3), 1/2<Y<1                              (18)

on the wider closed interval 4<=R^2<=5. Its whole continuous proof uses the exact identity rho=a-(L/K)*(b+tau), a<1, b>0, 0<tau<K, (15), the actual plus-circle equation, and the radius; it never uses the strict sigma<1 inequality. It does not use any original U-to-T support, T force or degree, or the terminal formula displayed elsewhere in that source.

With (18), Sections 2--3 of the complete plus-port source 88f89381 prove

    kappa=d/K=a-(L/K)*b>2/3, hence a>2/3.           (19)

That complete scalar proof uses the actual plus-circle equation, rho=kappa-(L/K)*tau, positive tau, the radius, X>sqrt(3) and Y<1. It does not use tau<K-b or sigma<1, so it applies to the closed endpoint here. The later assertions about a boundary T port are not used here.

For a unique V mask with Z_- physical, Sections 2--3 of c0b1494d use (12),(15),(16) and R>=2 to prove

    z=L/K>2/3,
    r=Y/X<3/5,
    X>10/sqrt(34)>12/7.                             (20)

The first step is its complete affine-circle comparison on -1/2<t<=1/2. The ratio step applies the complete 692044eb scalar only after establishing L>1/2 and s>L/(L+Kr). Neither step uses sigma<1 or tau<K-b: the strict bound s>L/(L+Kr) follows from rho=a-(L/K)*(b+tau)<1-(L/K)*tau using a<1 and b>0. Nor does either step use the terminal formula, T boundary status, T force, the original terminal normal, or a loaded path. None of c0b1494d's later Section 6 terminal-moment conclusions is transferred.

These are proof-section exports at their full actual algebraic hypotheses, not invocations of old West-terminal theorems with a missing premise.

## 5. Entire unique-V/plus-W mask

Assume V is unique and Z_+ is physical; its W tie is included.

The exact actual data satisfy every hypothesis of the closed scalar theorem proved in Appendix A:

    X>0, 1/2<Y<=1, 4<=X^2+Y^2<=Q_*,
    a,b>0, a^2+b^2=1, a>=2/3,
    0<tau<1,
    rho=1-(Y/X)*(1-tau),
    (a-rho)^2+(b+tau)^2<=1.

Indeed (18),(19) give the first line and the a bound, while (12),(13),(15) give the exact original remaining identities, including the full closed side bound. Appendix A states on this entire enlarged continuous domain that

    p=b*(X-1)+a*Y-a*(Y/X)*(1-tau)<26/25.            (21)

Its proof explicitly requires no W equation or mask, terminal condition, or U force equation beyond the displayed scalar premises. The complete curvature and circle-arc arguments are reprinted in Appendix A with the closed inequality and all needed strict final reserves. They are not a limit of sampled physical configurations.

Equation (15) gives

    E>(1/2)*(1-1/sqrt(3))>1/5.

Together with D=X-1>sqrt(3)-1>5/7, the actual world coordinates obey

    x=aD-bE,
    p=bD+aE>0,
    p>aE>(2/3)*(1/5)=2/15.                          (22)

The exact squared comparison sqrt(3)>12/7 has reserve 3/49.

Apply the coordinate mechanism (8)--(10) to the original physical-boundary W point Q. It gives x>0 without any original terminal-axis or terminal-boundary premise. Since E>0,

    x<aD<D<61/60.                                   (23)

For the last upper comparison,

    X^2<=Q_*-Y^2<Q_*-1/4,
    (121/60)^2-(Q_*-1/4)=31/57600>0.

Thus the actual U in this entire mask has the required positive coordinates and p<26/25.

## 6. Entire unique-V/minus-W mask

Assume V is unique and Z_- is physical; again its physical W tie is included.

Only the scalar portions of the complete root injection c597a6c7 are used for the p bound. To make the import explicit, all of their premises follow here from (12),(15),(20):

    6/25<r<3/5,
    kappa=a-z*b>1-r>2/5,
    z>2/3,
    tau<=K-b,
    s=1-tau.

The lower r comparison follows from Y>1/2 and R^2<=Q_*:

    r^2>64/1041>36/625,
    64/1041-36/625=2524/650625>0.

Since K=1/sqrt(1+z^2)<3/sqrt(13)<5/6, the actual closed side condition gives

    s-b>=1-K>1/6.

Also b>=3/5 would imply a<=4/5 and

    kappa=a-z*b<4/5-(2/3)*(3/5)=2/5,

a contradiction. Therefore

    0<b<3/5, a>4/5.                                (24)

The unchanged coordinate is

    p=R*(b+a*r)/sqrt(1+r^2)-b-a*r*s.

Sections 3--6 of c597a6c7 prove the complete pure scalar consequence

    p<26/25                                         (25)

from precisely s-b>1/6, 6/25<r<3/5, 0<b<3/5, a=sqrt(1-b^2) and R^2<=Q_*. The strict intermediate comparison s-b>1-K in that older source is unnecessary: the closed endpoint here already gives the same strict s-b>1/6. That full proof covers both 0<b<=3/8 and 3/8<=b<3/5 continuously, including their common endpoint and every Y>1 possibility. It neither uses its later T-West width argument nor requires the original h=bc/K terminal-port identity. In particular there is no transfer of a terminal equation to the present arbitrary third feature.

For clarity, its comparison function is

    F(r,b)=sqrt(Q_*)*(b+a*r)/sqrt(1+r^2)
                          -b-a*r*(b+1/6),  p<F(r,b).

For b>=3/8 the full coefficient bound a*(b+1/6)>12/25 and its single concave circle comparison prove (25). For b<=3/8 the uniform derivative partial_r F>29/96 reduces to r=3/5, where the explicit whole b bound is

    F(3/5,b)<831/800=26/25-1/800.

All these scalar proofs are printed completely at the pinned input, and none contains a geometric condition on T.

From (15),(20),

    D=X-1>5/7,
    E> (1/2)*(1-7/12)=5/24,
    p>aE>(4/5)*(5/24)=1/6.                          (26)

The actual coordinate mechanism (8)--(10), using Q in W, now gives x>0. Finally E>0 and the same radius comparison as (23) give

    0<x<D<61/60.                                   (27)

This finishes the entire unique-minus mask, including the W tie. It does not assume Y<1, the additional zero-axis angle restriction L<K, or any particular third U vertex.

## 7. Entire physical-two V mask

The X=1/2 possibility was excluded in Section 4 using the actual m_0 third-force support bound. Hence every physical-two case has, in the actual V frame,

    V=[D,D+1] times [-1/2,1/2],
    P=(D,q), M=(D+tau,-1/2),
    q=rho-1/2,
    187/200<D<61/60.                                (28)

The full physical resultant is Lambda*(D+1,xi), where its two actual corner coefficients and F_V=mu*n+omega*k give

    0<xi<=1/2.

The original torque is

    mu*q=omega*(D+tau).

Consequently

    0<q<1/2,
    rho>1/2,
    (D+1)*q=xi*(D+tau)<=(D+tau)/2.                  (29)

The endpoint xi=1/2 is retained. No unique-circle relation (15) is imposed.

The complete local Sections 4--7 of acd1a2b5 apply at the actual W chart (1), rho=a-(L/K)*(b+tau), 0<tau<K, (28),(29), physical-boundary W and the radius window. Their scalar proofs never use sigma<1 or the stricter tau<K-b; the bound a>rho is still strict because L,b,tau are positive. They contain no terminal hypothesis or equation. We print the operative chain to separate it from that source's old West-side exit for X=1/2, which is not used.

### 7.1. Both W masks and the radial scalar domain

The actual W is

    W=M+[-1,0](K,L)+[0,1](L,-K).

Its m-center is positive. Writing

    zeta=K*(D+tau)-(1+L)/2,

the physical plus candidate requires zeta>=0 and the minus candidate requires zeta<=0. Their exact deficits are

    R^2-|Z_+|^2
       =2D*(1-L-tau)-tau^2-2L*tau-K,

    R^2-|Z_-|^2
       =2D*(1-L-tau+K)-tau^2
                         -2tau*(L-K)-(1+L+K).

If the minus point were physical, set H0=1-L-tau+K>0. Its circle equality gives the exact identity

    2zeta=tau*(1+L+2K-K*tau)/H0>0,

a contradiction. This also excludes a physical W tie. Therefore W has the unique physical circle corner Z_+ and

    D=(tau^2+2L*tau+K)/(2*(1-L-tau)),
    D>D0=(1+L)/(2K).                                (30)

The complete whole-interval scalar proof in acd1a2b5, Section 5, uses only (12),(29),(30) and the D bounds to establish

    z*tau<1/16, z=L/K<4/5, tau<3/7,
    rho<727/847, b>9/100.                            (31)

Its proof retains the entire weight inequality (29). It uses a positive quadratic-root comparison, one positive cubic bound, and monotonicity over whole intervals; no terminal port or T2 condition appears.

In particular (12),(29) give a>rho>1/2, hence b<sqrt(3)/2. The actual world coordinates therefore satisfy

    x=aD-bq>187/400-sqrt(3)/4>0,
    x<D<61/60,

    p=bD+a*q>bD>1683/20000>7/100.                   (32)

The squared reserve for the first strict comparison is 4969/160000.

### 7.2. The actual boundary-W point bounds the remaining coordinate

If p>=1, the unchanged Q=(x,p-1) satisfies

    |Q|^2=D^2+q^2+1-2p
          <(61/60)^2-3/4=1021/3600.

But its actual physical-boundary W gives

    |Q|>=R-sqrt(2)>=2-sqrt(2),
    (2-sqrt(2))^2>12/35>1021/3600,

with final rational reserve 1493/25200. Thus

    0<p<1.                                          (33)

Its actual vertical interval [p-1,p] contains zero in its interior. With 0<x<61/60, the actual hub has distance max(x-1,0)<1/60.

The right vertices P,Q lie in physical boundary units and have norm >1/2. The upper-left vertex has norm at least p>7/100. The lower-left vertex satisfies

    |(x-1,p-1)|>=sqrt(2)-|P|,
    |P|^2=D^2+q^2<(61/60)^2+1/4<(8/7)^2.

Thus its norm is greater than 7/5-8/7=9/35>7/100. These bounds prove (4) and the full four-vertex assertion throughout the entire physical-two domain.

The shared terminal mean and every possible third-normal feature were irrelevant to these local calculations; they remain unchanged.

## 8. The whole unique domain has the required distance and four-vertex margin

Sections 5--6 give, for either actual unique-V/W mask,

    0<x<61/60, 0<p<26/25.

Therefore the exact distance of the unchanged axis-aligned U is

    dist(O,U)^2=max(x-1,0)^2+max(p-1,0)^2
       <(1/60)^2+(1/25)^2=(13/300)^2.               (34)

This includes both x>=1 and p>=1 residual strips.

The original right vertices P,Q belong to actual physical boundary V,W. Their norms exceed 1/2. The upper-left vertex has norm at least p, and (22),(26) give

    p>min(2/15,1/6)=2/15>1/10.

For the lower-left vertex, suppose

    |(x-1,p-1)|<=1/10.

Then x,p>=9/10. Since D=a*x+b*p and a+b>1,

    D>9/10.

The actual unique V circle corner is

    Z_V=P+n+(1-rho)*k.

The actual quantities E=P.k and 1-rho are strictly positive, by (15). Hence

    R^2=|P|^2+1+2D+(1-rho)^2+2E*(1-rho)
        >|P|^2+1+2D
        >=2*(9/10)^2+1+2*(9/10)
         =221/50>Q_*,

whose final exact reserve is 663/6400. This contradicts containment. Thus the lower-left vertex has norm strictly greater than 1/10.

Every unique-mask vertex has norm >1/10>7/100. Section 7 established >7/100 for the complete physical-two mask. Together these prove every assertion in (3), with the stronger radial distance (4).

## 9. Complete two-near-unit exclusion

The separately reviewed radius-free theorem UNEQUAL_NEAR_ORIGIN_UNIT_ANGULAR_BUDGET.md, Section 4, covers three actual interior-disjoint units whose distances are at most 1/40,1/40,13/300 and whose every vertex has norm greater than 19/300.

For completeness, on that same circle of radius d0=19/300 the normalized distances are

    15/38, 15/38, 13/19.

If alpha=acos(15/38), beta=acos(13/19), then

    cos(2alpha)=-497/722,
    cos(pi-beta)=-494/722.

The strict reserve 3/722 gives 2alpha+beta>pi, contradicting the total available angular measure. The complete theorem includes an origin in a square, on its side, or outside it; no connectedness shortcut is used.

The actual U from (3) supplies the third unit, since

    7/100>19/300, 7/100-19/300=1/150.

The actual H,E in (5) would supply the other two. This proves the stated corollary, including equality in their distance bounds, without moving a square or changing a physical force.

## 10. Whole-square clearance, exact closed-domain changes and review boundary

Every actual point of U lies within sqrt(2) of an actual nearest point to O. The proved distance therefore gives

    |z|<sqrt(2)+13/300<3/2,
    3/2-99/70-13/300=89/2100>0.

Thus U is physically circle-clear even if an initially permitted physical corner had coefficient zero. This is a geometric conclusion about the whole square.

Three changes from the earlier strict-side theorem have been proved explicitly. First, Section 2 uses the actual UW normal m_0 in the entire U3 and nowhere substitutes the geometric side axis g. Its horizontal-support conclusion is independent of whether W owns m_0. Second, Section 4 keeps sigma=1 and the weak tau<=K-b. The W-face, X>Y, plus Y<1, plus kappa>2/3, minus z>2/3 and ratio proofs use only their displayed identities and the still-strict tau<K, rho<a and a<1,b>0; their actual proof-section hypotheses were checked. The minus height bound still has s-b>=1-K>1/6, and the radial scalar proof never uses sigma<1. Third, Appendix A proves the plus height bound at the closed side norm <=1 with the final uniform reserve intact.

The operative mathematical sections of the prior all-mask adjacent near-origin proof and each scalar export were read in this continuation. The complete ratio scalar and complete plus-port source were read, and the full relevant plus/minus/radial scalar arguments were checked. The inherited entire component proofs and independent reviews keep their existing acceptance boundary. This new document does not claim a fresh recursive full read of all historical sources or reviews, and none of their narrower original physical theorem statements is invoked outside its hypotheses. The explicit pure scalar proof sections, whose hypotheses are identified above, are the operative imports.

The new full local theorem and its exact actual-normal distinction require separate independent review. No original four-load allocation, closing-pocket capacity or full original graph/load flag is claimed by this manuscript.

| Complete source or recorded review | SHA256 | Exact operative boundary |
| --- | --- | --- |
| ADJACENT_HUB_PORTS_TIP_OWNED_POSITIVE_DOT_ALL_MASK_NEAR_ORIGIN.md | 9da02095677cdbf4b85f48a10c42282b874914332d99860c78e14a60da8df904 | Earlier full strict-side local theorem; original actual U3 support argument and detailed all-mask proof-section exports |
| REVIEW_ADJACENT_TIP_OWNED_POSITIVE_DOT_ALL_MASK_NEAR_ORIGIN_HOUSE_2026_10_28.md | 3c28d6a43cd0d5751c9ef19b36529955d93db54ce46a9c91b5180fcbffb8aa33 | Existing complete independent strict-side review, not a review of the new closed endpoint |
| TERMINAL_HUB_AXIS_TIP_OWNED_POSITIVE_DOT_FULL_MASK_ENTRY.md | 1e9e597ad4b13995909cdac5d204b111d20ef305768fe6d44def11264e4a4c49 | Only Sections4--6 pure W-face, X>Y and plus Y<1 proofs at the actual reestablished algebraic scope |
| REVIEW_TERMINAL_HUB_AXIS_TIP_OWNED_POSITIVE_DOT_ENTRY_CYCLES_2026_10_28.md | 77623fdce8cb6d780ce745a788d52d21719bf796d4ba717954784a4ae14252c8 | Existing complete independent physical entry audit |
| TERMINAL_HUB_AXIS_UNIQUE_PLUS_UNIFORM_PORT_BOX.md | 88f89381e0a978c301880dcf49f7cbf735fa7c04b16927d391e23c85db2e3c1a | Only complete Sections2--3 pure kappa>2/3 proof; no terminal-port hypothesis |
| REVIEW_TERMINAL_HUB_AXIS_UNIQUE_PLUS_PORT_BOX_ROOT_2026_10_28.md | aec59e0d84f5328a8224f8c10ddd6be217dbcbb3b278df51ccdbf47bb4820757 | Existing complete independent plus scalar review |
| TERMINAL_HUB_AXIS_UNIQUE_PLUS_NEAR_ORIGIN_INJECTION.md | 0a7d1e09191af313b91c9e6b08e2835e163e874624574f869ae81acf0e9fba90 | Complete broad strict-side plus scalar Sections3--7, reproved at the closed side bound in AppendixA |
| REVIEW_TERMINAL_HUB_UNIQUE_PLUS_NEAR_ORIGIN_INJECTION_HOUSE_2026_10_28.md | 2e2cd3157fef32d0b60ff386b508bcd71d9ecd106b75adbfb4615eebceb7ca7d | Existing complete independent plus scalar and injection review |
| TERMINAL_HUB_AXIS_UNIQUE_MINUS_UNIFORM_PORT_ENTRY.md | c0b1494d821eaa604d2313ae4675f8bc69149d4a73fdb75ecc545d0c21c77e63 | Only complete pure Sections2--3 minus z bound and exact ratio entry; no terminal equations |
| REVIEW_TERMINAL_HUB_AXIS_UNIQUE_MINUS_PORT_ENTRY_PENTAGON_2026_10_28.md | 1c5939231854aec15b81a03acc1bc234cde50d787e311f0001e2104872a79795 | Existing separate complete minus-entry review |
| THREE_FIFTHS_RATIO_BOUND_FOR_POSITIVE_DOT_MINUS_BOUNDARY_CORNER.md | 692044ebc896f0464fb2b9bf5d6ae07db38f8cfd7ab29054dd47bbcd5b554fdc | Whole terminal-free scalar ratio theorem at L>1/2 and s>L/(L+Kr) |
| REVIEW_THREE_FIFTHS_MINUS_RATIO_SCALAR_HOUSE_2026_10_28.md | 4c5f4772fce8ee0d243f82c603358b33b853d42285f49fb320d33c7e4b993cb5 | Existing independent whole ratio-scalar review |
| TERMINAL_HUB_AXIS_UNIQUE_MINUS_NEAR_ORIGIN_INJECTION.md | c597a6c741d686777d99ce09adef682cf64eb156f6eb746f5d2eaad6f09e73dc | Only complete pure p<26/25 proof after s-b>1/6, preserved at the closed endpoint |
| REVIEW_TERMINAL_HUB_UNIQUE_MINUS_NEAR_ORIGIN_INJECTION_PENTAGON_2026_10_28.md | 191bb1b8b82374fa1d5d3d49509ae120bb3a54a059c9d1752c62018a877b72b4 | Existing complete independent minus scalar and injection review |
| TERMINAL_HUB_AXIS_RADIAL_TIP_NEAR_ORIGIN_INJECTION.md | acd1a2b515779188a9e029d7e9b4a4c0182cde9c43b58fb52cd2a4237094761a | Only complete W-mask and scalar Sections4--7 at rho identity and tau<K; no strict sigma condition or terminal equation |
| REVIEW_TERMINAL_HUB_RADIAL_NEAR_ORIGIN_INJECTION_CYCLES_2026_10_28.md | a68f86733559921f19f8344a926944a5f252b88cf26c4be23233c448ef39816c | Existing full independent radial local review |
| UNEQUAL_NEAR_ORIGIN_UNIT_ANGULAR_BUDGET.md | 741ff2415b91fa8d490c601185994b7d947e000003c1ca702e423677eea3684e | Complete near-three angular contradiction for all origin positions |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Unchanged full physical equations, original support conventions, means and physical zero coefficients |

Appendix A contains the complete new closed plus scalar, preserving the full analytic proof and all fixed rational reserves. Main-text equation labels retain their predecessors for literal comparison; Appendix A labels carry an A prefix. Every original unit, full force, true degree, corner, zero coefficient, normal, application and mean remains. No pose sampling, angle mesh, physical limiting construction, numerical exclusion packet, Lean/Lake, build, CI/workflow, merge, remote write or original flag change is used.

## Appendix A. The complete plus-mask scalar with the closed side inequality



Let X,Y,a,b,tau be real numbers with

    X>0, 1/2<Y<=1,
    4<=X^2+Y^2<=Q_*,
    a,b>0, a^2+b^2=1, a>=2/3,
    0<tau<1.

Define

    R=sqrt(X^2+Y^2), r=Y/X, s=1-tau,
    rho=1-r*s,
    p=b*(X-1)+a*Y-a*r*s.

Suppose the full closed side inequality is retained:

    (a-rho)^2+(b+tau)^2<=1.                           (A13)

Then

    p<26/25.                                        (A14)

The scalar theorem does not need a>rho, the sign of L, a W circle equation, or any terminal premise. Those additional actual restrictions may be present but are not used to shrink this continuous comparison domain.

Put

    R_*=sqrt(Q_*), J=sqrt(Q_*-1)=sqrt(849)/16,
    r_0=1/J.

Throughout the whole domain,

    X>=sqrt(3),
    6/25<r<3/5.                                    (A15)

For the lower bound, r^2>64/1041>36/625, with final reserve 2524/650625. For the upper, r^2<=1/3<9/25, with final reserve 2/75.

Since b+tau>0, (A13) gives b+tau<=1. Therefore

    delta=s-b>=0.

Write

    h_0=a-1+r*b, h_+=max(h_0,0).

Then

    a-rho=h_0+r*delta,
    b+tau=1-delta.

Inequality (A13) is exactly

    2delta-delta^2>=(h_0+r*delta)^2.

If h_0>=0 this implies delta>=h_0^2/2. If h_0<0 the already proved delta>=0 is enough. Consequently, in every case,

    delta>=h_+^2/2,

and the displayed definition of p has the weak upper bound

    p<=R*(b+a*r)/sqrt(1+r^2)
           -b-a*r*b-(a*r/2)*h_+^2.                 (A16)

This bound is valid on both sides of h_0=0 and at h_0=0. The function h_+^2 is continuously differentiable there. The following two branches cover all b without omitting their common endpoint.

## Appendix A.1. Complete branch b>=3/5

Because a>=2/3,

    9/25<=b^2<=5/9.

The concavity of t*(1-t) on this interval implies

    a*b>=12/25.

At its two endpoints the squares of the candidate products are 144/625 and 20/81; their difference is 836/50625>0.

Dropping the last nonpositive term in (A16), applying Cauchy's inequality, and then increasing R to R_* gives

    p<=a*Y+b*(X-1)-(12/25)*r
       <=sqrt(Y^2+(X-1)^2)-(12/25)*r
       <=sqrt(Q_*-2R_*/sqrt(1+r^2)+1)-(12/25)*r.    (A17)

The last radicand is increasing with R for R>=2, since its derivative before the square root is 2R-2/sqrt(1+r^2)>0.

It suffices to prove the following exact squared excess is positive:

    S(r)=51/625-Q_*+(624/625)*r+(144/625)*r^2
                           +2R_*/sqrt(1+r^2)>0.   (A18)

Indeed S(r) equals

    (26/25+(12/25)*r)^2
        -[Q_*-2R_*/sqrt(1+r^2)+1],

and the quantities being compared are nonnegative.

For 6/25<=r<=3/5,

    S''(r)=288/625
            -2R_*(1-2r^2)/(1+r^2)^(5/2).

The positive function (1-2r^2)/(1+r^2)^(5/2) decreases throughout this interval: its derivative has numerator r*(6r^2-9)<0. At r=3/5 use

    (1+r^2)^(5/2)<(34/25)^2*(6/5)=6936/3125,
    1-2r^2=7/25,
    2R_*>=4.

It follows that S''<0, because

    3500/6936-288/625=47483/1083750>0.

Thus S is strictly concave; its minimum on the complete closed interval is at an endpoint.

We have R_*>83/40, with squared reserve 69/6400. At r=6/25,

    sqrt(1+r^2)<103/100,
    (103/100)^2-(1+(6/25)^2)=33/10000.

Substitution into (A18) gives the explicit endpoint lower bound

    S(6/25)>
      51/625-Q_*+(624/625)*(6/25)
         +(144/625)*(6/25)^2+415/103
      =486232137/10300000000>0.                    (A19)

At r=3/5,

    sqrt(1+r^2)<7/6,
    (7/6)^2-(1+(3/5)^2)=1/900.

Therefore

    S(3/5)>
      51/625-Q_*+(624/625)*(3/5)
         +(144/625)*(3/5)^2+249/70
      =120977/28000000>0.                          (A20)

Concavity and (A19)--(A20) prove (A18) throughout the full branch. Equation (A17) then gives p<26/25.

## Appendix A.2. Complete branch b<=3/5: reduction to one continuous function

Here a>=4/5. At each fixed r,b, the right side of (A16) increases with R. The condition Y<=1 gives the simultaneous bound

    R<=min(R_*,sqrt(1+r^2)/r).

The two radius bounds meet exactly at r=r_0=1/J. They give

    1/2<r_0<11/20,                                 (A21)

because J^2=849/256<4, with reserve 175/256, and J^2>400/121, with reserve 329/30976.

For r<=r_0 consider the upper function

    F_-(r,b)=R_*(b+a*r)/sqrt(1+r^2)
                    -b-a*r*b-(a*r/2)*h_+^2.

Its derivative is

    partial_r F_-=
       R_*(a-b*r)/(1+r^2)^(3/2)
            -a*b-(a/2)*(h_+^2+2r*b*h_+).           (A22)

On the enlarged interval 0<=r<=r_0, a>=4/5,b<=3/5 and (A21) give

    a-b*r>47/100,
    a*b<=1/2.

Also

    (1+r^2)^(3/2)<3/2,

since (521/400)^3<9/4, with reserve 2579239/64000000. By Cauchy's inequality,

    h_0<=sqrt(1+r^2)-1<1/7,

because (8/7)^2-521/400=71/19600. Finally r*b<=33/100. With R_*>=2 these bounds imply

    partial_r F_->
      47/75-1/2-(1/2)*(1/49+33/350)
      =1019/14700>0.                               (A23)

This also covers the differentiable joining point h_0=0.

For r>=r_0 the Y bound gives the upper function

    F_+(r,b)=a+b*(1/r-1)
                    -a*r*b-(a*r/2)*h_+^2.

Its derivative is

    partial_r F_+=
      -b/r^2-a*b-(a/2)*(h_+^2+2r*b*h_+)<0.          (A24)

Thus the complete radius/r comparison has its maximum at r=r_0, R=R_*, Y=1. No actual pose with these comparison values is asserted or needed.

Put r=1/J for the remainder of this section and define

    G(b)=a+b*(J-1)-a*b/J
                   -a*(a-1+b/J)^2/(2J),
    a=sqrt(1-b^2), 0<=b<=3/5.                       (A25)

The b=0 endpoint is a harmless closed scalar enlargement. At this fixed r,

    h_0=a-1+r*b
        =b*(r-b/(1+a))>=0,

because r>1/2 and b/(1+a)<=1/3. Equations (A16), (A23)--(A24) show

    p<=G(b).                                         (A26)

We next prove G(b)<26/25 on this entire closed interval.

## Appendix A.3. Uniform curvature: G''<-1/5

Write r=1/J and h=a-1+r*b. Separate (A25) into

    G=B-C,
    B=a*(1-r*b)+b*(J-1),
    C=(r/2)*a*h^2.

Using a'=-b/a and a''=-1/a^3 gives

    B''=[-1+r*b*(3-2b^2)]/a^3.                      (A27)

Since r<11/20 and

    a^3=(1-b^2)^(3/2)
       <=1-(3/2)*b^2+(1/2)*b^4,

the strict inequality B''<-9/20 follows if

    P(b)=11-33b+(27/2)*b^2+22b^3-(9/2)*b^4>0.       (A28)

This polynomial is positive on the whole interval. Indeed

    P''(b)=27+132b-54b^2>=27.

At b_0=9/16 exact arithmetic gives

    P(b_0)=22807/131072,
    P'(b_0)=-273/2048.

The global quadratic lower bound from P''>=27, followed by completing the square, gives

    P(b)>=P(b_0)-P'(b_0)^2/54
          =4370663/25165824>0.                      (A29)

This proves B''<-9/20 without splitting or sampling any orientations.

Direct differentiation of C gives the exact identity

    -C''=(r/2)*[
       (h^2+2a*h)/a^3
          +4*(b/a)*h*h'-2a*(h')^2].                (A30)

Throughout the interval,

    0<=h<1/7,
    4/5<=a<=1,
    b/a<=3/4,
    max(h',0)<=r<11/20.

Dropping the last nonpositive term in (A30) therefore gives

    -C''<=(11/40)*(1875/3136+33/140).

Consequently

    G''<-9/20+(11/40)*(1875/3136+33/140)
        =-1/5-13019/627200<-1/5.                    (A31)

All endpoint derivative statements are understood as the ordinary one-sided restrictions of the same smooth formula, which is smooth on a neighborhood of [0,3/5].

## Appendix A.4. One exact scalar value and slope finish the entire b interval

At b_*=1/3,

    a_*=2sqrt(2)/3.

The following rational brackets are strict:

    a_-=942809/1000000 < a_* < a_+=942810/1000000,
    J_-=1821100/1000000 < J < J_+=1821101/1000000.

The four positive squared reserves, in the same order, are

    8/9-a_-^2=705671/9000000000000,
    a_+^2-8/9=162649/90000000000,

    849/256-J_-^2=13/12500000,
    J_+^2-849/256=2602201/1000000000000.              (A32)

Define entirely rational constants

    r_-=1/J_+, r_+=1/J_-,
    t_-=1/(3a_+), t_+=1/(3a_-),

    h_-=a_--1+r_-/3,
    h_+=a_+-1+r_+/3.

Here the last two symbols are rational endpoint names, not the positive-part operation at the start of Appendix A. Both are positive, and r_--t_+>0. For example,

    h_-=687548238127/5463303000000>0,
    r_--t_+=1007326000000/5150851238127>0.

All factors below therefore have the displayed signs. Formula (A25) gives

    G(1/3)<=G_up,

    G_up=a_+ +(J_+-1)/3
               -a_-*r_-/3-(a_-*r_-/2)*h_-^2
          <10399/10000.                            (A33)

For full exactness, the last strict reserve is

    10399/10000-G_up
      =6592635251782643294434234361
        /108711278588737679418000000000000>0.

At b=1/3 put t=1/(3a). The exact derivative of (A25) is

    G'=(J-1)-t*(1-r/3)-r*a
                      +(r*t*h^2)/2-r*a*h*(r-t).

Its complete rational interval is obtained using

    D_lo=J_--1-t_+*(1-r_-/3)-r_+*a_+
             +(r_-*t_-*h_-^2)/2
             -r_+*a_+*h_+*(r_+-t_-),

    D_hi=J_+-1-t_-*(1-r_+/3)-r_-*a_-
             +(r_+*t_+*h_+^2)/2
             -r_-*a_-*h_-*(r_--t_+).

The signs above and (A32) give

    167/50000<D_lo<=G'(1/3)<=D_hi<67/20000<1/250.    (A34)

The two nontrivial endpoint reserves in (A34) are exactly

    D_lo-167/50000
      =474373331584114657775431201774728093650189
        /273567919358343177192564696477968458439990540625>0,

    67/20000-D_hi
      =57245473563770999727639763843467659405670253
        /9726859354963312966846744763661100744532997000000>0.

Thus (A34) bounds the absolute value of the derivative as well. Integrating the whole-interval curvature bound (A31) from b=1/3 in either direction and completing the square yields, for every 0<=b<=3/5,

    G(b)<=G(1/3)+G'(1/3)*(b-1/3)-(b-1/3)^2/10
         <=G(1/3)+(5/2)*G'(1/3)^2

         <10399/10000+(5/2)*(1/250)^2
          =26/25-3/50000<26/25.                    (A35)

This is a single continuous curvature argument. The rational brackets in (A32) evaluate one fixed analytic value and derivative; they are not numerical poses, a finite geometric subdivision, or a substitute for the whole-domain derivative proof.

Together with (A26), (A35) proves the small-b branch. Appendix A.1 proves the other branch, so the complete closed-domain abstract scalar theorem (A14) is established. In the small-b branch the final reserve is 3/50000 even if the first bound for p is an equality. In the large-b branch the two strictly positive endpoint reserves for S give the strict final bound independently of that equality.
