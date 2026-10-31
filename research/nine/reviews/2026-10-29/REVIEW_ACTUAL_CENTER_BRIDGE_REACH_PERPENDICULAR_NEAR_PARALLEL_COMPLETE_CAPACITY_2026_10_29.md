# Complete independent review of actual-center bridge reach and the near-parallel singleton roof

Date: October 29, 2026 UTC. Reviewer: capacity continuation.

**Verdict: ACCEPT at the exact frozen source below.** I read the complete
new manuscript and reconstructed its force-free center-offset lemma, full
D3 and V2 equations, continuous tilt bounds, actual bridge contradiction,
all endpoints, and both literal original D02 transfers. No defect was
found. The proof does not use an unloaded equation at the loaded N.

This is a full noncontributor review. I previously completed the separate
independent review of the manuscript supplying the complete physical-two
perpendicular-singleton chart. That chart and its exact force, support and
mean conventions were retained in the present review.

## 1. Frozen source and original inputs

Reviewed source:

    ACTUAL_CENTER_BRIDGE_REACH_AND_PERPENDICULAR_SINGLETON_ROOF_NEAR_PARALLEL_EXCLUSION_2026_10_29.md

Frozen SHA256:

    8b73232e774201fedb5eec884672bdb431de09b7452c4636f19d7e232c06faf9

Its complete original chart source is

    PHYSICAL_TWO_WEST_STRICT_PERPENDICULAR_SINGLETON_ADJACENT_RETURN_EXCLUSION_AND_COMPLETE_RESIDUAL_2026_10_29.md

at SHA256

    f3718c86a99ef196eba1ee875b66375582a0fc588f10275ec171c442e46780dd.

The complete physical force and mean input is

    PHYSICAL_CONTACT_STRESS.md

at SHA256

    d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5.

The complete original graph and load input is

    SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md

at SHA256

    cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1.

The previously completed complete chart review is

    REVIEW_PHYSICAL_TWO_PERPENDICULAR_SINGLETON_RETURNS_COMPLETE_CAPACITY_2026_10_29.md

at SHA256

    a9e123dde7bc3919c801d7c6baebf60ef01290c83534af70e492262b691e0663.

All four mathematical source hashes were independently recomputed before
writing this review. The new source was not edited.

## 2. The actual support-center lemma

Let X be an actual minimum-f support point or support-side mean of a
unit square E, with f a unit direction and c_E its actual center. An
aggregate side mean is still a point of the same closed physical
minimum-support face; it does not change the support level.

In E's own orthonormal frame u,v, its actual halfwidth gives exactly

    f.(c_E-X)=(|f.u|+|f.v|)/2>=1/2.

Every point of E lies within 1/sqrt(2) of its center, including both
endpoints of a side and every mean between them. Thus, writing

    delta=c_E-X=A f+B Jf,

one has

    A>=1/2, A^2+B^2<=1/2,
    |B|<=sqrt(1/2-A^2)<=1/2.

For any positively oriented orthonormal proof frame h,e, if f.e>=0,

    delta.e
      =A*(f.e)+B*(Jf.e)
      >=(1/2)*(f.e)-(1/2)*|f.h|.

The identity |Jf.e|=|f.h| is exact in this frame. The multiplication
of A>=1/2 uses the stated nonnegative sign of f.e; it would not be
valid without that sign.

For the other support direction g with g.e<=0, applying the same
argument in direction -e gives

    (c_C-L).e<=(1/2)*(g.e)+(1/2)*|g.h|.

Consequently the two actual centers obey

    (c_B-c_C).e
      >=(K-L).e
        +(1/2)*(f.e-|f.h|-g.e-|g.h|).

This includes a strict vertex normal, an owned side normal, any genuine
shared side, every closed overlap endpoint and any original side mean.
It makes no claim about changing an owner, moving the support point or
choosing a new physical square.

If the actual N physically touches both B and C, a B--N intersection
point is within 1/sqrt(2) of each of their centers. Hence

    |c_B-c_N|<=sqrt(2), |c_C-c_N|<=sqrt(2),

and the ordinary triangle inequality gives

    |c_B-c_C|<=2sqrt(2).

The final projection of this center distance proves the manuscript's
necessary bridge inequality. All these statements are force-free and
radius-free. No force equation at B,C,N is used, and their true degrees
and physical circle masks are arbitrary.

## 3. Exact physical roof domain

The inherited full physical-two chart keeps all original squares and
the stars

    A:{V,D,B}, D:{V,A,C}, V:{A,D}.

Only A,D are unloaded true3; V is loaded true2. The two PHYSICAL circle
corners of V remain two physical corners even when an individual circle
coefficient vanishes. The radial and coordinate domains are

    79/40<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1, 9/10<d<61/60,
    V=[d,d+1] x [-1/2,1/2],
    P=(d,1/2), Q=(d,-t), 0<t<=1/2,
    H=t+1/2, 1/2<H<=1.

The lower bound on d is strict even at the radius lower endpoint; its
squared reserve is 13/320. The upper bound has squared reserve
31/57600. These are checked explicitly in Section 8.

In the actual A frame h=(c,-s), e=(s,c), both components c,s are
strictly positive. The original roof normal toward V is h, the original
A-to-D normal is -e, and AD is a genuine A-only owned singleton.

The actual chart is

    A=P+[-1,0]h+[-l,1-l]e,
    W=P-xh-le, 0<l<1, 0<x<1.

The inherited physical geometry makes Q and W adjacent strict D
vertices. Its actual edge vectors are

    v=W-Q=-a h+b e=(-u,v_y),
    w=-b h-a e=(-v_y,-u),

where

    a=H s+x>0, b=H c-l>0,
    a^2+b^2=1,
    u=a c-b s>0, v_y=a s+b c>0.

The frame (v,w) is positively oriented; its determinant is
u^2+v_y^2=1. In particular the new argument's scalar v_y is the
actual world vertical component of the edge v. No independently
chosen D frame or numerical orientation approximation is used.

The new theorem assumes only the additional actual physical bridge
B--N--C, with N distinct from B and C, and the whole tilt condition

    0<v_y<=1/8.

It needs no premise that N is unloaded or that any of B,C,N has true
degree two.

## 4. Full exterior applications and the unified D3 identity

A's full unloaded force equation gives

    F_B=-mu h+gamma e, mu,gamma>0.

Both components are strict, so its actual A support application is
the upper-left vertex

    K=P-h+(1-l)e.

K belongs to the actual B and is its minimum-support point in the
unchanged direction

    f=(-h+r e)/sqrt(1+r^2), r=gamma/mu>0.

This statement uses the whole A force equation. It does not need to
reassign a force or use any equation at B.

D's full unloaded force equation gives

    F_C=-nu East-gamma e.

In its actual frame the components are

    F_C.v=nu u-gamma b,
    F_C.w=nu v_y+gamma a>0.

Thus its actual exterior application is necessarily on the far-w face,
and may be written

    L=Q+w+zv, 0<=z<=1.

The actual selected value is z=0 for a negative v component, z=1 for
a positive v component, and the full original side mean for a zero
v component. This is a single support-face description of all three
features; it makes no change to their original applications.

I expanded the complete torque about Q in the positively oriented
(v,w) frame. The D-to-A force gamma e at W=Q+v contributes
-gamma a. The roof force at Q has zero moment. The exterior force
at w+zv contributes

    -(nu u-gamma b)+z*(nu v_y+gamma a).

The zero total moment is therefore exactly

    -gamma a-(nu u-gamma b)+z*(nu v_y+gamma a)=0.

With q=gamma/nu it becomes

    q*[b-(1-z)a]=u-z v_y.

The signs of both original moments are correct. This equation retains
every positive term of D's true3 star. It covers adjacent, opposite and
the whole side mean together, without using any previous exclusion
to restrict z before the calculation.

The complete V2 force and moment equations are also correct:

    mu c+nu=k(d+1),
    mu s=-k eta,
    nu t=mu*(d s+c/2),
    k>0, -1/2<=eta<=1/2.

The origin moment comes from
det(P,mu h)=-mu*(d s+c/2) and
det(Q,nu East)=nu t. Hence

    nu/mu=(d s+c/2)/t>c,

because d,s>0 and 0<t<=1/2. The closed eta interval was retained,
including both individual-zero corner coefficients. Neither endpoint
was reclassified as a physically unique-corner V.

## 5. Uniform direction bounds for the complete closed tilt interval

The exact inverse change of frame gives

    b=c v_y-s u>0.

Since all quantities in s u<c v_y are positive, squaring and using
the two unit identities gives

    s^2<v_y^2, hence s<v_y and c>u.

Also b<v_y, so a>u. Throughout 0<v_y<=1/8,

    a>u>=sqrt(63)/8>99/100,
    c>u>99/100,
    0<b<v_y<=1/8.

The strict rational reserve is 171/40000. This proves the displayed
bounds at the upper tilt endpoint as well as in its interior.

In particular u>v_y. The right side of the unified D3 identity is
positive for the entire closed interval z in [0,1]:

    u-z v_y>=u-v_y>0.

Since q>0, the factor b-(1-z)a must be positive, and it is at most b.
Thus

    q>=(u-v_y)/b
      >(u-v_y)/v_y
      =u/v_y-1
      >=sqrt(63)-1
      >27/4.

The last radical comparison has positive square reserve 47/16.
The first weak inequalities deliberately retain their possible
endpoints; strictness comes from b<v_y and the final radical margin.

Combining the original V2 ratio with c>99/100 gives

    r=q*(nu/mu)>(27/4)*(99/100)
                 =2673/400>20/3.

In the actual (h,e) frame, the unchanged direction into C is

    g=[-c h-(s+q)e]/sqrt(c^2+(s+q)^2),

so g.e<0 and

    (s+q)/c>q>27/4>20/3.

The lower bound r>20/3 uses the exact true V2 force and moment,
not a guessed effective force. The argument has imposed no force
equation on B,C,N.

## 6. Exact separation and actual bridge contradiction

The original applications give

    (K-L).e
      =1-l+H c+a-zb
      =1+a+(1-z)b
      >=1+a>199/100.

The middle equality uses the original b=H c-l. The same actual z
appears throughout; no endpoint or shared mean is changed.

For

    F(x)=(x-1)/sqrt(1+x^2),

the derivative is exactly

    F'(x)=(1+x)/(1+x^2)^(3/2)>0.

Consequently

    f.e-|f.h|=F(r)>F(20/3),
    -g.e-|g.h|=F((s+q)/c)>F(20/3).

The comparison

    F(20/3)=17/sqrt(409)>21/25

is justified by a positive square reserve 256/255625. All compared
quantities are positive, so squaring is legitimate.

The support-center lemma therefore forces the actual center projection

    (c_B-c_C).e
      >199/100+(1/2)*(21/25+21/25)
      =283/100>2sqrt(2).

The final positive square reserve is 89/10000. This contradicts
the actual bridge bound |c_B-c_C|<=2sqrt(2).

The quantitative margin is strict even at v_y=1/8 and for z=1.
For any endpoint z=0 incompatible with the unified moment, that
incompatibility is itself derived from the full original equation.
There is no deleted endpoint in the proof.

The contradiction concerns the actual centers of the given squares.
It does not posit a center packing, reconstruct new squares from
centers, or assume that incircle information alone determines a unit.

## 7. Exact original-family transfers and surviving domain

The literal original labels are

    A=0, V=1, D=2, C=3, N=4, B=5,

with rim A--V--D--C--N--B--A and chord AD. The true stars A3,
D3,V2 are exactly those used above.

In D02.L135, N is unloaded true2. In D02.L1345, N is loaded true2.
The original positive BN and CN edges imply the physical bridge
in BOTH rows. That is the entire use of N in the theorem.

B and C retain their original loaded true2 stars, and their equations
are not shortened. The proof would also work at arbitrary degrees
and physical masks of B,C,N. In particular the loaded N is never
treated as a two-force transmitter.

All three additional physical units remain in the same packing.
They are unnecessary for this local contradiction, but are not
discarded from the original configuration or any global argument.

The earlier complete source already excluded every adjacent return
and every return with c<=3/4. Combining it with the new theorem
leaves precisely the stated necessary conditions

    c>3/4, v_y>1/8,

in the unchanged two support rows:

1. Opposite D vertex with original application Q+v+w and
   nu*(u-v_y)=gamma b>0.
2. D-owned exterior side with original application Q+w+zv and
   nu u=gamma b,
   z*(nu v_y+gamma a)=gamma a.

The second equality forces 0<z<1 without any prior deletion of a
mean endpoint. This review does not assert that the remaining domains
are realizable.

Whole-data reflection transports the complete original chart, forces,
means and physical masks. It does not independently exchange a
unique-circle-adjacent port with an opposite port.

The new theorem applies only to the stated physical-two perpendicular
singleton feature and its reflected chart. It does not close either
whole D02 row or any unique-physical-circle Type III feature.

## 8. Exact rational checks and final verdict

I recomputed the following values with exact integer fractions.

| Check | Exact positive reserve |
| --- | --- |
| 63/64-(99/100)^2 | 171/40000 |
| 63-(31/4)^2 | 47/16 |
| 2673/400-20/3 | 19/1200 |
| (17/sqrt(409))^2-(21/25)^2 | 256/255625 |
| (283/100)^2-8 | 89/10000 |
| (79/40)^2-1/4-(19/10)^2 | 13/320 |
| (121/60)^2+1/4-1105/256 | 31/57600 |

These finite arithmetic checks corroborate the complete continuous
proof above. No numerical orientation search or pose enumeration was
used.

I accept the full frozen manuscript at
8b73232e774201fedb5eec884672bdb431de09b7452c4636f19d7e232c06faf9:
the generic actual-center bridge inequality, its complete roof
application on 0<v_y<=1/8, all original exterior support features
and mean endpoints, and both literal D02 joins are sound.

The new application retains the existing conditional common-selection
scope of its inherited physical chart. It introduces no selector and
does not repair the prior global extraction compatibility issue.

No input manuscript or original inventory flag was edited. No
physical unit, positive force, selected normal, true degree, original
mean, physical corner mask or individual coefficient was changed.
No pose search, angle mesh, packing certificate, Lean/Lake build,
CI, remote mutation or merge was performed.
