# An intact petal leaves room for at most one other unit near the origin

Date: October 27, 2026.

**Status: accepted complete uniform hand geometric theorem and complete
stated original-layout corollaries after full-source root and separate
independent reviews in
REVIEW_INTACT_PETAL_TWO_NEAR_ORIGIN_UNITS_ROOT_2026_10_27.md and
REVIEW_INTACT_PETAL_TWO_NEAR_ORIGIN_UNITS_HEXAGON_2026_10_27.md.**
No shared ledger is changed by this source.

Keep all nine original physical squares in the same compatible
selected certificate and radius window

    79/40<=R<=sqrt(1105)/16.

An actual intact petal H,U,V has both tips of their true positive
degree two and loaded. H keeps arbitrary degree and every original
force. The accepted origin theorem puts O in int H. Suppose

    d=sqrt(R^2-1/4)-1=1+epsilon,
    0<epsilon<1/60,

and two distinct actual units K_1,K_2, both different from H,
meet the closed disk D_epsilon.

**Theorem.** This physical configuration is impossible.

The two units need no force, load, leaf or graph-degree assumption.
Their actual points in D_epsilon and their complete physical unit
squares suffice. Every additional positive force at H remains.

## 1. The accepted intact-petal geometry gives a fixed interior test point

Choose actual x_i in K_i with |x_i|<=epsilon. Because O is in
int H and K_i is a distinct interior-disjoint unit, x_i cannot
belong to int H. Therefore an actual side of H has positive
height sigma<=epsilon.

The full theorem in
INTACT_PETAL_SHALLOW_SIDE_BOUNDARY_EXCLUSION.md supplies H's own
axes and a reflection in which

    H=[-sigma,1-sigma] times [-P,1-P],
    0<sigma<=epsilon<1/60,       16/25<P<=11/15.        (1)

One actual intact tip, named U, has an unchanged application

    p=(-w,-P),       0<w<=sigma,

and its unique physical circle corner is

    Z=(-X,-Y),       0<=X<1/18,       Y>0.             (2)

The same accepted theorem proves that p and Z are opposite
vertices of this actual unit U. These statements retain every
circle mask and endpoint alternative until that complete physical
classification. In particular neither K_i can equal U, since a
physical boundary unit has no point of norm below r=R-sqrt(2),
where r>129/200>epsilon.

Define the following physical point in the same fixed coordinates:

    q=(-1/5,-P-1/5).                                  (3)

We first prove q lies strictly inside U. Write its actual diagonal

    Z-p=(s,-t),       s=w-X,       t=Y-P>0.

Its length is sqrt(2), so

    |s|<1/18,       t=sqrt(2-s^2)>7/5,
    s<=w.                                             (4)

The two unit side directions from p are

    u_U=((s+t)/2,(s-t)/2),
    v_U=((s-t)/2,(-t-s)/2).

These are orthonormal, their sum is Z-p, and the actual U is
p+[0,1]u_U+[0,1]v_U. The own coordinates of q-p are

    a_U=[w t+(w-2/5)s]/2,
    b_U=[(2/5-w)t+w s]/2.                             (5)

Both are strictly positive. For a_U, if s<=0 this follows from
w>0 and w<2/5. If s>0, use s<=w and the negative coefficient
w-2/5 to obtain

    2 a_U>=w(t+w-2/5)>0.

For b_U, the bounds w<1/60, |s|<1/18 and t>7/5 give

    2 b_U>(23/60)(7/5)-1/1080>0.

Also |q-p|^2=(1/5-w)^2+(1/5)^2<2/25<1. Since the two
coordinates in (5) are orthonormal projections, each is less
than one. Thus

    q belongs to int U.                               (6)

The rest of the proof shows that one of K_1,K_2 must contain
this same q in its open interior.

## 2. Two quarter-squares and their forced order on a small circle

Set

    rho=4/15,
    delta=arcsin(1/16),       0<delta<pi/6.             (7)

At each actual point x_i in the unit K_i, choose the sign of
each own side axis toward the center of K_i. There is at least
one half-unit of room from x_i in each chosen direction. Order
these two perpendicular directions as u_i,v_i with v_i=J u_i.
The actual square therefore contains

    x_i+[0,1/2]u_i+[0,1/2]v_i.                        (8)

Let phi_i be the angle of u_i. On the radius-rho circle consider
the closed angular arc

    I_i=[phi_i+delta, phi_i+pi/2-delta].               (9)

Every point y on this arc lies in int K_i. Indeed both own
projections of y are at least rho sin(delta)=1/60>epsilon,
so both projections of y-x_i are strictly positive. Each is
at most rho+epsilon<17/60<1/2. Thus y lies strictly inside
the quarter-square in (8), hence inside the original K_i.

H contains the entire closed eastern semicircle of this small
circle: in (1), 1-sigma>rho, P>rho and 1-P>=rho. No point
of either arc can belong to closed H, since it is interior to
the distinct K_i. Consequently both arcs lie in the open
western semicircle. They are disjoint because the original
K_1,K_2 have disjoint open interiors.

Order them from north to south in that semicircle, calling their
units K_+ and K_-. Choose the angles without wrapping so that
the arc of K_+ comes first. The inclusions and disjointness give

    phi_+ +delta>=pi/2,
    phi_- +pi/2-delta<=3pi/2,
    phi_+ +pi/2-delta<=phi_- +delta.                  (10)

It follows that

    pi/2-delta<=phi_+<=pi/2+3delta,
    pi-3delta<=phi_-<=pi+delta,                       (11)
    |phi_+ +pi/2-phi_-|<=2delta.                      (12)

Thus K_+'s selected directions are approximately north and
west; K_-'s are approximately west and south. Their selected
west directions differ by at most 2delta. These are conclusions
about their original physical axes, not newly chosen contact
normals.

The exact bounds needed below are

    cos(2delta)=127/128,
    sin(2delta)<1/8,
    sin(3delta)=191/1024<3/16,
    cos(3delta)>49/50.                                (13)

The last comparison follows by squaring, since
1-(3/16)^2=247/256>(49/50)^2 and 3delta<pi/2.

## 3. The actual separating axis makes the lower square's upper face shallow

Use the elementary separating-axis property of two squares:
if their open interiors are disjoint, their projection intervals
have disjoint interiors along an own side axis of at least one
square. One direct proof applies the supporting-edge inequalities
to their convex difference polygon. Its edges are parallel to
the original square edges; if O is not in its interior, one of
those edge inequalities gives the stated original axis.

Let the selected west directions be

    w_+=v_+,       w_-=u_-.

By (12), their angle difference is at most 2delta. Neither
original horizontal axis, meaning either -w_+ or -w_- and its
negative, can separate the squares. To check this with a fixed
rightward choice r_0 from those axes, each actual square contains
the two points x_i and x_i+(1/2)w_i, whose projections satisfy

    r_0.x_i>=-epsilon,
    r_0.(x_i+(1/2)w_i)<=epsilon-127/256.

Since epsilon<1/60, both projection intervals contain the whole
nondegenerate interval [-1/4,-1/8] in their interiors. They
therefore cannot be disjoint on either such axis.

The separating axis must be one of the two original upward axes

    n_+=u_+,       n_-=-v_-.

Their directions also differ by at most 2delta. Call the actual
choice n_0, directed upward. K_+ has a point of n_0 projection
at least -epsilon+127/256>0, while K_- has a point of projection
at most epsilon-127/256<0, by their selected north and south
half-unit segments in (8). Thus the separated order must be
K_- below K_+, rather than the reverse. In particular

    h_{K_-}(n_0)<=min_{K_+} n_0.x
                 <=n_0.x_+<=epsilon.                 (14)

Give K_- its actual right/up own axes

    r_-=-u_-,       n_-=-v_-.

Write its real upper supports as h_r,h_n, so its two own
coordinate intervals are [h_r-1,h_r] and [h_n-1,h_n]. Since
it contains x_-,

    h_r>=-epsilon,       h_n>=-epsilon.                (15)

Its selected half-unit west segment also gives

    h_r<=r_-.x_-+1/2<=epsilon+1/2.                    (16)

Write n_0=a n_-+b r_-. By (12)--(13),

    a>=127/128>0,       |b|<1/8.

The point on K_-'s upper own face with the same r_- coordinate
as x_- belongs to K_-. Applying (14) to that actual point gives

    a h_n+b(r_-.x_-)<=epsilon,
    h_n<=epsilon(1+1/8)/(127/128)
         =(144/127)epsilon<12/635<1/50.               (17)

This uses the actual separating axis even when it belongs to
K_+; no common orientation of the two squares is assumed.

## 4. The fixed tip point lies strictly inside the lower square as well

Put theta=phi_- -pi. By (11), -3delta<=theta<=delta, and

    r_-=(cos(theta),sin(theta)),
    n_-=(-sin(theta),cos(theta)).

For the point q in (3), put Q=P+1/5. From (1),

    21/25<Q<=14/15.

Its original two projections satisfy, by (13),

    q.r_-<=-(1/5)(49/50)+(14/15)(3/16)
            =-21/1000<-1/60,
    q.r_->=-1/5-(14/15)(3/16)=-3/8.                   (18)

Equations (15)--(16) imply h_r>=-epsilon>-1/60 and
h_r-1<=epsilon-1/2<-29/60<-3/8. Hence (18) puts q's
rightward coordinate strictly between the two actual side
supports of K_-.

Its upward coordinate has the bounds

    q.n_-<(1/5)(3/16)-(21/25)(49/50)
             =-7857/10000<-3/4,
    q.n_->-3/80-14/15=-233/240>-49/50.                (19)

By (15), h_n>=-epsilon>-1/60, so the first inequality is
strictly below h_n. By (17), h_n-1<-49/50, so the second
is strictly above h_n-1. Thus

    q belongs to int K_-.                             (20)

Equations (6) and (20) contradict interior disjointness of the
distinct actual U and K_-. This proves the uniform theorem.

## 5. Complete genuine-leaf-root consequence

Suppose an actual intact-petal root H has two distinct genuine
leaf roots K_1,K_2 elsewhere in the same original physical packing.
The roots need no specified positive degree or other attachment
restriction. Neither can have a D leaf, whose root would contain
O openly and overlap H. Nor can d<=1 occur for an S leaf,
whose root would then contain O closed.

Thus both genuine leaves are S and d>1. Each root contains its
unchanged inward radial-segment point epsilon e_i. The two real
roots therefore meet D_epsilon and contradict the theorem.

**Whole-family consequence.** An intact petal cannot coexist
with two distinct other genuine leaf roots, at arbitrary true
degrees and with all other original forces retained.

This conclusion requires neither a reduced equation at H nor a
minimum-support branch deletion. The only stress geometry used
is the accepted intact-petal and shallow-side theorem, each at
its stated arbitrary-root-degree scope. The later small-circle,
separating-axis and interior-point argument is purely physical.

## 6. The two final explicit C3.333.b2 attachments are excluded

The first original layout has triangles

    H,U,V;       H,A,B;       H,C,D,

and genuine leaves at A and C. H has its actual degree six,
A,C degree three, U,V,B,D true degree two and the two leaves
degree one. The first triangle is intact at H, and A,C are two
distinct other genuine leaf roots. Section 5 excludes the whole
layout with H's three actual triangle pair systems unchanged.
This is B7, or residual R1, of
THREE_TRIANGLES_TWO_BRIDGES_ATTACHMENT_COVER.md.

The second original layout has triangles

    H,U,V;       H,A,B;       A,C,D,

and genuine leaves at H and U. The actual degrees are
H5,A4,U3,V2,B2,C2,D2, with two genuine degree-one leaves.
The intact root is A; H and U are the two distinct other
genuine leaf roots. Section 5 excludes this whole layout as
well. In particular H's own leaf force is kept in its real
degree-five equation and is never deleted to invoke an opposite-
pair ray corollary. This is C9, or residual R2, of that cover.

All original S/D types, circle masks, zero individual weights,
actual owners and means are covered by the whole geometric joins.
This source supplies these two entire attachment exits; the full
coarse-cell assembly must still verify the remaining original
34-layout cover and its other complete dependencies. No force,
mean, normal, unit square or selected pose moves. No numerical
pose search, Lean compilation, CI, remote action or shared-ledger
edit is used.
