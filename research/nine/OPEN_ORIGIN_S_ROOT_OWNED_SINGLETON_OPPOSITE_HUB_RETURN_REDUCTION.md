# The root-owned singleton roof interface reduces to opposite hub returns

Date: October 28, 2026 UTC. Author: root continuation.

**Status: complete proposed uniform geometric lemma, full hub-return
feature cover and necessary-domain reduction for both roof families.
Submitted for separate full review; no original whole-family gate closes.**

The actual near-hub strip and weak moment signs first leave only one
side and one strict vertex for its return to A. The side is already
excluded. A single corner bound then excludes the opposite return
at C, including the case in which the A application is an arbitrary
point of its XA support face. The original C2 and A3 equations remain.

## 1. Complete actual chart

Use the accepted root-owned open-origin S chart, with all nine actual
squares and all original forces, means, physical masks and zero weights:

    sqrt(17)/2<R<=sqrt(1105)/16,
    d=1+epsilon, 0<epsilon<1/60,
    X=[-a,1-a] x [-b,1-b],
    0<a<=epsilon, (1-a)^2+b^2=d^2,
    sqrt(2 epsilon)<b<=2 sqrt(epsilon)<31/120,
    P_XH=P=(-a,-t), 0<t<b.

The actual X3 has neighbors its genuine leaf L, H and physical boundary
A. HX is singleton owned by X; the actual H--A contact is present.
Write H's two actual inward axes at its rightmost vertex P as

    u=(-alpha,beta), v=(-beta,-alpha),
    alpha,beta>0, alpha^2+beta^2=1,
    H=P+[0,1]u+[0,1]v.                              (1)

The proper H frame is e=v, f=-u. Its actual one-missing-interval strip is

    H=[a_H,a_H+1]e+[c-1,c]f,
    a_H=a beta+t alpha in(0,epsilon],
    c=t beta-a alpha in[0,1].                       (2)

In fact c<=t beta<b<1. The original HX direction in this frame is
(-beta,alpha). Its moment is positive, while the actual HA and HC
moments are nonpositive, as supplied by the actual-hub theorem.

The remaining actual XA feature is North, with its unchanged support
mean

    Q=((t/b)(1-a),1-b),

or strict Northwest, with

    Q=(-a,1-b),
    m=(-z,1)/s, s=sqrt(1+z^2),
    z=[a+(1-a)t/b]/[1-b+t], 0<z<1.                 (3)

For the Northwest feature XA is genuinely A-owned by the existing
fixed-nonleaf selector at the actual X3: both nonleaf contacts are
singleton, H is the actual near unit, and A physically touches the
circle. No normal is subsequently reselected.

When H3 is invoked below, its entire original positive neighborhood
is X,A,C and it is unloaded. No such equation is assigned to a fan H4.

## 2. A complete HA feature cover from the actual weak moment

The following argument does not use H's degree or force equation.
All directions in this section are expressed in the proper H frame
(e,f) of (2).

The HA axes East and South have negative dot product with the actual
HX direction (-beta,alpha). Either contradicts the owned-axis triangle
inequality for the physical triangle H-X-A. The North axis has positive
origin moment at every actual support mean, since its application has
first coordinate at least a_H>0. A strict Northwest HA direction at
P has moment a_H N_f-c N_e>0. Thus both also contradict the given
nonpositive HA moment.

A strict Southeast HA normal has its original H application at
W=P+u+v. In world coordinates its x component is strictly negative:
it is a positive combination of u and v. The strict complete unit
support-span lemma consequently gives

    max_A x<W_x+1=P_x-alpha-beta+1<P_x.

Here alpha+beta>1. But the actual whole X lies in x>=P_x and A
physically touches X, a contradiction. This includes arbitrary A
orientation and ownership of the original HA normal.

It remains to exclude strict Northeast. Write its unit components
as N=s_0 e+t_0 f, s_0,t_0>0, and k=t_0/s_0. The actual application
is (a_H+1,c). Its weak origin moment gives

    k<=c/(a_H+1),
    h_H(N)=(a_H+1+c k)/sqrt(1+k^2)
              >=(a_H+1)sqrt(1+k^2)>1.             (4)

Its world y component -s_0 alpha-t_0 beta is negative. Its world
x component is negative too, because

    k alpha<=c alpha/(a_H+1)<t beta alpha<beta.

For a North XA mean, Q has both world coordinates positive, so
N.Q<0, contradicting Q in A and the actual support (4). For strict
Northwest XA, Q=(-a,1-b) and the same world components give

    N.Q=a(s_0 beta-t_0 alpha)
             -(1-b)(s_0 alpha+t_0 beta)<=a<1,

again contrary to (4). All actual XA features have been covered.

Therefore the original HA feature is exactly one of:

* the H-owned West side, normal -v, with its whole actual mean
  P+tau u, 0<=tau<=1;
* strict Southwest in the H frame, at the actual singleton R=P+u,
  with its original positive force vector q u-p v, p,q>0.

The complete West-side alternative is excluded at actual H3 by
`OPEN_ORIGIN_S_ROOT_OWNED_SINGLETON_HUB_SIDE_RETURN_INSIDE_RADIUS_TWO.md`.
No side endpoint or free HA vertex normal has been dropped in this cover.

## 3. A full-face geometric lemma when alpha>=beta

Suppose alpha>=beta, and suppose an original HA application has the
form R=P+tau u, 0<=tau<=1. In the Northwest XA feature, assume its
original inward-to-A normal N has N.m>0. N need not be A-owned, and
R need not initially be an A vertex. The exact conclusion is

    every actual point of A has norm<247/120<sqrt(17)/2.            (5)

In the North XA feature no extra normal condition is needed: alpha>=beta
already gives max_H y=beta-t<1/sqrt(2)<89/120<1-b<=min_A y, contradicting
HA. Thus only Northwest needs the following full-face calculation.

From (2) and alpha>=1/sqrt(2),

    t<sqrt(2)epsilon, |P|<1/30,
    t/b<sqrt(epsilon)<13/100,
    0<z<(1/60+13/100)/(89/120)=88/445<1/5.           (6)

These bounds retain the whole original strip and application, not just
their vertex values. The norm bound follows from
|P|^2=a^2+t^2<3 epsilon^2<1/1200<1/900.

Put w=(1,z)/s, so m,w are the actual A own axes. Because N.m>0,
minimizing N on A forces its m coordinate to the minimum. Thus R and
Q lie on A's same actual minimum-m side. Their world x difference is
tau alpha, so

    Q-R=tau alpha s w.                              (7)

This proves the identity from the actual points; it is not a reset
of the HA mean. Their separation must be at most one. The complete
minimum-m side of A, with its unknown real endpoints, is consequently
contained between Q-w and R+w. Its parallel maximum-m side is
contained between

    Q+m-w and R+m+w.                                (8)

Define

    U=u.m=(alpha z+beta)/s>0,
    V=u.w=(-alpha+beta z)/s<0.

Since beta<=1/sqrt(2) and alpha+beta<=sqrt(2),

    U<=(1+z)/(sqrt(2)s),
    u.(m+w)<sqrt(2)/5<2/7.                          (9)

The displacement of R+m+w from P is tau u+m+w. Its squared norm
is strictly below 3+4/7=25/7, including both signs of the mixed dot
product and every tau endpoint.

For the other endpoint in (8), the identity V+alpha s=zU and (7)
give its exact displacement coordinates in the (m,w) frame:

    Q+m-w-P=(1+tau U, tau zU-1).                    (10)

Its squared norm is

    2+2 tau U(1-z)+tau^2 U^2(1+z^2)
       <=2+2U(1-z)+U^2(1+z^2)
       <=2+sqrt(2)(1-z^2)/sqrt(1+z^2)+(1+z)^2/2
       <=5/2+sqrt(2)+z+(1/2-sqrt(2))z^2.            (11)

The first bound uses 0<=tau<=1, U>0 and z<1. For 0<=z<=1/5,
the last polynomial increases on the whole interval: its difference
between 1/5 and z factors as

    (1/5-z)[1-(sqrt(2)-1/2)(1/5+z)],

whose bracket is positive, even using sqrt(2)<10/7. Therefore (11)
is at most

    68/25+(24/25)sqrt(2)<716/175<(81/40)^2.           (12)

The last squared reserve is 103/11200. The other bound 25/7 is
smaller than (81/40)^2 as well.

For completeness this covers the whole unit, not just the two displayed
points. Relative to P, the minimum-m side has constant m coordinate
tau U>=0; the maximum-m side has coordinate tau U+1. Adding m to a
point of the first side increases its squared distance from P. On the
second side, the squared norm is convex in the single w coordinate,
so (8)--(12) bound every point of that side and then the whole square.

Thus all points of A have distance less than 81/40 from P. Equation
(6) gives the strict origin bound

    |Z|<81/40+1/30=247/120,
    17/4-(247/120)^2=191/14400>0.

This proves (5), contradicting the actual physical boundary A at R>
sqrt(17)/2. The argument includes a whole HA support side at A when
N is parallel to m, arbitrary original mean positions and every mask.

## 4. Full H3 leaves only the opposite return or its side

By Section 2 and the accepted West-side exclusion, HA is strict
Southwest in the H frame. Retain its actual force vector

    F_HA=q u-p v, p,q>0,

and write lambda>0 for the original HX magnitude. The complete H3
force equation makes

    F_HC=(lambda alpha-q)u+(lambda beta+p)v.         (13)

Its v component is positive. If its u component is also positive,
its original H support is W=P+u+v. Full H torque about P is then

    -p+[lambda(beta-alpha)+p+q]=0,
    q=lambda(alpha-beta)>0.                         (14)

In particular alpha>beta. In the Northwest XA feature its original
HA normal satisfies

    N.m proportional to qU-pV>0,

because U>0 and V<0 by (6),(9). Its actual application R=P+u is
of the form required by Section 3. Both that feature and the North
feature are therefore impossible. This excludes the entire HC
opposite-vertex alternative without any force equation at A or C.

Consequently q>=lambda alpha. There are precisely two survivors:

1. If q=lambda alpha, the original HC vector is
   (lambda beta+p)v. Its actual support mean lies on the complete
   side P+v+[0,1]u. Full torque gives the exact genuine mean

       R_HC=P+v+sigma u,
       sigma=p/(lambda beta+p) in(0,1).             (15)

   The mean endpoint exclusion is derived from positive magnitudes,
   not imposed before balancing the original H3.

2. If q>lambda alpha, the original HC support is the opposite
   vertex P+v. Its full torque about P gives

       q=p+lambda alpha,
       F_HA=(p+lambda alpha)u-p v,
       F_HC=-p u+(lambda beta+p)v.                 (16)

   Both unchanged return normals strictly expose their respective
   H vertices P+u and P+v. They may be externally owned or free.

Every conclusion is a statement about the actual original application
and force. The continuous parameters in (15)--(16) remain. This source
does not declare either surviving interface impossible.

## 5. Literal original-family joins and exact limits

In both M6.B5L.HOUSE.ROOF.LAC.S and
M6.B5L.HOUSE.ROOF.LABC.S, take X=T3, H=D3, A=A3, C=C2. The real
AD edge supplies the triangle. The accepted actual-hub theorem and
root-owned normal form apply on the original open-origin root domain.

For their entire X-owned singleton HX interface, Sections 2--4 leave
exactly (15) or (16), with every original A3/C2 force still present.
This is stronger than an owner-specific sampling or a chosen A-circle
corner calculation: the full original HA feature cover and all possible
HA support means at A were handled before making the reduction.

The physically shared HX domain, aligned-high roots and origin-free
roots are outside this interface. The earlier complete H-owned singleton
exclusion is separate. The endpoint-fan hub remains true degree four;
no H3 consequence in Section 4 is transferred to it. No original fine
or coarse gate is closed by this necessary-domain result.

## 6. Exact direct inputs

| Source | SHA256 | Exact use |
| --- | --- | --- |
| OPEN_ORIGIN_S_ROOT_OWNED_AXIS_POSITIVE_CONCURRENCE_FROM_ACTUAL_HUB_STRIP.md | 8fb2124065fbc37b4746e94bf45611f2dbd3bb29990391256ddd15d5c15bb917 | Complete actual chart, near strip, North/Northwest cover and conditional A-owned axis |
| ONE_UNLOADED_RETURN_HUB_ACTUAL_WEAK_MOMENT_STRIP.md | 382e06b874e41cf582b17374a122c7e4f289472f00cd6d02d926b680f15c1ed5 | Original weak HA/HC moments and the exact roof H3 joins |
| OPEN_ORIGIN_S_ROOT_OWNED_SINGLETON_HUB_SIDE_RETURN_INSIDE_RADIUS_TWO.md | 0cb653d75bd7c7bf6293f8920fc6ce7de7391a710405ab218d89a037f5e2b038 | Entire actual H-owned West HA side exclusion, with all means |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Actual owned-axis triangle restriction and complete strict unit support span |
| S_LEAF_ROOT_FIXED_NONLEAF_CONTACT_SELECTION.md | 499e6d42632a811bcb7bef6596b8585c11fbb5f59f36551d02fd05c080387a43 | Only the already accepted genuine-X3 singleton A-owner consequence |
| FIVE_BODY_BLOCK_LEAF_GRAPH_LOAD_COVER.md | e5c84071363e8dc43b09f9033c7cb3a7684f1de19bcd169d53c9eab55d51963b | Literal original labels, full degrees, masks and all-nine contract |

All nine actual squares, original normals, shared means, complete stars,
physical circle masks and zero individual weights remain. No new generic
condition, numerical pose certificate, mesh, Lean compilation, CI,
original checkbox edit or remote action is used.
