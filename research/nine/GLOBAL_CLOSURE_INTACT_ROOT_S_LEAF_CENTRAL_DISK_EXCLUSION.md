# An intact triangle root with an S leaf isolates the central disk

Date: October 26, 2026.

**Status: accepted complete hand argument after full-source root and
separate independent reviews in
REVIEW_INTACT_ROOT_S_LEAF_CENTRAL_DISK_ROOT_2026_10_26.md and
REVIEW_INTACT_ROOT_S_LEAF_CENTRAL_DISK_HEXAGON_2026_10_26.md.**
No original ledger or coarse-cell status is changed by this source.
Section 5 excludes the complete formerly
remaining intact-petal attachment of C2.33.b2; the no-intact attachment
remains a separate original obligation.

Keep all original nine physical unit squares, the common compatible
selected physical certificate and the same radius/Phi-minimizer pose.
Write

    79/40 <= R <= sqrt(1105)/16,
    d = sqrt(R^2-1/4)-1,
    epsilon = max(d-1,0) < 1/60.

An intact petal is an actual positive triangle H,C,D with both tips
of true positive degree two. Their touching neighbors make both tips
loaded. H retains its full original degree and every other force.

The accepted ROOTED_END_TRIANGLE_ORIGIN_INTERIOR.md gives O in int H.
It also gives an actual common side for the two original petal ports,
with height P and strict transverse straddling, where

    1/5 < P < 39/40.                                    (1)

Both actual outward normals have positive component along the common
side's outward axis. Their transverse components have the same weak
signs as their actual ports. At each true loaded tip, the full proper
concurrence theorem gives

    q_C = p_C + ell n_C = tau F_C,
    ell >= 0, tau > 0.                                 (2)

The other tip is a physical boundary neighbor, so the required true
tip force pair is nonparallel. These statements include every physical
circle mask, zero individual corner coefficient, normal owner and
actual shared-side mean. The proof below uses no reduced equation at H.

## 1. An intact petal cannot have a small transverse port on a middle-height side

Assume d>1 and choose the common-side frame so that its outward axis
points south. Suppose one actual port and its actual normal are

    p=(-w,-P),     n=(-s,-c),
    0<w<1/60,     11/15<P<39/40,
    s>=0, c>0,    s^2+c^2=1.                           (3)

The other port has strictly positive horizontal coordinate, and its
normal has nonnegative horizontal and strictly negative vertical
component.

**Small-port lemma.** The complete physical situation (3) is impossible.

### 1.1. The actual normal and radial concurrence stay in the same narrow cone

First,

    s/c < w/P.                                         (4)

If s=0 this is immediate. Otherwise the two root normals are
nonparallel: their horizontal components have opposite weak signs,
and only the first is strictly negative. Write the other normal
as (s',-c'), where s'>=0 and c'>0, and its positive magnitude as mu'.
The complete end-triangle theorem gives the actual root intersection
q_0=-t M, t>0, where M is the positive sum of the two root normals.
Put v=(-c,s), a unit perpendicular to n. Since p=q_0+a n,

    p.v = -t M.v
        = t mu' (c s' + s c') > 0.

But p.v=wc-Ps. This proves (4). No assumption is made about which
physical square owns either normal, or about a side mean being interior.

Apply the actual tip relation (2). Its two coordinates are negative:

    q_C=(-w-ell s,-P-ell c).

Its positive radial direction therefore has a horizontal-to-vertical
ratio bounded by

    (w+ell s)/(P+ell c) <= w/P < 1/44.                  (5)

The weak first inequality includes ell=0. The last bound uses (3).

### 1.2. The physical circle mask is necessarily unique

The actual port satisfies

    |p|^2=P^2+w^2
      <(39/40)^2+(1/60)^2<1.                           (6)

A unit square with two physical circle corners in this radius window
is radial S, and every one of its points has norm at least d. To see
the classification directly, write its center as (a,b) in its own
side frame. The maximum squared corner norm is
a^2+b^2+1/2+|a|+|b|. More than one corner attains it only if a or b
is zero. Both cannot vanish in this radius window. The remaining
center coordinate therefore has absolute value d+1/2, and the full
radial coordinate interval is [d,d+1]. This uses physical circle
corners, independently of their individual coefficients.
Because d>1, (6) excludes that entire mask.
The loaded tip consequently has one physical circle corner Z and
F_C is a strictly positive multiple of Z.

By (2), (5), write

    Z=(-X,-Y),     X>=0, Y>0,
    X/Y<=w/P<1/44,     X^2+Y^2=R^2.                   (7)

The bounds d>1 and R<=sqrt(1105)/16 give

    R^2>17/4,       2<R<25/12.

Thus

    X <= R w/P < 25/528 < 1/20,
    Y^2=R^2-X^2>4-1/400>1,
    0<Y-P<R-P<27/20.                                  (8)

### 1.3. A tip vertex cannot be the port

If p is any vertex of the actual tip, its distance from the different
circle vertex Z is either 1 or sqrt(2). Yet (6), (8) imply

    |Z-p| >= R-|p| > 1,

and, because X,w are both nonnegative and less than 1/20,

    |Z-p|^2=(X-w)^2+(Y-P)^2
            <(1/20)^2+(27/20)^2=73/40<2.              (9)

This is impossible. Every vertex/vertex, vertex/side and endpoint-
valued actual mean with a tip vertex is included in this argument.

### 1.4. A tip-side interior cannot be the port either

Otherwise p lies in the relative interior of a side of the actual
tip. Its supporting normal n is then that tip's own inward side
axis. In the orthonormal n,v coordinates, its full normal interval is
[p_n,p_n+1], and its transverse interval has length one. Put

    p_n=p.n=ws+Pc,
    p_v=p.v=wc-Ps.

By (4),

    0<p_v<=w<1/60.

Also s/c<1/44 implies c>10/11, so

    p_n> (11/15)(10/11)=2/3.                           (10)

The unique circle corner must maximize the positive normal coordinate:
Z_n=p_n+1. Its transverse absolute coordinate is at least 1/2, since
it is the farther endpoint of a length-one transverse interval.
The positive radial relation q_C=kappa Z, kappa>0, and q_C.v=p_v>0
show that its sign is positive. Thus Z_v>=1/2.

On the other hand q_C.n=p_n+ell>=p_n gives exactly

    Z_v=p_v (p_n+1)/(p_n+ell)
        <=p_v(1+1/p_n)<(1/60)(5/2)=1/24.               (11)

Equations (10)--(11) contradict Z_v>=1/2. The two port-location
possibilities exhaust the boundary of a square. The small-port lemma
is proved with all original means and masks retained.

## 2. An intact petal and a genuine S leaf force strict central-disk containment

Suppose the actual root H of an intact petal also carries a genuine
direct radial S leaf E. Its original application is d e, where e is
the leaf's actual unit direction. Keep every other H force.

**Central-disk theorem.**

    D_epsilon is contained in int H.                    (12)

For epsilon=0, this is already O in int H. Assume epsilon>0 and
suppose (12) fails. Then d=1+epsilon>1, and some actual H side has
positive height at most epsilon.

The leaf direction cannot be an H side axis: in that aligned case
H's full radial coordinate interval would be [d-1,d], which misses O.
It therefore strictly exposes a vertex of H. Choose H's own axes
and their signs so that this actual leaf application is (x,y), with

    x>=y>0,     x^2+y^2=d^2,
    H=[x-1,x] times [y-1,y].

Origin-interior containment gives x,y<1. Both x and y exceed epsilon,
because each of x^2,y^2 is greater than d^2-1=2epsilon+epsilon^2.
The smaller of the other two margins is sigma=1-x, so the assumed
failure of (12) gives

    0<sigma<=epsilon<1/60,
    H=[-sigma,1-sigma] times [y-1,y],
    y^2=2epsilon+epsilon^2+2sigma-sigma^2<=4epsilon,
    0<y<4/15.                                         (13)

For the displayed weak bound, the function 2sigma-sigma^2 is
increasing on [0,epsilon], so its maximum is
2epsilon-epsilon^2. All four actual H sides remain to be considered.

The left side has height sigma<1/5, and the right side has height
1-sigma>59/60>39/40. Neither can be the actual common petal side
by (1).

If the common side were the top, strict straddling would give one
actual boundary-tip port (z,y), with -sigma<=z<0. Its squared norm
would be at most

    sigma^2+y^2<1/3600+1/15=241/3600<1/4.

Every point of a physical boundary unit has norm at least R-sqrt(2),
which is greater than 67/120>1/2 in the original window. This excludes
the entire top-side alternative, including all side-mean endpoints.

Consequently the actual common side is the bottom. Its height is
P=1-y. By (1), (13),

    11/15<P<39/40.

Strict straddling supplies an actual left port p=(-w,-P) with
0<w<=sigma<1/60. Its actual normal has the signs in (3), by the
unchanged complete common-side normal-cone statement. The small-port
lemma applies and gives a contradiction.

Thus (12) cannot fail. This proof needs no other leaf root and no
particular graph away from H. It retains the genuine S-leaf force,
the intact petal's two actual loaded-tip equations and the full root.

## 3. Every genuine leaf root is H; no bridge-only internal body exists

Every genuine leaf root K meets D_epsilon. A D-leaf root contains O
openly. An S-leaf root contains the inward radial unit segment ending
at its actual application d v, hence contains epsilon v when d>1
and contains O when d<=1.

By (12), any such root distinct from H would meet int H. Even a
boundary point of a closed square in int H forces open-interior
overlap, since its own interior approaches that point. Therefore

    every genuine leaf root is H.                       (14)

For the following graph consequences use the original minimum-positive-
scalar-support selection and the small-core joins in
GLOBAL_CLOSURE_ARTICULATION_STRESS_SPLITTING.md. A bridge-only internal
body cannot be loaded. If U were such a truly unloaded body, O in int H
would force U to avoid O. The complete
GLOBAL_CLOSURE_OFF_ORIGIN_BRIDGE_TRANSMITTERS.md theorem would give an
actual incoming application in U with norm in (0,epsilon], contrary
to (12). Thus there is no bridge-only internal positive body.

## 4. Complete all-triangle block-tree exclusion

Assume the entire selected positive component has only triangles as
its cyclic blocks, arbitrary bridges, and at most nine bodies, and
contains an intact petal at H together with the genuine S leaf.

Root its actual finite block-cut tree at H, regarding each bridge as
a two-vertex block. Every terminal triangle has two actual private
degree-two loaded tips, so it is intact. Its root must be H, or the
origin-interior theorem would put O in the interiors of two distinct
actual units. Every terminal bridge is a genuine leaf and has root H
by (14).

If any block occurred farther from H, a farthest descendant would
be a terminal triangle or terminal bridge whose root differs from H.
Both alternatives have just been excluded. Hence every cyclic block
is an intact petal directly at H and every bridge is a genuine direct
leaf at H. No decorated block or positive branch was deleted to reach
this conclusion.

H is physically circle-clear. Its full original force equation is

    sum_j M_j + sum_i alpha_i v_i = 0,

where each M_j is a complete intact-petal resultant and each alpha_i
v_i a genuine direct-leaf force. The accepted petal pressure gives
c_H.M_j>0. Every genuine leaf also has positive center pressure:

    S: c_H.v_i=d-H_H(v_i)>=d-1/sqrt(2)>0;
    D: c_H.v_i=R-sqrt(2)-1/2>0.

Taking scalar product with c_H is a contradiction.

**Whole-family theorem.** No selected all-triangle cyclic block tree
with arbitrary bridge forests can contain an intact-petal root which
also carries a genuine S leaf.

Together with the independently accepted D-leaf theorem, this excludes
the full S/D type domain whenever an intact-petal root is a genuine
leaf root. The geometry (12) itself does not assume an all-triangle
component or minimum support; those hypotheses are used only in the
subsequent whole-graph application.

## 5. Exact original C2.33.b2 consequence

In the ten-layout cover TWO_TRIANGLE_TWO_BRIDGES_TEN_LAYOUT_REDUCTION.md,
the previously unresolved intact-petal layout is the complete graph

    HA,AB,BH, HC,CD,DH, HE,AL,

with genuine leaves E at H and L at A. H has its original degree five,
A degree three, and B,C,D true loaded degree two. The two other
original physical squares remain arbitrary.

If E is D, the accepted D-leaf central-disk theorem already excludes
the entire layout. If E is S, (12) and (14) exclude the distinct
genuine leaf root A directly, irrespective of the S/D type of L.
This therefore closes the complete original attachment, without
deleting HE or using a fictitious degree-four H equation.

The exact ten-layout cover now leaves only the no-intact attachment
with one leaf at a private tip in each of the two triangles. Its S/S
and S/D domains remain original obligations. No claim that the whole
coarse cell is closed is made here.

All nine physical squares, genuine positive-force degrees, actual
normals and means, physical circle masks and zero individual weights
remain. No sampled pose, scalar sign grid, numerical certificate,
Lean compilation, CI, remote action, or shared-ledger edit is used.
