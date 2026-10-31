# A genuine D root leaves at most one other unit in the fixed 3/125 disk

Date: October 28, 2026. Author: two_blocks.

**Status: complete proposed uniform physical theorem, submitted for full
root and separate independent review. No original gate is changed.**

Keep all nine original interior-disjoint closed unit squares, their
unchanged containing circle and compatible selected certificate in

    79/40 <= R <= sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1,
    epsilon=max(d-1,0)<1/60.

Suppose G has a genuine positive D leaf L. Its other forces and true
degree are arbitrary. Put sigma=3/125. Then **at most one actual unit
different from G can meet the closed disk D_sigma**. Those units need
no load, force, degree, contact or component premise.

In particular, once one other near unit is present, every remaining
actual closed unit U satisfies

    dist(O,U)>3/125>sqrt(2)*epsilon.

The second strict inequality follows from sqrt(2)<36/25 and
epsilon<1/60. This is the stronger distance required by the
far-body port theorem; it is not inferred from D_epsilon avoidance.

## 1. The genuine D root contains a fixed lower semicircle

The actual D-leaf/root classification gives, after rotating the
whole physical configuration,

    r=R-sqrt(2), s=1-r,
    G=[-s,r] x [a-1,a], 0<a<1,
    L={ (x,y): |x-(r+1/sqrt(2))|+|y|<=1/sqrt(2) }.

This keeps every actual additional G force and the real occupied
diamond L. Throughout the full stated radius interval,

    11/20<r<2/3, s>1/3.

For the lower bound use sqrt(2)<57/40 and R>=79/40. For the
upper use R<52/25 and sqrt(2)>140/99; their difference is
1648/2475<2/3. The positive squared reserves are 49/1600,
1599/160000 and 2/9801 respectively.

Suppose two distinct actual units K_1,K_2 different from G have
points x_i with |x_i|<=sigma. Such a point cannot lie in int G,
by density of the interior of its own full-dimensional square.
The two horizontal G margins r,s exceed sigma. Therefore one
vertical margin is at most sigma. Reflect the entire packing
vertically to obtain

    0<a<=sigma.

Set rho=1/3. The entire closed lower semicircle of radius rho
belongs to G: its horizontal coordinates are strictly between
-s and r, its minimum height exceeds a-1, and its maximum
height zero is less than a. Neither K_i is L, whose minimum
x-coordinate is r>sigma.

## 2. The two actual near units must have adjacent upward quadrants

At each actual x_i choose the signs of its own square axes toward
its center. At least half a unit remains along each chosen axis.
Order these orthonormal axes u_i,v_i so that v_i=J u_i. Thus

    x_i+[0,1/2]u_i+[0,1/2]v_i is a subset of K_i.

Let phi_i be the angle of u_i and put beta=arcsin(3/40).
Every point of the closed radius-rho arc with angle in

    I_i=[phi_i+beta, phi_i+pi/2-beta]

belongs to int K_i. Both own projections relative to x_i are
strictly positive because

    rho*sin(beta)=1/40>sigma,

and both are at most rho+sigma<1/2. They are therefore strictly
inside the actual half-unit own intervals. No actual square
frame or nearby point has been moved.

The two arcs are disjoint and lie in the open upper semicircle.
Otherwise one of their interior square points would belong to
the closed G, forcing open-interior overlap. Order the two
nonwrapping intervals from east to west and name their units
K_R,K_L. Their actual angular endpoints give

    -beta<=phi_R<=3 beta,
    pi/2-3 beta<=phi_L<=pi/2+beta,
    |phi_R+pi/2-phi_L|<=2 beta.

Use the following full-interval bounds:

    cos(2 beta)=791/800,
    sin(2 beta)<3/20,
    sin(3 beta)=3573/16000<9/40,
    cos(3 beta)>97/100.

The last bound follows from 3 beta<pi/2 and
1-(9/40)^2>(97/100)^2. These are exact trigonometric and
rational comparisons, not sampled angular assertions.

## 3. An actual separating axis controls the right unit's left face

Two disjoint square interiors have a separating axis parallel to
an actual own side axis of one of the squares. This follows from
the edge directions of their convex difference polygon and retains
weak physical contact.

Neither upward axis v_R nor u_L can separate K_R from K_L.
Along either such axis each square's actual half-unit north
segment starts at a projection of absolute value at most sigma
and ends at projection at least

    (1/2)(791/800)-sigma>1/4.

Since sigma<1/8, both full projection intervals contain [1/8,1/4]
in their interiors. The actual separator is therefore one of
the two rightward own axes

    r_0=u_R or r_0=-v_L.

The real half-unit east segment of K_R has a point of positive
r_0 projection, and the real half-unit west segment of K_L
has a point of negative r_0 projection, using the same positive
lower bound (791/1600)-sigma. Hence K_R is the right square
in this separating coordinate. In particular

    min_(K_R) r_0.x >= max_(K_L) r_0.x
                      >= r_0.x_L >= -sigma.

Now use the actual own axes r_*=u_R, n_*=v_R of K_R, and write
its full own intervals as [l_r,l_r+1] and [l_n,l_n+1]. Its
near point and its genuine half-unit north segment give

    l_r<=sigma, l_n<=sigma, l_n+1>=1/2-sigma.

Write r_0=A r_*+B n_*. The angular bounds in Section 2 imply
A>=791/800 and |B|<3/20. The point of the actual left K_R
face with n_* coordinate n_*.x_R belongs to K_R. Applying
the real separator inequality to that point gives

    A l_r+B(n_*.x_R)>=-sigma,
    l_r>-(920/791)sigma=-552/19775.

Consequently its actual right-face coordinate satisfies

    l_r+1>19223/19775.

This uses either possible owner of the separating axis. A
common orientation of the two near squares has not been assumed.

## 4. One fixed actual point overlaps the D leaf

In the original leaf coordinates choose

    q=(r+1/4,6/25), X=r+1/4.

This point belongs to int L. Indeed 1/4>6/25, and the exact
diamond inequality reads

    |1/4-1/sqrt(2)|+6/25=1/sqrt(2)-1/100<1/sqrt(2).

The full radius range gives 4/5<X<11/12. Put theta=phi_R.
The two actual own axes of K_R are

    r_*=(cos(theta),sin(theta)),
    n_*=(-sin(theta),cos(theta)).

Section 2 gives cos(theta)>97/100 and |sin(theta)|<9/40.
Therefore the first actual own projection satisfies

    q.r_*>(4/5)(97/100)-(6/25)(9/40)=361/500>sigma,
    q.r_*<11/12+(6/25)(9/40)=364/375<19223/19775.

The second satisfies

    q.n_*>(6/25)(97/100)-(11/12)(9/40)
           =531/20000>sigma,
    q.n_*<6/25+(11/12)(9/40)=357/800<1/2-sigma.

These strict inequalities put both own coordinates of q
strictly inside the full K_R intervals from Section 3. Thus
q belongs to int K_R as well as int L. The two actual units
are distinct, contradicting their disjoint open interiors.

This proves the whole fixed-disk theorem, including points on
the boundary of D_sigma, points on the boundaries of K_i,
all weak contact equalities and every orientation.

## 5. Inputs, exact checks and scope

The genuine D chart and its physical selected-contact scope are
those of `RADIAL_BRIDGE_AND_LEAF_REDUCTION.md`, SHA256
`faf453b3c519b10590cf9d6f6dbf9282233bd2ff04c90aa0cd8cd89e060bc676`.
The arc/separating-axis proof follows the complete physical method
of `D_LEAF_TWO_DISTINCT_NEAR_ORIGIN_UNITS_EXCLUSION.md`, but the
larger disk, all new constants and the actual witness are proved
in full above. No stronger conclusion is attributed to that source.

The companion exact record checks the displayed rational reserves
and the elementary polynomial identities. Such arithmetic checks
accompany the whole angular and feature argument; they do not
replace it. No unit has been replaced by a radial surrogate and
no equation at K_1 or K_2 is used. Every original G force remains.

This is a force-free physical implication once the genuine D chart
is established. It needs no same-nine R>2 import: all geometric
comparisons above hold on the stated full window. It changes no
fine identifier, coarse cell, source header or shared ledger and
uses no Lean build, compilation, CI, numerical pose or remote write.
