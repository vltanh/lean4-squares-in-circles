# A genuine D leaf leaves at most one other unit near the origin

Date: October 27, 2026.

**Status: accepted complete hand proof at its stated original scope; full root and separate independent source/scope reviews passed.**

Accepted reviews: REVIEW_D_LEAF_TWO_NEAR_ORIGIN_LEAF_PAIR_2026_10_27.md and
REVIEW_NEAR_ORIGIN_AND_ATTACHMENT_CLOSURES_ROOT_2026_10_27.md.
Their mathematical-source pins precede this acceptance-only header update.

Keep the original nine interior-disjoint physical unit squares, their
original selected certificate, and

    79/40 <= R <= sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1,   epsilon=max(d-1,0)<1/60,
    r=R-sqrt(2),         s=1-r.

Suppose H has a genuine positive D leaf L. Thus, in the original D-leaf
frame, the radial-leaf theorem gives

    H=[-s,r] times [a-1,a],   0<a<1,
    L={ (x,y): |x-(r+1/sqrt(2))|+|y| <= 1/sqrt(2) }.
                                                               (1)

H may have arbitrary additional positive forces, circle masks and degrees.
Let K_1,K_2 be two distinct actual units, both different from H, each
meeting the closed disk D_epsilon. They need not be loaded, leaf roots,
neighbors of H, or members of H's positive component.

**Theorem.** This entire physical configuration is impossible.

The proof uses the actual D leaf and elementary geometry. It does not
replace either K_i by a radial surrogate or use its force equations.

## 1. The root contains a fixed lower semicircle

The genuine D root H contains O in its open interior. If epsilon=0,
each K_i contains O and therefore meets int H, forcing interior overlap.
Hence assume epsilon>0.
Then d>1 and R>sqrt(17)/2. The exact bounds are

    0<epsilon<1/60,   129/200<r<2/3,   1/3<s<71/200.
                                                               (2)

For the lower r bound, R>103/50 and sqrt(2)<283/200 suffice.
For the upper bound, R<52/25 and sqrt(2)>140/99 give

    r<52/25-140/99=1648/2475<2/3.

These rational comparisons follow by squaring positive numbers; in
particular (52/25)^2-1105/256=1599/160000>0 and
2-(140/99)^2=2/9801>0. The standard d<61/60 bound gives epsilon<1/60.

Choose actual x_i in K_i with |x_i|<=epsilon. No x_i belongs to int H.
The two horizontal side distances r,s exceed epsilon. Consequently
one vertical side of H has distance at most epsilon. Reflect the whole
physical configuration vertically, if necessary, so that (1) satisfies

    0<a<=epsilon.

Put

    rho=4/15,   delta=arcsin(1/16).

By (2), H contains the entire closed lower semicircle of the radius-rho
circle: its horizontal distances exceed rho, and 1-a>rho. This is the
only shape input about H used in the next two sections.

## 2. The two near-origin units have a left and a right quarter

At each x_i choose the sign of each actual own side axis toward the
center of K_i. At least one half-unit remains from x_i along each
chosen axis. Order them as u_i,v_i with v_i=J u_i. The actual K_i contains

    x_i+[0,1/2]u_i+[0,1/2]v_i.

If phi_i is the angle of u_i, every point y on the closed radius-rho arc

    I_i=[phi_i+delta, phi_i+pi/2-delta]

belongs to int K_i. Indeed both own projections of y-x_i are strictly
positive, since rho sin(delta)=1/60>epsilon, and each is at most
rho+epsilon<17/60<1/2. Such a point is interior even to the selected
quarter-square.

The two arcs are disjoint, and both lie in the open upper semicircle:
otherwise an interior point of K_i would lie in closed H, which also
forces interior overlap. Order their nonwrapping angular intervals from
east to west, and call their units K_R,K_L respectively. Their endpoints
give

    phi_R+delta>=0,
    phi_L+pi/2-delta<=pi,
    phi_R+pi/2-delta<=phi_L+delta.

Consequently

    -delta<=phi_R<=3delta,
    pi/2-3delta<=phi_L<=pi/2+delta,
    |phi_R+pi/2-phi_L|<=2delta.                         (3)

Thus the actual selected upward directions v_R,u_L differ by at most
2delta, as do the actual rightward directions u_R,-v_L. We use

    cos(2delta)=127/128,   sin(2delta)<1/8,
    sin(3delta)=191/1024<3/16,   cos(3delta)>49/50.       (4)

For the last inequality, 1-(3/16)^2=247/256>(49/50)^2 and
0<3delta<pi/2. These are whole angular bounds, not angle samples.

## 3. The actual separating axis controls the right unit's left face

Two squares with disjoint open interiors have disjoint projection
interiors along a side axis of at least one of them. This standard
separating-axis fact follows directly by considering their convex
difference polygon: every edge is parallel to an original side edge.

Neither upward axis v_R nor u_L can separate K_R,K_L. In either such
axis n_0, the selected actual half-unit north segments have endpoint
projections at most epsilon at their bases and at least
-epsilon+127/256 at their tips. Both full projection intervals therefore
contain [1/8,1/4] in their interiors, using epsilon<1/60.

The separating axis is consequently one of the actual rightward axes

    r_0=u_R or r_0=-v_L.

K_R has an actual point of r_0-projection at least
-epsilon+127/256>0; K_L has an actual point of projection at most
epsilon-127/256<0. Their separated order must therefore be K_R to the
right of K_L. In particular

    min_{K_R} r_0.x >= max_{K_L} r_0.x >= r_0.x_L >= -epsilon.
                                                               (5)

Use the actual own right/up axes r_*=u_R,n_*=v_R of K_R. Write its own
coordinate intervals as [l_r,l_r+1] and [l_n,l_n+1]. Its contained point
x_R and its contained half-unit north segment give

    l_r<=epsilon,  l_n<=epsilon,  l_n+1>=1/2-epsilon.    (6)

Write r_0=A r_*+B n_*. From (3)--(4), A>=127/128>0 and |B|<1/8.
The point of K_R's left face with n_*-coordinate n_*.x_R is an actual
point of K_R. Applying (5) to it yields

    A l_r+B(n_*.x_R)>=-epsilon,
    l_r>=-(144/127)epsilon>-12/635>-1/50.

Thus the actual right face has coordinate

    l_r+1>49/50.                                        (7)

The chosen separating axis may belong to either square. No common
orientation of K_R,K_L is assumed.

## 4. One fixed point is inside the D leaf and the right unit

In the original coordinates of (1), take

    q=(r+1/4,1/5),   X=r+1/4.

This point belongs to int L. Relative to L's inner radial vertex (r,0),
its two diagonal side coordinates are positive because 1/4>1/5,
and their sum is 9/20<sqrt(2). Equivalently, directly in (1),

    |1/4-1/sqrt(2)|+1/5=1/sqrt(2)-1/20<1/sqrt(2).

By (2),

    179/200<X<11/12.

Write theta=phi_R. The actual own axes are

    r_*=(cos(theta),sin(theta)),
    n_*=(-sin(theta),cos(theta)).

Equations (3)--(4) imply cos(theta)>49/50 and |sin(theta)|<3/16.
The first projection of q obeys

    q.r_*>(179/200)(49/50)-3/80>1/60,
    q.r_*<11/12+3/80=229/240<49/50.                     (8)

The second obeys

    q.n_*>49/250-11/64=193/8000>1/60,
    q.n_*<1/5+11/64=119/320<1/2-1/60.                  (9)

Every comparison is strict. The closest displayed reserves are
193/8000-1/60=179/24000, 49/50-229/240=31/1200, and
1/2-1/60-119/320=107/960.

Equations (6)--(9) put both own coordinates of q strictly inside
K_R's original unit intervals. Therefore q belongs to int K_R.
This contradicts q in int L. These are distinct actual units: every
point of the boundary square L has norm at least r>epsilon, whereas
K_R has the actual point x_R in D_epsilon.

This proves the theorem for the entire radius interval.

## 5. Degree-independent leaf-root consequence

Every genuine S/D leaf root meets D_epsilon by its actual radial unit
segment; for d<=1 it contains O. Thus an original packing cannot have
three distinct genuine leaf roots if at least one has a D leaf.
The roots may have arbitrary true degrees, further cyclic blocks,
additional leaves, circle masks, selected normals and actual means.

In particular, all D-containing assignments of the original shared-H
two-triangle layouts with leaves at H,A,C or at A,B,C are excluded by
this one physical theorem. No positive force or physical square has
been discarded. It does not exclude their all-S assignments or claim
that an entire coarse cell is closed.

The quarter-circle and separating-axis technique is adapted from
INTACT_PETAL_TWO_DISTINCT_NEAR_ORIGIN_UNITS_EXCLUSION.md, Sections 2--4.
The present fixed witness belongs to the actual D leaf, and all new
coordinate inequalities and force-independent hypotheses are proved
above. No Lean compilation, CI, numerical search, scalar certificate
table, or central-ledger change is used.
