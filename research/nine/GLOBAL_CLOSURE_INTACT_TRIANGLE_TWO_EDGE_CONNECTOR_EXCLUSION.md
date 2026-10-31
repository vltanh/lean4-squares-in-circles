# An intact end triangle cannot connect to another triangle through an unloaded body

Date: October 26, 2026.

**Status: accepted complete geometric theorem and whole two-edge-connector
exclusion after full root review in
REVIEW_INTACT_TRIANGLE_TWO_EDGE_CONNECTOR_ROOT_2026_10_26.md and separate
independent review in
REVIEW_INTACT_TRIANGLE_TWO_EDGE_CONNECTOR_ROOTED_BLOCKS_2026_10_26.md.**
No ledger is changed.

Keep all nine original physical unit squares, the common compatible
selected certificate, and

    79/40 <= R <= sqrt(1105)/16.

The main geometric lemma below extends the accepted contact-triangle
enclosure argument while retaining an arbitrary full external aggregate
at the third triangle body. Its application excludes every two-triangle
component with an intact end triangle and a two-edge bridge path between
the two cyclic blocks. It does not exclude all of C2.33.b2, b3, or b4:
direct connectors and layouts without an intact petal retain their
separate obligations.

## 1. A reusable near-extreme-root exclusion

Put

    d=sqrt(R^2-1/4)-1=1+epsilon,
    0<epsilon<1/60.

Suppose A,B,C are three distinct actual units with all three positive
triangle edges. A has precisely one external positive pair edge, a
radial bridge to a distinct actual unit U. Keep any actual circle
resultant G_A at A. In a frame about the original circle origin, assume
the unchanged bridge application and actual squares have the forms

    p=(-rho,0),               59/60<rho<61/60,
    A=[-rho-1,-rho] times [t-1/2,t+1/2], |t|<1/8,
    U=[-rho,1-rho] times [u-1/2,u+1/2], |u|<=1/2.       (1)

The bridge force at A is alpha e_x, alpha>0. No force equation at U is
assumed in this local lemma.

B has one genuine direct S leaf, of direction v, and no other external
positive pair edge. Its actual leaf force is beta v, beta>0. The radial
leaf theorem makes B physically circle-clear and gives

    d v in B,                epsilon v in B.             (2)

At C retain its entire actual external force system, with resultant
F_C. Assume only that this system has zero origin moment. In particular
it may contain an actual circle load and additional radial bridges.
The three complete triangle external systems are

    F_A=G_A+alpha e_x,        F_B=beta v,        F_C.       (3)

All of their origin moments are zero; their force sum is zero by the
full original triangle equations. No positive force is dropped.

**Local theorem.** The entire configuration (1)--(3) is impossible.

### 1.1. The two nearby centers lie on opposite vertical sides

Every original center has norm <91/60. In addition,

    |c_U|^2 < (31/60)^2+1/4 =1861/3600 <(29/40)^2,
    |c_B| <epsilon+sqrt(2)/2 <29/40.                     (4)

The strict reserve in the second comparison of the first line is
5/576. Also

    c_Ux=1/2-rho<-11/40,
    c_Bx<=-rho+sqrt(2)/2<-11/40.                         (5)

For the last inequality use rho>59/60 and sqrt(2)/2<17/24.
The centers' horizontal difference is less than 9/20. Their distance
is at least one because the open unit incircles are disjoint. Thus

    |c_By-c_Uy|>7/8.

Since |c_Uy|<=1/2, reflection permits

    c_By>3/8,             every point of B has y>-3/8.    (6)

These estimates do not require O to belong to U. This is the first
important difference from the original long-arm application.

Write b_-=t-1/2 and b_+=t+1/2. Then

    b_-<-3/8<0<3/8<b_+.

At the actual AB support, B's D_epsilon intersection bounds its support
height by epsilon. Every top/bottom side or left-facing feature of A has
support height above 3/8, so the AB normal n has n_x>0 and its application is on
A's right wall. Equation (6) excludes the lower-right vertex. The full
AB feature cover is therefore

    n=e_x, P=(-rho,y), b_-<=y<=b_+;
    or P=(-rho,b_+), n_x>0, n_y>0.                       (7)

### 1.2. Every left interface of A is impossible

Use the radius-free corner-center lemma proved in Section 3 of
`GLOBAL_CLOSURE_LONG_ARM_AND_DIRECT_LEAF_TRIANGLE_EXCLUSION.md`.
At a square vertex p with inward orthonormal axes e_1,e_2, every
neighbor T whose actual separating normal exposes that vertex obeys

    (c_T-p).(e_1+e_2)<=0.                               (8)

Its proof uses |c_T-p|<=sqrt(2)/2 and the neighbor's support halfwidth
at least 1/2; it includes axis endpoints and selects no new normal.

At either left A vertex, (8) implies one of

    c_Tx+c_Ty < -119/60-3/8=-283/120,
    c_Tx-c_Ty < -283/120.

Both contradict |c_Tx +/- c_Ty|<sqrt(2)*91/60<273/120.
A left-side-interior neighbor would have center x<=-rho-3/2<-91/60,
also impossible. Thus the AC contact is on the right wall or has a
vertical side normal. The bottom-side alternative separates C from
all of B by (6), preventing their required contact. The only remaining
alternative to the right wall is

    m=e_y, Q=(x,b_+),       -rho-1<=x<=-rho.              (9)

### 1.3. The entire top-side alternative retains G_A and F_C

The actual A equation is

    G_A+alpha e_x+mu n+nu m=0,       mu,nu>0.             (10)

If AB strictly exposes the upper-right vertex in (7), then (9)--(10)
give (G_A)_y=-mu n_y-nu<0. Moments about p=(-rho,0) are

    circle: rho (G_A)_y<0;
    AB:     -b_+ mu n_x<0;
    AC:     (x+rho)nu<=0.

Their sum cannot vanish. This uses the full actual circle resultant,
including the possible zero resultant.

It remains that AB uses n=e_x with its actual mean (-rho,y).
Origin moment gives

    -mu y+nu x=0,             y=nu x/mu<0.              (11)

Thus the common triangle moment is nonzero. The complete external
noncollinearity theorem
`RADIAL_TRIANGLE_EXTERNAL_RESULTANTS_NONCOLLINEAR.md` applies to (3),
and `RADIAL_TRIANGLE_CONCURRENCE.md` supplies a positive concurrence at
each nonparallel root, with its actual proper ports.

If B's cycle pair were parallel, both its outward normals would point
west. Its full equation would give v=e_x. But every point of B has
x<c_Bx+sqrt(2)/2<13/30, whereas d v in B has x=d>1.
This is impossible. In particular no second, coincident S leaf is
needed to exclude this parallel case.

Hence B is nonparallel and

    q_B=P+s e_x=tau_B beta v,        s>=0, tau_B>0.

Equation (11) gives v_y<0. At C, if the cycle pair is parallel, both
outward normals point downward and its full external resultant obeys
(F_C)_x=0. If nonparallel, its proper CA port gives

    q_C=Q+s' e_y=tau_C F_C,          s'>=0, tau_C>0,

so (F_C)_x<0 because Q_x=x<0. Thus (F_C)_x<=0 in every case. Summing
the complete triangle equations in (3), using F_A=-mu e_x-nu e_y,
now gives

    beta v_x=mu-(F_C)_x>0.

The actual leaf application d v in B is strictly southeast. Equations
(5)--(6) bound it by

    0<(d v)_x<13/30,       0<-(d v)_y<3/8,
    |d v|^2<4729/14400<1,

contradicting d>1. This excludes the entire top-side alternative, with
all mean endpoints and the full original C external system retained.

### 1.4. Actual moment cancellation forces the impossible contact enclosure

Both A triangle contacts now belong to its right wall with positive
horizontal normal component. On that wall the origin moment of a
support normal has sign opposite to its application height: this is
immediate for the side axis, and at a strict upper or lower vertex it
follows from

    det((-rho,y),n)=-rho n_y-y n_x.

Zero moment occurs only at p=(-rho,0), with normal e_x. Since G_A and
the bridge have zero origin moment, either both triangle moments vanish
or the two actual heights have strictly opposite signs.

If both vanish, B,C,U all contain p in the right half-plane beside A.
Their three interior-disjoint tangent cones, each of angle at least
pi/2, cannot lie in the same semicircle. Otherwise name the ports

    P_-=(-rho,y_-), P_+=(-rho,y_+),       y_-<0<y_+.

The actual BC application Q belongs to both B,C. If Q_x<-rho, one
of the two segments from Q to P_- or P_+ immediately enters A's
interior, according to the sign of Q_y. If Q_x=-rho and Q_y!=0,
one of those segments has p in its relative interior; that square
occupies the right local half-plane beside A and overlaps U near p.
If Q=p, the same three-cone contradiction applies. These cover all
collinear and coincident cases, including endpoint means.

Thus Q_x>-rho. The nondegenerate triangle with vertices P_-,P_+,Q
has all boundary segments in the actual closed squares A,B,C.
The actual U lies to the right of its base and has p on its left
side, possibly at an endpoint. Some U interior points near p lie
inside this triangle. Convexity of U's interior and its avoidance
of the entire occupied boundary force all of U's interior inside.
But the triangle's base is at most one and its height at most sqrt(2),
because Q and each relevant base endpoint belong to one actual unit.
Its area is at most sqrt(2)/2<1, whereas U has area one. Contradiction.

This is the complete barrier argument from Sections 5--6 of the
accepted long-arm source, with exactly its physical hypotheses now
verified. It uses no load or degree assumption at C or U. The local
theorem is proved.

## 2. Apply the lemma to every two-edge connector from an intact triangle

Assume now the common minimal-support selected scope of
`GLOBAL_CLOSURE_ARTICULATION_STRESS_SPLITTING.md`, including its named
small-core joins. Let the positive component have exactly two cyclic
blocks, both triangles, with any attached bridge forests and at most
nine actual bodies. Suppose one triangle H,T1,T2 is intact: its two
tips have their true positive degree two and positive circle loads.
Suppose the block-connecting bridge path has two edges

    H -- U -- A,

where A is a vertex of the other actual triangle A,B,C. This is an
assumption on the entire original block tree, not a deletion of any
attached force.

The complete splitting theorem makes every loaded bridge-only body a
genuine leaf. Thus U is genuinely unloaded. The accepted end-triangle
origin theorem gives O in the open interior of H. Every other actual
unit therefore avoids O even on its boundary.

Apply `GLOBAL_CLOSURE_OFF_ORIGIN_BRIDGE_TRANSMITTERS.md` to each positive
unloaded bridge-only body. It has exactly two positive neighbors, is
side-normal, and has a unique inward neighbor containing O. That
neighbor must be H. In particular U has exactly the two displayed
neighbors, and in its outward direction its applications have radii

    eta in (0,epsilon],            rho=eta+1 in (1,d].   (12)

This proves d>1. Rotate its outward direction west. The actual U and
its application at A are exactly as in (1), with |u|<=1/2, and
A lies in x<=-rho and contains p=(-rho,0).

### 2.1. The outer triangle root has the required full chart

The application p cannot be an A vertex, including an axis endpoint.
If its inward orthonormal axes have nonpositive x components -a,-b,
then a,b>=0 and a^2+b^2=1. The center would satisfy

    |c_A|^2=rho^2+rho(a+b)+1/2
           >=rho^2+rho+1/2>5/2>(91/60)^2.

Therefore p is in the relative interior of a side, giving the actual
axis-aligned chart A=[-rho-1,-rho] times [t-1/2,t+1/2]. Circle
containment gives

    (rho+1)^2+(|t|+1/2)^2<=R^2<=1105/256,
    |t|+1/2 <sqrt(1105/256-4)=9/16,
    |t|<1/16<1/8.                                     (13)

This retains any original A circle force. A may be physically boundary;
no leaf-only or degree-two equation is imposed on it.

### 2.2. Exhaust all remaining bridge attachments at the other triangle

Every positive bridge-only internal body would have to be adjacent to
H as its inward neighbor. Thus there is no nontrivial pendant path or
outside fork attached at A,B, or C. Any further bridge attached there
must go directly to a genuine leaf.

A cannot have such a leaf: its distance from O is rho>1, whereas every
genuine leaf root meets D_epsilon. Hence A's only external pair edge is
AU, as required by the local theorem.

If neither B nor C has an attached bridge, both are true degree-two
loaded tips. Then A is a second intact end-triangle root and contains O
openly, contradicting the actual H. Thus at least one of B,C has a
genuine direct leaf; call that root B.

It cannot be D, because a D leaf puts O in its root's open interior,
again overlapping H. It is S. Also B cannot carry two distinct genuine
leaves: the complete two-leaf-root geometry in
`TRIANGLE_THREE_BRIDGES_DOUBLE_LEAF_ROOT_EXCLUSION.md`, Section 1,
puts O in every such root, with arbitrary other neighbors retained.
Consequently B has exactly its two triangle forces and the one actual
S-leaf force. The same argument shows C is either an untouched loaded
tip or a single-S-leaf root. Its complete external system has zero
origin moment in either case.

All hypotheses of Section 1 now hold, including A's possible circle
load and C's full actual external system. Its contradiction excludes
the entire original two-edge-connector family.

## 3. Exact graph scope and remaining obligations

The same origin/off-origin argument shows that an intact end triangle
cannot connect to another cyclic block through two or more internal
bridge-only vertices: each would have to have H as its inward neighbor,
whereas a block-tree path cannot do so. The present result disposes of
the sole remaining case with one internal body, when the other block
is a triangle.

Thus, in the complete two-triangle bridge inventory, whenever an intact
triangle is present, the two distinct cyclic blocks must be joined by
a single bridge or share their articulation. This conclusion retains
all original tip attachments and all genuine higher root degrees.

It is not a complete C2.33.b2/b3/b4 closure. In particular, a direct
intertriangle bridge with further genuine forces at its endpoints,
shared-hub layouts with tip leaves, and layouts in which neither
triangle has two untouched tips have not been removed by this theorem.
No original gate is changed. No Lean compilation, CI, remote action,
numerical pose, or sampled parameter certificate is used.
