# One unloaded return hub gives a common moment reduction for three S-leaf families

Date: October 28, 2026. Author: s_family.

**Status: complete proposed uniform theorem and exact partial original-family
joins, submitted for root and separate independent review. No original
checkbox changes before or after this partial reduction alone.**

This manuscript removes the entire strict-low-radius domains of the original
roof AC.S, roof ABC.S and endpoint-fan 234.S families by one argument. It
also removes their entire tilted critical-radius domain and confines every
high-radius tilted root to a shallow chart. The high aligned and shallow
tilted domains remain. The proof uses no computational exclusion certificate.

Throughout, retain all nine actual interior-disjoint closed unit squares,
the unchanged containing circle, and the one compatible selected physical
certificate, with

    79/40 <= R <= sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1,
    epsilon=max(d-1,0),
    r=R-sqrt(2).

The established elementary bounds are

    9/10<d<61/60,  0<=epsilon<1/60,  r>11/20.

Every original positive force, physical circle corner, individual zero
circle weight, true degree, shared mean and endpoint, additional physical
contact and arbitrary completing unit remains present.

## 1. Uniform theorem with arbitrary true degree at the unloaded hub

Let X be an actual genuine leaf root whose entire positive neighbor set is
exactly L,A,H, where L is its genuine positive leaf. Assume the following
literal properties of its entire positive component.

1. A is physically boundary, H is unloaded (zero total circle force),
   and O belongs to int(X).
2. Deleting X and L leaves a connected original positive graph G. The
   only vertices of G incident to X are the distinct actual A,H.
3. Every vertex of G other than H is either physically boundary or a
   true unloaded degree-two transmitter. Each such transmitter has two
   distinct physical boundary neighbors in G. In particular H is not
   adjacent to one of those transmitters.

Physical boundary status in this theorem does not require positive total
circle load. The true degree of H and of all boundary vertices is arbitrary.
No degree-two equation is imposed on any boundary vertex unless its own
literal caller has that degree. All positive edges outside the displayed
local triangles, if any, are included in G and in the full original stars.

Let n be the original X-to-H unit normal, p its unchanged application,
and h=h_X(n)=p.n. Then

> **Uniform conclusion:** h<=epsilon.

Since O is open in X, h>0. Thus the conclusion is an exact small-support
condition on the original force, not a replacement force or chosen mean.
In particular the entire configuration is impossible when d<=1.

The theorem does not assume a physical A--H contact. That contact will be
used separately in Section 6 to cover the non-open aligned low S endpoints.
The genuine leaf may be S or D in Sections 1--5.

## 2. Nonradial private edges, including every transmitter mean

Suppose for contradiction that h>epsilon. Reversing the actual support
at H gives

    h_H(-n)=-h<-epsilon.

Every point of H therefore lies outside closed D_epsilon. Every point
of a physical boundary unit has norm at least r, by its distance at most
sqrt(2) from an actual circle corner. Thus all nontransmitter vertices
of G avoid closed D_epsilon.

Every actual contained unit has center norm at most d+1/2. A contained
unit beyond a support f.x>=t, with |f|=1, consequently requires t<=d:
its normal half-width is at least 1/2. These physical bounds do not use
any force or circle-load premise at that unit.

### 2.1. Edges between units avoiding the small disk

Such an original edge cannot have zero origin moment. Otherwise its
application is p=t f, t>0, with an inner unit U on f.x<=t and an outer
neighbor on f.x>=t; the p=O case already contradicts disk avoidance.
The outer support bound gives t<=d.

Because U avoids O, at least one of its own intervals misses zero.
Reflect that own coordinate to [a,a+1], a>0. Radial outward support
places the corresponding coordinate of p at a+1, so t>1 and

    a<=t-1<=epsilon.

If both own intervals miss zero, both absolute coordinates of p exceed
one, giving t>sqrt(2)>d. If just one does, the other interval contains
zero and the actual point (a,0) belongs to U and closed D_epsilon.
Both alternatives contradict the original physical premises.

### 2.2. An actual two-force transmitter between boundary units

Let B be any transmitter in Section 1, with original application means
p_0,p_1 at its two physical boundary neighbors. Its full force equation
gives equal positive magnitudes and opposite normals. Write e for the
original normal directed through B from its first neighbor to its second.
The full B torque equation and the actual support width give

    p_1-p_0=w e,  w=w_B(e)>=1.                         (1)

Every point of [p_0,p_1] lies in the actual B. This retains the original
side means, their endpoints and the entire actual width; no midpoint or
new mean is selected.

Since O is in int(X), every other actual closed square avoids O. Indeed
a point of such a square in int(X), even a boundary point of that square,
would yield nearby points of its open interior in int(X). In particular B
avoids O, and the compact chord (1) has positive clearance from O.

If either original transmitter edge had zero origin moment, both would,
by (1). Their two nonzero radial coordinates on the common line through
O have the same sign. The nearer endpoint belongs to an actual boundary
unit and has radius at least r. The farther endpoint therefore has radius
at least r+w>=r+1>d. The actual neighbor beyond that farther endpoint
violates the preceding support bound t<=d. Thus both original edge
moments are nonzero, including every original mean endpoint.

Sections 2.1--2.2 prove that every edge of G has nonzero original moment.
Orient each original edge by the direction of its positive origin moment.

## 3. A directed private cycle would wind about the occupied root

At every physical boundary vertex U, its actual distance from O is at
least r>sqrt(2)*epsilon. Section 1.2 of
`HOUSE_ROOF_AC_D_COMPLETE_MOMENT_EXCLUSION.md` therefore gives its full
far-body port theorem: a negative incoming outward moment followed by a
positive outgoing outward moment has nonnegative angular advance through
the actual application chord of U. This theorem places no disk-avoidance
condition on U's neighbors, so an adjacent real transmitter causes no
gap in the invocation. U retains its full actual degree and other forces.

At H, the actual unit and its two neighbors on any cycle avoid closed
D_epsilon: those neighbors are boundary units by Section 1. Thus the
degree-free port theorem of
`GLOBAL_NEXT_DEGREE_FREE_MOMENT_PORT_ORDER_AND_INTACT_BLOCK_EXCLUSION.md`,
Section 2, gives the same nonnegative angular advance at H.

At any transmitter B lying on a directed cycle, the directed passage
uses exactly its two original edges. In (1), the actual directed moment
is positive. Along its original chord z(t)=p_0+t e, 0<=t<=w,

    d(arg z(t))/dt=det(z(t),e)/|z(t)|^2
                  =det(p_0,e)/|z(t)|^2>0.             (2)

This is strictly positive angular advance for the whole real chord,
including the endpoint means. The chord avoids O as proved in Section 2.

Suppose now that G contains a directed cycle C. If C contains a
transmitter, all its vertex advances are nonnegative and at least one
is strictly positive by (2). The total angular advance of its closed
contact loop is then a positive integer multiple of 2pi.

If C contains no transmitter, all its units avoid closed D_epsilon.
The complete directed-cycle theorem in Section 3 of the same degree-free
port source gives strictly positive winding. Its proof includes the
coincident-port equality case: zero advance at every vertex would put
at least three actual unit tangent sectors at their one shared nearest
point inside a single half-plane, which is impossible.

Use the original compatible physical embedding. Homotoping its
center-to-application strands to the application chords inside the actual
convex cycle units avoids O. Its sufficiently close weak-junction routing
has the same winding, since those finitely many units have positive O
clearance. The embedded C is therefore a Jordan cycle enclosing O.

The whole compact segment from O to c_X belongs to int(X) and misses
every private cycle unit. The routing neighborhoods can be chosen smaller
than that clearance, so c_X is inside the same cycle. The original XL
edge is disjoint from C and puts c_L inside it too. This contradicts the
actual boundary leaf L's protected access to the unbounded face in the
same physical embedding.

Therefore the positive-moment orientation of G is acyclic. No scalar
stress at an altered graph, new physical contact or deleted force is
part of this argument.

## 4. The unique unloaded attachment is an opposed-moment star

The connected graph G has at least the distinct vertices A,H. An
acyclic orientation of a nontrivial connected graph has a distinct
source and sink, each incident to a private edge. No vertex other than
A,H can be either: all of its original positive pair forces lie in G,
and its full origin-torque equation says their signed moments sum to
zero. Its physical circle atoms have zero origin moment, regardless
of their individual weights. All private edge moments are nonzero.

Thus A and H are the two extrema, in opposite roles. Every original
private moment at H has one common strict sign. Its full original torque
equation makes the original HX moment nonzero with the opposite strict
sign. H is unloaded, and this is its entire original star, with arbitrary
true degree.

The exceptional HX support is h_H(-n)=-h<-epsilon. Consequently Section 1
of `UNLOADED_OPPOSED_MOMENT_STAR_AND_LOWER_HOUSE_TDC_D_SMALL_SUPPORT_REDUCTION.md`
applies to this literal full star, after reflecting all coordinates if
necessary to reverse all moment signs. That complete theorem has no
distance premise, no intact-triangle premise and no degree-three
restriction. It contradicts the full original H force equation.

This proves h<=epsilon and completes the uniform theorem. In particular,
when d<=1, epsilon=0 contradicts h>0 from O in int(X).

## 5. Equivalent common central-root exclusion

If a root satisfying the graph and load hypotheses of Section 1 contains
closed D_epsilon in its open interior, then every unit-normal support of
X is strictly greater than epsilon. Its actual return support h therefore
violates the uniform theorem.

Hence these whole graph families require a root which fails that central
disk inclusion. The sharper statement is the original directional one:
when O is open in X, its actual X-to-H support, including every genuine
side mean and normal-owner endpoint, must belong to (0,epsilon]. The
weak endpoint h=epsilon is expressly retained.

## 6. A complete aligned endpoint lemma for a genuine triangle root

Assume a genuine S root X has exactly its two nonleaf positive neighbors
A,H, these two actual units physically touch, and A is physical boundary.
Their degrees, loads and additional forces are otherwise unrestricted.
If the real leaf axis is an own X axis, rotate it East. The full chart is

    X=[d-1,d] x [t-1,t],  0<=t<=1,
    L=[d,d+1] x [-1/2,1/2].

**Endpoint lemma.** Neither t=0 nor t=1 is possible, throughout the
full radius window, not just at d<1.

It suffices to reflect the whole configuration and prove t=1. Put a=d-1,
so X=[a,d] x [0,1]. The genuine leaf force is positive East and has zero
origin moment. Its two other forces keep their original positive
magnitudes and actual applications.

No nonleaf normal is East. The universal sharp support bound h<=d has
the equality case that any contained unit beyond x=d is exactly the
radial S unit L; it cannot be a distinct original neighbor.

No nonleaf normal is North or South either. Such a normal is an own
X axis, and the physical triangle X,A,H gives its nonnegative dot
product with the other X normal, by the owned-axis triangle theorem.
Dotting the full three-force X equation with that axis would give its
strictly positive own force term, a nonnegative other term and zero
leaf term. This is impossible.

If either nonleaf normal is West, full vertical balance makes the other
normal horizontal too, hence also West. Their original application
heights y_A,y_H belong to [0,1]. Their full origin-torque equation is

    beta*y_A+gamma*y_H=0,  beta,gamma>0,

so both are zero. The actual A application is (a,0), whose norm is
|d-1|<1/10<r. It cannot belong to the actual boundary unit A.

It remains that both nonleaf normals strictly expose X vertices, with
nonzero own components. Their vertical components have opposite signs
by full balance. If their horizontal signs differ as well, their actual
applications are opposite X vertices, and the physical opposite-vertex
triangle theorem excludes the required A--H contact. If both horizontal
components are positive, full horizontal balance with the East leaf is
impossible. They must therefore be a Northwest normal (-u,v) at (a,1)
and a Southwest normal (-s,-w) at (a,0), with u,v,s,w>0.

Writing their actual magnitudes beta,gamma, vertical balance is beta*v=
gamma*w. Their unchanged total origin moment is consequently

    beta*(a*v+u)-gamma*a*w=beta*u>0,

contradicting the actual X torque. This exhausts all own-axis, strict
vertex and shared-mean cases. The reflected t=0 endpoint follows.

## 7. Three literal original-family joins

The complete original graph and load cover gives the following exact
assignments. The letters in the middle columns are the generic roles
of Sections 1--6; the last column lists actual private transmitters.

| Existing original fine ID | X | A | H | Private graph G | Transmitters |
| --- | --- | --- | --- | --- | --- |
| M6.B5L.HOUSE.ROOF.LAC.S | T | A | D | A--B--C--D--A | B, between boundary A,C |
| M6.B5L.HOUSE.ROOF.LABC.S | T | A | D | A--B--C--D--A | None |
| M6.B5L.FAN.ENDPOINT.L234.S | 1 | 2 | J | Edges J2,J3,J4,23,34 | None |

Here J is the actual fan hub; its original path is 1--2--3--4 and its
original spokes are J1,J2,J3,J4. In each row the real X has exactly the
positive neighbors L,A,H. In the first two rows D remains true unloaded
degree three; A retains its true loaded degree three. In the third row
J remains true unloaded degree four and 2 remains true loaded degree
three. No fake two-force boundary equation or shortened hub equation is
used. The loaded C in the first row and the actual B transmitter retain
their respective full true degree-two equations.

All Section 1 hypotheses except the separately stated open-origin
condition hold literally. The actual A--H contact also holds: it is AD
in the roof rows and J2 in the fan row. Thus Section 6 applies to every
original aligned endpoint in all three rows.

### 7.1. Entire strict-low-radius exclusion, without angle certificates

Let d<1, equivalently R^2<17/4. In an aligned S-root chart the endpoint
lemma leaves 0<t<1. Since d-1<0<d, this puts O in int(X).

For a strictly tilted S root, use its original own coordinates

    X=[U-1,U] x [V-1,V],
    U>=V>0, U^2+V^2=d^2.

Both U and V are strictly less than one when d<1, so again O is open
in X. The uniform theorem now says 0<h<=epsilon=0, a contradiction.

Therefore the complete strict-low domain of each of the three original
families is excluded. Both own-frame limits and every transverse mean
endpoint have been included; no new radius subdivision is introduced
as an additional gate identifier.

### 7.2. Entire tilted critical-radius exclusion

At d=1 a strictly tilted root has 0<V<=U<1, hence O is open in X.
The same zero-epsilon contradiction applies. An aligned root at d=1
has O on its actual left side, so it is expressly outside this argument.
Its transverse endpoints are still excluded by Section 6.

### 7.3. The remaining high tilted root is uniformly shallow

Let d=1+epsilon>1 and use the tilted chart above. If U>=1, then
automatically U>=1-epsilon. If U<1, then O is in int(X) and the theorem
forces h<=epsilon. At least one own-face distance of X from O is then
at most epsilon: its support is a nonnegative linear combination of
two such distances with coefficient sum at least one.

The four distances are U,1-U,V,1-V. Only 1-U can be at most epsilon.
Indeed U>=d/sqrt(2)>1/2, while

    V^2=d^2-U^2>d^2-1=2*epsilon+epsilon^2>epsilon^2,
    V<=d/sqrt(2)<3/4,

and hence V>epsilon and 1-V>1/4>epsilon. We conclude

    1-epsilon<=U<=d,
    0<V<=2*sqrt(epsilon)<4/15.                         (3)

The upper V estimate follows by subtracting (1-epsilon)^2 from d^2;
2/sqrt(60)<4/15. All weak endpoints U=1-epsilon and h=epsilon remain.

Consequently the force-free theorem
`SHALLOW_TILTED_S_ROOT_BOUNDARY_NEIGHBORS_ONE_SIDE.md` applies to every
remaining tilted root in these three families. With the actual radial
transverse direction f=(-V,U)/d, every physical circle corner Z of its
actual boundary neighbor A satisfies f.Z<0. This is a retained necessary
condition, not a contradiction by itself. The other private boundary
units are not declared to lie on that same side.

The exact surviving domain in all three original rows is therefore:

* aligned roots with d>=1 and 0<t<1;
* strictly high-radius tilted roots with (3), retaining h<=epsilon
  whenever U<1.

No full original fine ID or coarse cell closes from this manuscript.
Its value is a single continuous proof that removes the same low and
nonshallow domains in three original families, including their arbitrary
three-square completions, without a numerical certificate.

## 8. Exact operative sources and remaining boundaries

| Source | SHA256 | Exact scope used |
| --- | --- | --- |
| RADIAL_BRIDGE_AND_LEAF_REDUCTION.md | faf453b3c519b10590cf9d6f6dbf9282233bd2ff04c90aa0cd8cd89e060bc676 | Actual S/D leaf and root geometry, real radial leaf force and zero leaf origin moment |
| GLOBAL_NEXT_DEGREE_FREE_MOMENT_PORT_ORDER_AND_INTACT_BLOCK_EXCLUSION.md | 8def789e0cde632795f81d8ecf92d6dd3642b37fd4ca6e79cc4890594264fd49 | Only Sections 1--3: actual support bound, degree-free moment order and strict directed-cycle winding outside D_epsilon |
| HOUSE_ROOF_AC_D_COMPLETE_MOMENT_EXCLUSION.md | db795b7a1a287d7e8e422bd80f3ea04e714d9d98af88226e9c16ad757b7e0f5a | Only Section 1.2: boundary/far-body port order with no neighboring-disk-avoidance requirement; its D-root caller is not imported |
| UNLOADED_OPPOSED_MOMENT_STAR_AND_LOWER_HOUSE_TDC_D_SMALL_SUPPORT_REDUCTION.md | 008acc8485e591b34604bf3e0b0cdcb03b7220aa249fc8e49552a065770ca129 | Only Section 1: complete arbitrary-degree inward opposed-moment star theorem, with no distance or intact-root premise |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Owned-axis physical triangle dot-product obstruction |
| END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md | 20a845eff8bee3e9c533162df0b32ea96f9dd104a3cfec41efb3b0cf92d6e9cf | Only Sections 1--2: sharp support equality and opposite-vertex physical triangle obstruction |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe | Common compatible physical embedding and protected boundary access, including weak-junction routing |
| FIVE_BODY_BLOCK_LEAF_GRAPH_LOAD_COVER.md | e5c84071363e8dc43b09f9033c7cb3a7684f1de19bcd169d53c9eab55d51963b | Literal three original graph/load families, actual hub/root degrees and original fine-ID meanings |
| SHALLOW_TILTED_S_ROOT_BOUNDARY_NEIGHBORS_ONE_SIDE.md | c8e399293ee684fa21a4d5028dc56ab9234007db2b7e1b3a35ad9e214efc45a3 | Only the final partial corner-sign corollary at the explicitly derived shallow high-radius chart |

The shallow-boundary source is used only for the final explicitly partial
corner-sign corollary after (3); the three-family radius and chart reduction
is complete before that invocation. The whole manuscript retains all nine
physical units, all selected normals, original side means and endpoints,
zero-weight physical contacts and circle masks. It neither changes original
checklists nor promotes a necessary subclass to a complete original family.
No Lean compilation, CI, sampled pose or computational exclusion certificate
is an input.
