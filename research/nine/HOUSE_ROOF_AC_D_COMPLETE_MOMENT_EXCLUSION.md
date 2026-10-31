# The complete roof-AC D house is excluded by its actual transmitter and moment order

Date: October 28, 2026. Author: six_body.

**Status: new complete original-family hand proof, frozen for root and
separate independent review. No original gate is changed before acceptance.**
This source extends the preceding two-family moment argument to the one
additional true unloaded degree-two body. It explicitly proves the weaker
physical port-order statement needed at that body's neighbors. It never
assumes that the unloaded transmitter avoids the epsilon disk or is
physically circle-clear.

Keep all nine original closed unit squares, with disjoint open interiors,
the unchanged circle and the common compatible selected certificate in

    79/40 <= R <= sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1, epsilon=max(d-1,0),
    r=R-sqrt(2), s=1-r.

The exact original positive house edges and genuine leaf are

    AT, DT, AD, AB, BC, CD, TL,

with L a genuine D leaf at roof T and exact positive block load set
`A,C`. In particular the true degrees are

    T3, D3, A3, B2, C2, L1.

T and D and B have zero total circle force. T is physically clear by
its genuine D-leaf geometry. No physical-clearance conclusion is imposed
on D or B merely from their zero circle multipliers. A,C and L are
physical boundary units. All three arbitrary completing squares stay
present, as do all actual circle corners, individual zero weights,
additional physical contacts, original positive forces, normals and
shared-side application means.

**Theorem.** This entire existing original fine family is impossible:

    M6.B5L.HOUSE.ROOF.LAC.D.

## 1. Full-window geometric facts and a far-body port theorem

The unchanged full-window bounds are

    9/10<d<61/60, 0<=epsilon<1/60,
    11/20<r<2/3, s>1/3,
    r^2-s^2>1/10.

Every actual contained unit V satisfies

    |c_V|<=d+1/2<91/60.

Every actual unit-normal contact support `n.x>=h` at that neighbor
has `h<=d`, because its normal half-width is at least 1/2.
Every actual point of a physical boundary unit has norm at least r.
These are purely geometric facts, including zero-weight circle corners.

### 1.1. A complete contained-neighbor cap

No actual unit neighbor beyond a support at p can satisfy

    h=p.n>1 and |p|^2>=2.                              (1)

Indeed `h<=d<61/60`. The actual neighbor center has
`c.n>=h+1/2>3/2` and norm less than `91/60`. Therefore

    |p.Jn|>sqrt(3479)/60,
    |c.Jn|<sqrt(181)/60,
    |p-c|>(sqrt(3479)-sqrt(181))/60
           >(58-14)/60=11/15>1/sqrt(2).

The last inequality contradicts p belonging to the actual unit neighbor.
The calculation covers every support owner and original side mean. It
uses no disk-avoidance or degree assumption at that neighbor.

### 1.2. Exact far-body port statement

Let U be any actual contained unit with

    dist(O,U)>sqrt(2)*epsilon.                         (2)

Let its two original actual contact applications and outward normals be
`p_-,n_-` and `p_+,n_+`, with

    det(p_-,n_-)<0<det(p_+,n_+).                      (3)

Their actual neighbors may have arbitrary degrees and may meet
`D_epsilon`; only their actual containment and support are required.

**Far-body port theorem.** On the angular branch of the origin-free
convex U, the counterclockwise angular change from `p_-` to `p_+`
is nonnegative.

Here is the complete physical feature proof. Rotations preserve the
statement. Reflection reverses both determinant signs and angular
orientation, so interchange the two port labels after a reflection.
These coordinate choices do not restrict the original normal intervals.

Because of (2), at least one missing own interval has distance more
than epsilon from zero. There are exactly the following two types.

**The other own interval contains zero.** Write

    U=[a,a+1] x [b,c], c=b+1,
    a>epsilon, b<=0<=c.

The right-side axis is impossible because its support is
`a+1>1+epsilon>=d`. At the upper-right vertex a negative-moment
normal `(u,v)`, `u,v>0`, would give

    (a+1)v<c*u,
    h_U(u,v)=(a+1)u+c*v>(a+1)/u>=a+1>d,

which no actual neighbor can satisfy. Its axis endpoints are the
already excluded right side or the positive-moment top side.
Reflection gives the complete lower-right counterpart: there is no
positive-moment port there.

The top side and upper-left cone have nonnegative moment, strictly
positive when (3) applies; the bottom side and lower-left cone have
nonpositive moment, strictly negative when (3) applies. A left-side
normal has moment equal to its actual y-coordinate. Consequently
every negative port has `y<=0`, while every positive port has
`y>=0`. All actual x-coordinates are positive. Their angular order
is therefore the claimed one, for every original mean and vertex
endpoint.

**Both own intervals miss zero.** Reflect their signs and exchange
axes so

    U=[a,a+1] x [b,b+1], a>=b>0.

By (2), `a>epsilon`. The right-side axis is again impossible.
No actual contact at all is possible at the far corner `(a+1,b+1)`:
every outward normal there has nonnegative components, so its support
is greater than one and its squared point radius is greater than two.
The complete cap (1) excludes its entire normal cone, including both
axis endpoints.

Put `theta_0=arg(a,b)`. The bottom side and lower-right cone have
negative moment, with angular coordinates at most `theta_0`. The
left side, top side and upper-left cone have positive moment, with
angular coordinates at least `theta_0`. For the top side the exact
comparison is

    (b+1)/(a+1) >= b/a,

which follows from `a>=b`. The only remaining feature is the near
vertex `(a,b)`, whose normal cone can have either sign but whose
angular coordinate is exactly `theta_0`. Thus the claimed order
holds also in this whole case.

These two cases exhaust (2); the near-corner alternative with both
missing intervals at distance at most epsilon is excluded by (2)
itself. At no step was a neighboring unit required to avoid
`D_epsilon`. In particular the result applies with the actual B2
transmitter as one of the neighboring units. The proof uses no force
equation at U and retains its complete true degree.

## 2. The common neighbor D is far, and its return support is strictly inward

Apply the complete full-window common-neighbor quarter-disk theorem
to the actual triangle T,A,D, with genuine D leaf L at T, page A
and common neighbor D. T has exactly its real three forces to L,A,D,
and the actual AD edge is positive. The theorem gives

    D is disjoint from closed D_(1/4).                 (4)

It uses neither the load nor the degree of B, so its premise is
unchanged in the present AC family. Compactness gives
`dist(O,D)>1/4>sqrt(2)*epsilon`. The physical boundary units A,C
also satisfy (2), since their point norms are at least `r>11/20`.

Let n be the original T-to-D normal. The entire local T3 calculation
gives

    h_T(n)>epsilon,
    h_D(-n)=-h_T(n)<-epsilon.                          (5)

For clarity, its exact local scope is as follows. In the genuine chart

    T=[-s,r] x [-b,a], a,b>0, a+b=1,

if both vertical margins exceed epsilon, every unit-normal support
already does. Otherwise reflect the entire original configuration to
make `a<=epsilon<1/4`. The full-window shallow-D kernel gives the
actual page normal `m_y<=0`. The full equation

    alpha*East+gamma*n+beta*m=0

and physical triangle axis/opposite-vertex cover leave either two West
triangle normals, where `h_T(n)=s>epsilon`, or

    n=(-c,t), m=(-u,-v), c,t,u,v>0,
    p_TD=(-s,a), p_TA=(-s,-b),
    gamma*t=beta*v,
    gamma*a*c=beta*b*u.

The last two equalities are T's full original force and torque
equations, including its genuine radial leaf's zero origin moment.
The actual D--A contact and physical support spans give `c+u>=1`.
If `c<=1/2`, then `t>3/4` and

    u<=a*c/(b*t)<=c/(3*t)<2/9,

contradicting `c+u>=1`. Hence `c>1/2` and
`h_T(n)=s*c+a*t>1/6>epsilon`. This proves (5) for the entire
original slider. It uses no hypothesis about another private body's
circle status or epsilon clearance.

## 3. B's actual two forces give its entire normal chord

The original B has exactly its positive AB and BC pair forces and
zero total circle load. Let `p_A,p_C` be their original actual
application means on B. The complete B force equation gives equal
magnitudes and opposite outward unit normals. Write the B-to-C normal
as e, so the B-to-A normal is `-e`.

Its unchanged full torque equation then gives

    det(p_C-p_A,e)=0.

The two points are the actual maximum-e and minimum-e supports of B.
Their projection difference is the actual square width `w_B(e)>=1`.
Consequently the exact original application relation is

    p_C-p_A=w*e, w=w_B(e)>=1.                          (6)

The entire chord `[p_A,p_C]` lies in B. Every actual shared-side
application, including its two endpoint values, remains. No midpoint,
new mean, parallel endpoint frame or circle mask has been selected.
This argument needs only width at least one; it does not restrict w
to an assumed side or diagonal channel alternative.

The actual T contains O openly, so no other actual closed square,
including B, contains O. Thus B is origin-free, with strictly positive
distance from O for each actual configuration. This assertion is weaker
than avoidance of `D_epsilon`; that stronger assertion is not used.

### 3.1. Neither original transmitter edge has zero origin moment

If either of B's two original edge moments were zero, (6) would make
both zero and would put both original applications on one line through
O. Because `[p_A,p_C]` lies in origin-free B, the two radial coordinates
are nonzero with the same sign. Orient that radial direction outward.
The nearer application belongs to an actual physical boundary unit
A or C, so its radius is at least r. By (6), the farther application's
radius is at least

    r+w>=r+1>31/20>d.                                (7)

The farther endpoint's actual boundary neighbor lies beyond precisely
that radial support. The contained-neighbor bound requires its support
height to be at most d, contradicting (7). This proves that the actual
AB and BC moments are nonzero without a clearance or load assumption
at B beyond its original zero circle total.

### 3.2. A directed positive-moment passage through B turns strictly forward

Suppose the actual directed passage is A--B--C, with positive original
directed moments. The incoming A-to-B normal and the outgoing B-to-C
normal are both exactly e. Along the real chord

    z(t)=p_A+t*e, 0<=t<=w,

the derivative of the angular argument is

    d(arg z(t))/dt = det(z(t),e)/|z(t)|^2
                   = det(p_A,e)/|z(t)|^2 > 0.         (8)

The positive sign is the actual directed edge moment divided by its
positive magnitude. The chord avoids O because it lies in origin-free
B. Thus its complete angular contribution is strictly positive.
The reversed directed passage has the identical conclusion with its
original normal and moment. This is a true two-force argument at B2,
not at A3,D3 or the loaded C2.

## 4. Every private edge is nonradial, and its orientation has no directed cycle

After deleting the actual T,L, the exact private positive graph is

    A--B--C--D--A.                                   (9)

The original AD and DC edges have both endpoint bodies outside closed
`D_epsilon`, by (4) and the boundary status of A,C. Their original
moments cannot vanish. Here is the precise geometric check. A zero-
moment edge at `p=t f`, `t>0`, would have inner unit U and outer
unit V with opposite radial supports at p, and the actual neighbor
bound gives `t<=d`. A missing own interval `[a,a+1]` of origin-free
U contributes coordinate `a+1` at p, giving `t>1` and
`a<=t-1<=epsilon`. If both intervals miss zero, `t>sqrt(2)>d`.
Otherwise the actual point `(a,0)` lies in U and `D_epsilon`, a
contradiction. This includes original side means and every owner.

The AB and BC moments are nonzero by Section 3.1. Thus orient each
of the four original private edges in its positive-moment direction.
If this orientation had a directed cycle, it would be exactly the
whole C4 in (9); there is no original positive private chord.

At each of the actual A,C,D bodies, the incoming original outward
normal has negative moment and the outgoing one has positive moment.
All three units satisfy the far-body hypothesis (2). Section 1.2
therefore gives a nonnegative angular contribution through each body,
without requiring its B neighbor to avoid `D_epsilon`. At the true
B2 transmitter, Section 3.2 gives a strictly positive contribution.

Replace the center-to-application strands inside each actual convex
unit by its straight application chord. Every private unit avoids O:
this is explicit for A,C,D and follows from T's open origin for B.
These homotopies avoid O. The total angular increment of the closed
contact loop is an integer multiple of `2*pi`; the preceding four
contributions make it strictly positive. Its winding about O is
therefore positive.

Use the one original compatible physical plane embedding, choosing
all routing neighborhoods within the positive O clearance of the
four actual units. Its C4 is a Jordan curve with the same winding.
The actual T contains O openly, so its center lies inside that curve:
the compact segment from O to the center lies in `int(T)` and has
positive clearance from every private unit. The real positive T--L
edge is disjoint from the C4 in the same embedding, so L also lies
inside. This contradicts L's protected physical boundary access.

No new physical edge or circle-resultant path was introduced. Extra
zero-stress contacts are kept in the same physical embedding. The
private positive orientation is consequently acyclic.

## 5. The original full D3 star is forced into the excluded moment pattern

The connected private C4 with an acyclic orientation has a distinct
source and sink. The actual B and C have no positive edge to T or L.
Their complete origin-torque equations involve just their original two
private pair moments, since every circle moment is zero. Neither can
be a source or sink while its two actual moments are nonzero. This
argument uses the true B2 and loaded C2 stars; it does not declare C
unloaded or remove its positive circle force.

The source and sink are therefore exactly A and D, in one order.
At D the original moments on DA and DC have the same strict sign.
Its full torque equation makes its actual DT moment strictly nonzero
with the opposite sign. D has its true degree-three unloaded force
equation with all three original magnitudes and applications present.

The complete geometric unloaded-star theorem of
`D_LEAF_ONE_CLEAR_COMMON_NEIGHBOR_BOUNDARY_REMAINDER_EXCLUSION.md`,
Section 2, applies under exactly these independently verified premises:

* `dist(O,D)>1/4>sqrt(2)*epsilon`, by (4).
* Its actual exceptional D-to-T support is less than `-epsilon`, by (5).
* That exceptional original moment has the opposite strict sign to
  every other original D moment, by the actual source/sink conclusion.
* Its full original circle total is zero, and every actual neighbor is
  contained in the unchanged disk.

Reflect the entire coordinates if needed to put the exceptional
moment positive. The theorem excludes this complete actual star.
It assumes no intact triangle and no central-disk containment at T.
This contradiction proves the whole original roof-AC D family.

## 6. Original scope, dependencies and exact credit

The original force and graph domain is the complete roof-AC line of
`FIVE_BODY_BLOCK_LEAF_GRAPH_LOAD_COVER.md`. Its root-preserving reflection
is covered by reflecting all original units, forces and means together.
All original radius endpoints, actual transverse sliders, physical
boundary masks, individual zero circle weights and three additional
packing squares remain. A zero total circle load was never used to
infer physical circle-clearance at B or D.

| Source | SHA256 | Operative scope |
| --- | --- | --- |
| `D_LEAF_ONE_CLEAR_COMMON_NEIGHBOR_BOUNDARY_REMAINDER_EXCLUSION.md` | `4e4e6e09bcb61f8e9a4de8cc75341b99914136369f807936c0351c1aff8f85b5` | Only Section 2's explicit geometric full unloaded-star theorem; its otherwise-boundary whole-component hypothesis is not imported |
| `D_LEAF_COMMON_TRIANGLE_NEIGHBOR_FULL_WINDOW_QUARTER_DISK.md` | `c39605b955d98f7fbe8499cf0a06dc4cc780a7dada4ee83c05ffc627f6d866bc` | Full one-page T3 conclusion, actual support spans and unchanged quarter-disk avoidance of D |
| `D_LEAF_SHALLOW_SIDE_BOUNDARY_FULL_WINDOW_EXCLUSION.md` | `ca7c3f4b32e45fc0c118bd766f438fce3019b0b44220604e33bc842a504ac670` | Full-window force-free shallow-page conclusion and root margins |
| `RADIAL_BRIDGE_AND_LEAF_REDUCTION.md` | `faf453b3c519b10590cf9d6f6dbf9282233bd2ff04c90aa0cd8cd89e060bc676` | Original genuine D root and leaf charts, open origin containment and physical root clearance |
| `UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md` | `b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207` | Full physical owned-axis triangle implications in the T3 return calculation |
| `END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md` | `20a845eff8bee3e9c533162df0b32ea96f9dd104a3cfec41efb3b0cf92d6e9cf` | Only Section 2's physical opposite-vertex fact in that same complete T3 cover |
| `PHYSICAL_BODY_GRAPH_UNCROSSING.md` | `bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe` | One common compatible embedding, weak junction routing and protected physical boundary access |
| `FIVE_BODY_BLOCK_LEAF_GRAPH_LOAD_COVER.md` | `e5c84071363e8dc43b09f9033c7cb3a7684f1de19bcd169d53c9eab55d51963b` | Entire original house roof-AC graph, loads and true degrees |

The weaker far-body port theorem and its complete physical cap are
proved here. They are consistent with the far-interval cases of
`GLOBAL_NEXT_DEGREE_FREE_MOMENT_PORT_ORDER_AND_INTACT_BLOCK_EXCLUSION.md`,
but its stronger requirement on both neighbors' epsilon clearance is
not silently invoked at A or C. The true B2 normal chord, its zero-
moment exclusion and strict angular increment are all proved directly.

The intended new credit after full acceptance is exactly the existing
fine ID `M6.B5L.HOUSE.ROOF.LAC.D`. The S alternative, other house
roots, inner fan and entire C1.5.b1 coarse cell remain separate.
The previously checked roof-AB D family is not recounted. No original
ID, force, degree, mean, normal, circle mask, physical square, shared
ledger or remote object is changed. No radius-two theorem, n=8 import,
Lean compilation, CI, numerical pose or scalar certificate is a premise.
