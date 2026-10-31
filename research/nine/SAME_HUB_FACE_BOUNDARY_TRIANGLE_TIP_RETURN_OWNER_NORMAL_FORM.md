# A common hub face forces the nonparallel boundary tip's return to be owned by its other neighbor

Date: October 28, 2026 UTC. Author: cycles continuation.

**Status: complete proposed uniform owner normal form and literal
D02.L01345 same-axis reduction, awaiting full root and independent
review. No original graph/load family is declared closed.**

Keep the same actual units, containing-circle origin, positive
forces, true degrees, physical masks, actual means, selected normals
and all completion squares throughout.

## 1. Exact setting and two additional complete local lemmas

Let U,V,W be contained pairwise interior-disjoint unit squares in
D_R, with R>2 and physical contacts UV,UW,VW. Both original normals
from U to V and W are the same actual side axis of U. Let V be
loaded with its complete positive neighborhood exactly U,W, and
let W physically touch the containing circle. Degrees and forces
at U,W are arbitrary.

The first result below is selection-free:

**Parallel-tip lemma.** If V's frame is parallel to U, then W's
frame must also be parallel to U.

The second result is also selection-free, assuming a free
vertex/vertex return at VW in its literal physical sense:

**Two-circle free-return lemma.** If V is nonparallel to U and
has two physical circle corners, VW cannot be a point-only
vertex/vertex contact.

Together with the complete V-owned exclusion and the existing
simultaneous fixed-tip normal selection, they give the following
normal form throughout the original upper-radius window:

**Selected owner normal form.** If V is nonparallel to U, then
the actual VW contact is a singleton owned by W, with its actual
V application a vertex and its actual W application in the
relative interior of a W side.

This is a reduction to an actual owner, not an assertion that the
remaining owner is impossible.

## 2. Complete parallel-tip proof

Rotate about O so the common U support is x=a, with U to its
left. Suppose V is parallel to U and W is not. The minimum-x
support of W is its unique left vertex. It cannot lie on the
left side of V: its inward tangent sector contains East openly,
and would overlap the inward half-plane or quadrant of V at
such a point.

Consequently that vertex is strictly above or below V's whole
left side. Reflect all data to put W below V. Write

    V=[a,a+1] times [b,b+1].

At V, its original UV normal is West. The physical triangle
side-axis theorem gives (n_VW)_x<=0. A strict leftward normal
would place the VW contact at a left V vertex, impossible by
the preceding tangent-sector argument. West itself would put
W entirely to the left of x=a, contrary to its positive width.
North is incompatible with W's minimum-x vertex lying below
V. Thus the complete original VW normal is South.

The actual top W vertex lies on V's lower side. Write its
actual axes from its leftmost vertex as (C,S),(S,-C), where

    C,S>0, C^2+S^2=1.

The unchanged actual points are

    P_W=(a,b-S),       M_VW=(a+C,b).                   (1)

The positive magnitudes of V's West and South forces are
mu,nu. Its full circle resultant is (mu,nu), both components
positive. Put

    X=a+1, Y=b+1.

Physical farthest-corner comparison gives

    X,Y>=1/2,
    (X,Y) is an actual circle corner,
    X^2+Y^2=R^2>4.                                   (2)

If Y=1/2, the W right vertex is

    (X-1+C+S,-1/2-C).

Its first coordinate is greater than X>0 and its second
has absolute value greater than 1/2. Its squared norm
therefore exceeds R^2, contradicting containment. Thus
Y>1/2.

If X>1/2, the actual circle mask of V is unique and
mu/nu=X/Y. If X=1/2, its full two-circle mask has
corners (-1/2,Y),(1/2,Y), so every permitted weighting
with mu>0 satisfies

    0<mu/nu<=X/Y.                                    (3)

Let P_V=(a,t) be the unchanged original UV side mean.
Its full possible interval on V is b<=t<=b+1. The
same actual U side contains both P_V and P_W, and
has length one. Therefore

    t<=Y-S.                                          (4)

The complete V torque gives

    mu*t=nu*(X-1+C).                                 (5)

Here t>0. If Y>1, then t>=Y-1>0. If Y<=1, (2)
gives X>sqrt(3)>1, so (5) gives t>0. These two
alternatives also include Y=1.

Using (3),(5) and then (4),

    Y*(X-1+C)/X<=t<=Y-S,
    k:=X/Y<=(1-C)/S<1,
    Y>sqrt(2).                                       (6)

All original UV means and either individual zero
circle weight were retained in deriving (6).

The top and left W vertices in (1) are shared with
other actual units and cannot be circle points. The
standard unshareability argument is geometric:
at a circle corner both inward side directions have
strictly negative dot product with that corner, so
two right-angle tangent sectors could not have
disjoint interiors in the same inward open half-plane.

For the right W vertex put

    x=C+S-1>0, H=1+C,
    C_W=(X+x,Y-H).

Its exact squared-radius deficit is

    R^2-|C_W|^2=2Y*(H-k*x)-(H^2+x^2).                 (7)

By k<=1, H-k*x>=H-x=2-S>0. Since sqrt(2)>7/5,
(6)--(7) give

    (7)>(14/5)*(2-S)-(H^2+x^2)
        =13/5-C^2-2CS-(4/5)S
        >=2/15>0.                                    (8)

The final uniform bound uses S<=1 and the exact identity

    5/3-C^2-2CS
       =(2/3)(C-(3/2)S)^2+(1/6)S^2>=0,

with C^2+S^2=1.

The last W vertex is

    D_W=(X-L,Y-H_2),
    L=1-S in [0,1],
    H_2=1+C+S in [2,1+sqrt(2)].

On the latter entire interval,

    2sqrt(2)H_2-H_2^2>=1,

by concavity and the endpoint values 4sqrt(2)-4>1
and 1. Since k,L>=0 and Y>sqrt(2),

    R^2-|D_W|^2
       =2Y*(H_2+kL)-(H_2^2+L^2)
       >1-L^2>=0.                                    (9)

All four W vertices are strictly inside D_R, contrary
to its actual physical circle contact. This proves
the parallel-tip lemma for every original mask and
mean, without a normal-selection premise.

## 3. Every free nonparallel return has the actual reflected geometry

Suppose V is nonparallel to U. Put the common U
support at x=a and its actual V contact at P=(a,t).
The same tangent-sector argument shows that the whole
minimum-x support of W lies strictly above or below P.
Reflect to put it below P. Write

    V=P+[0,1](c,-s)+[0,1](s,c),
    c,s>0, c^2+s^2=1.                                (10)

Assume VW is a point-only vertex/vertex contact.
W cannot be axis-parallel: all its vertex abscissas
would be a or a+1, while V's nonleft vertices have
abscissas a+c,a+s,a+c+s; the first two are strictly
between a and a+1 and the last is greater than a+1.
The left V vertex P cannot belong to W.

Thus W has a unique left vertex P_W below P, and
axes (C,S),(S,-C), C,S>0. The only possible free
contact is V's bottom vertex with W's top vertex.
Here is the complete vertex check.

V's rightmost vertex has x>a+1, so its only possible
W partner is W's rightmost vertex. Both inward
tangent sectors contain West openly, causing overlap.
V's upper vertex cannot meet W's left or right vertex
by their abscissas. It is above P while W's bottom
vertex is below P_W, so those two cannot coincide.
If it met W's top vertex, both inward sectors would
contain South openly, again causing overlap.

For V's bottom vertex, W's left or right vertices
are excluded by their abscissas. Equality with W's
bottom vertex would give two inward sectors openly
containing North. Thus only the stated bottom/top
pair remains.

Their equal abscissas give C=c and hence S=s.
Their equal heights then give

    P_W=(a,t-2s),
    2s<=1.                                           (11)

The inequality uses the actual common length-one
U side containing both P and P_W.

The entire actual W is the reflection of V in the
horizontal line y=t-s. V lies wholly above that
line and W wholly below it. Their common contact
vertex is the only vertex on the line.

Since both are contained and both touch the circle,
this reflection line must pass through O:

    t=s.                                             (12)

Indeed if t-s>0, every noncontact V vertex has
strictly larger squared norm than its reflected
W vertex, by the difference 4(t-s)*h, where h>0
is its height above the reflection line. All W
vertices except the common contact are then
strictly inside D_R; the common contact cannot
be a circle point either. This contradicts W's
boundary status. If t-s<0, the reversed comparison
contradicts V's boundary status. This proves (12)
using the whole physical circle masks, not their
force-weighted corners.

## 4. The entire two-circle mask is impossible in that free geometry

Use the actual V coordinates of (10), and write

    A=P dot (c,-s), B=P dot (s,c).
    t=-A*s+B*c.

Any actual outward normal at V's bottom vertex
has own components (alpha,-beta), with alpha,beta>=0
and alpha^2+beta^2=1.
The full V circle force is its West-force reaction
minus that free pair force. Its second own component
is therefore strictly positive. Hence B>=-1/2.

Suppose V has two physical circle corners. At radius
R>2 these are adjacent, and its center is on one own
axis. Put

    T=sqrt(R^2-1/4)>3/2.

If A=-1/2, the positive second circle-force component
requires B=T-1. Equations (11)--(12) give

    (T-1)c=s/2,
    0<s<=1/2, c>=sqrt(3)/2>1/2.

The left side exceeds 1/4 because T-1>1/2 and
c>1/2, whereas the right side is at most 1/4.
This is impossible.

If B=-1/2, the first-coordinate interval can have
outer endpoint T or -T. In the former case
A=T-1>0 and

    t=-A*s-c/2<0,

contrary to t=s>0. In the latter case A=-T,
so the actual UV point P=(A,-1/2) is itself a
physical circle corner. It cannot be shared with U.

These exhaust the actual two-circle mask. They do
not omit either individual zero circle weight.
This proves the entire two-circle free-return lemma.

## 5. Complete selected owner normal form

Now retain the common previously selected physical
certificate in the original radius window. Suppose
V is nonparallel to U.

Its actual UV application is the fixed unique V
minimum-x vertex. A free VW contact would also be
a fixed physical vertex, distinct from that UV
point by the tangent-sector observation. If V has
a unique physical circle corner, the full
GENERAL_FIXED_TIP_NORMAL_SELECTION.md theorem
excludes that free VW normal in the same common
certificate. Its distinct-fixed-point hypothesis
is satisfied, so the coincident radial-D exception
is not being suppressed.

If V has two physical circle corners, Sections
3--4 exclude the same physical free contact
directly. Thus every physical mask is covered.

The complete theorem
SAME_HUB_FACE_NONPARALLEL_BOUNDARY_TIP_CANNOT_OWN_RETURN.md
excludes every actual VW normal owned by V,
including positive-length shared contacts and
all endpoint-valued V side means.

The remaining actual normal must therefore be
owned by W. With V nonparallel, it cannot be
a positive-length shared contact. In the selected
strict point-contact convention it is a W-side-
interior/V-vertex singleton: a point-only
vertex/vertex contact instead has a normal in
both strict vertex cones and was already excluded.

No normal has been changed after the stress
certificate was obtained. Only the pre-existing
simultaneous fixed-tip selection is used, at its
literal physical-unique and fixed-point scope.

## 6. Exact original D02.L01345 consequence

For the original graph with rim 0,1,2,3,4,5, chord02
and load mask01345, set

    U=2, V=1, W=0.

The actual U3 and loaded V2/W3 degrees match the
local premises whenever UV and UW have the same
original U side-axis normal. The same-nine
analytic lower-radius theorem supplies R>2.

If V is parallel to U, Section 2 forces W parallel
as well. In the original strict certificate each
positive same-axis contact of parallel units then
has positive shared length: an isolated parallel-
frame vertex contact cannot carry a side-axis
endpoint of the strict vertex normal cone.
Both contacts lie on that same U side, so the
complete shared-return pocket-capacity theorem
excludes the entire resulting feature with all
three extras retained.

Therefore the entire original same-axis branch
can survive only in the selected owner normal form:

    V is nonparallel to U;
    UV is an actual U-owned singleton;
    VW is an actual W-owned singleton.

W may be parallel or nonparallel to U. The actual
UW contact, every W3 force and every original mean
remain. The true U3 and both remaining boundary
path bodies retain their complete equations.
This source gives no completion-capacity assertion
for that remaining owner form.

Thus no whole original load row, graph parent or
coarse cell is closed by this normal form alone.

## 7. Exact operative sources

| Source | SHA-256 | Operative input |
| --- | --- | --- |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Actual triangle normal sign at the parallel V |
| SAME_HUB_FACE_NONPARALLEL_BOUNDARY_TIP_CANNOT_OWN_RETURN.md | a7be3d8bdbe43ec5ff978ad4f5bf015f63a4688fc4788c26a8a97ea249a96983 | Entire all-mask nonparallel V-owned exclusion |
| GENERAL_FIXED_TIP_NORMAL_SELECTION.md | ef8ae8a219af9fa15a70698e485bbb337925e5caf2cd64b6b5c2619d9c4bd194 | Existing simultaneous selection only for the physical-unique, two-distinct-fixed-point free case |
| SAME_FACE_SHARED_TRIANGLE_BOUNDARY_PATH_POCKET_CAPACITY_ONE.md | 075684b4e0e38905ab5318e107fd9f6656f3aa5b810de87faa76bb3cce56311d | Literal whole both-parallel shared feature in the D02 caller |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Original chord, load mask and true degrees |
| LOWER_WINDOW_FROM_NINE_ANALYTIC_MEASURE.md | 3b3f40af8f62beee8a55b8d4c8d26398097362d88e91d32116885b4ceea96e90 | Same-nine analytic R>2 entry for the literal original caller |

No normal, mean, corner mask or force is selected
anew in these proofs. No numerical pose, angle
mesh, computational exclusion certificate, Lean
compilation, CI, ledger edit, commit or remote
action is part of this manuscript.

