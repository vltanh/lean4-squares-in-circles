# The full low aligned house hub-TDB S row is excluded at the canonical minimizer

Date: October 27, 2026.

**Status: complete original-domain proof, submitted for full independent
and root review.** It retains true A4/T2/D3/B2/C2, all nine physical
squares, and every original mean. The canonical choice is made before
normal selection and stress extraction. This is a lower-bound
counterexample exclusion, not a classification of all equality packings.

## 1. Entire original residual domain

Use the original house edges AT, DT, AD, AB, BC, CD and the genuine
S leaf AL. The exact positive block loads are T,D,B; C is the actual
unloaded degree-two transmitter. Keep the same nine unit squares,
every circle mask and individual zero weight, and all other actual
physical contacts. The complete source
`HOUSE_HUB_TDB_S_ROOT_COMPLETE_DOMAIN.md` gives the only remaining
S domain, after one reflection of the whole packing:

    2<R<sqrt(17)/2,
    d=sqrt(R²−1/4)−1, 14/15<d<1, a=1−d in(0,1/15),
    A=[−a,d] times[h−1,h], 29/50<h<2/3,
    L=[d,d+1] times[-1/2,1/2].                         (1)

Put g=1−h, so 1/3<g<21/50. The actual AB normal is South at

    P=(x,−g), 3/10<x<=d.

B is tilted and has exactly one physical circle corner. Its full
actual frame is

    B=P+[0,1]u+[0,1]v,
    u=(b,−t), v=(−t,−b), b,t>0, b²+t²=1,
    Z=P+u+v=(X,−Y),
    Y=g+b+t, X=x+b−t>3/4, X²+Y²=R².                 (2)

The actual D and T have all their physical circle corners strictly
above the horizontal axis. They retain their actual physical DT edge.
Their A normals keep the whole West/North/Northwest/Northeast cover.
No true-A3 slope relation is imposed. All four forces at A remain.

The incoming B-to-A force has outward normal North. B retains its
actual second force to C, its full positive unique-corner circle force,
and its original torque. No proper-concurrence theorem is required in
the following proof.

## 2. The original C4 subcycle has an empty unit hole

The four actual positive edges A--B--C--D--A form a physical cycle
in the original selected plane embedding. The extra T and its AT/DT
edges remain; no force on those edges is deleted.

The complete physical winding/area proof in Sections 1–2 of
`FOUR_CYCLE_LEAF_HOLE_EMPTY.md` applies to these four original ring
units. For clarity, for the four original consecutive application
chords of lengths ell_i<=sqrt(2), an entire additional unit in the
bounded face would force equality throughout

    area(hole)<=sum_i [ell_i²/4
                   −sqrt(max(ell_i²−1,0))/2]<=1.

Every chord then has length one, and the contact polygon is a unit
square. Each ring unit occupies the exterior side of one full edge,
giving the aligned four-neighbor cross. Coincident contacts instead
give zero winding or a triangle of area less than one, so cannot
hide an exception. The source's complete weak-junction winding
argument retains every original routing neighborhood.

Now only the true equations at C are needed. Its zero circle weight
and two positive forces make them opposite, with their actual
application displacement parallel to their direction. In the cross
that displacement is a whole unit-side vector. Both original
point-only contacts would therefore have axis normals, contradicting
the selected strict point-normal convention. Thus no other whole
unit can lie in this bounded face.

This imports exactly the physical Sections 1–3 of the old source.
Its later argument for three loaded degree-two ring bodies is not
used. D keeps degree three, A keeps degree four, and the region is
unavailable to every other actual square, including T and all three
completion squares.

## 3. An actual canonical AC contact, without a new positive force

Before making the compatible finite physical-normal choices and
extracting the original stress, choose a minimum-radius nine-square
packing minimizing the continuous quantity

    Phi=sum_(i=1)^9 |center_i|².

This choice exists by compactness of the labeled minimum-radius
packing space. It is the same admissible secondary minimizer as
Section 1 of `FOUR_CYCLE_SECONDARY_CONTACT_REDUCTION.md`.

The true B--C--D channel and actual unit bypass A fall under the
complete `UNIT_BYPASS_NORMAL_CHANNEL.md`. The original C is side-normal
with reserve one. If n is its B-to-D direction, the two actual channel
applications satisfy

    Q_CD=Q_BC+n.                                      (3)

The bypass and C are separated transversely, and the n projection
of A contains the entire unit n interval of C. Write m for the
transverse own axis pointing from C toward A. In m,n coordinates,

    C=[s−1,s] times[z,z+1],
    A subset {m-coordinate>=s+delta}, delta>=0,
    B subset {n-coordinate<=z},
    D subset {n-coordinate>=z+1}.

If delta>0, the whole open rectangle
(s,s+delta) times(z,z+1) is on the bounded side of the original
C4 center/contact loop. This is the complete slice/winding argument
in Sections 3–4 of the secondary-contact source: the B and D
strands are absent at intermediate heights, while each of the A
and C center/contact strands crosses each such height once.

Section 2 makes that rectangle empty of every other square's open
interior. Translating C a small positive distance in direction m
therefore preserves all nine nonoverlaps. The original A in (1)
contains O openly, so s+delta<0. C's center m coordinate is
s−1/2, and the translation strictly decreases both its maximum
corner radius and its contribution to Phi. This contradicts the
canonical choice. Consequently

    A intersect C is nonempty.                        (4)

No translation is actually made in the retained counterexample;
its supposed positive gap has been excluded. All original B/C/D
forces, applications, and physical masks are still the same. The
contact (4) need not carry a positive force.

## 4. The complete actual transverse and channel-axis cover

At C the opposite owned channel normals are −n and n. The two
physical triangles C-B-A and C-D-A, and the radius-free owned-axis
triangle theorem, force its actual normal toward A to be perpendicular
to n. Thus it is exactly the transverse own axis m. The actual
A-to-C normal is −m.

A owns its actual AB normal South. The physical A-B-C triangle
therefore gives m_y>=0. If m points West, −m is East at A; the
sharp contained-unit support equality at d would make C the real L,
impossible. If m points East, A and C are parallel with a vertical
channel. Both B forces would then be vertical, contradicting the
strictly positive x coordinate of its unique physical circle corner
in (2).

If m_y>0 and m_x<0, the A-to-C support is a strict Southeast
vertex contact at (d,−g). An actual inward normal segment of C
then enters the open real L, since −1/2<−g<0. This is impossible.
If m is North, the channel is horizontal and parallel A/C have
identical unit horizontal intervals by projection containment. C
is exactly [−a,d] times[−g−1,−g]. The actual B inward vector
v=(−t,−b) from (x,−g) immediately enters its interior, also at
x=d. This again contradicts physical nonoverlap.

The entire remaining actual frame is therefore

    m=(c,s), c,s>0, c²+s²=1.

The B-to-C normal is either (−s,c) or its negative. The complete
B2 x equation and its positive unique-corner circle force make
this normal's x component strictly negative. Hence

    n=(−s,c),                                       (5)
    P_0=(-a,−g)=A intersect C,
    max_(z in C) m·z=m·P_0.

The last intersection is the original A lower-left vertex on the
actual C side. The original B top vertex P cannot be its BC port:
m·(P−P_0)=c(x+a)>0, whereas every C point has m projection at
most m·P_0.

In the B frame (2), n·u=−sb−ct<0. Its entire maximum-n support
is consequently on B's u=0 side. The top endpoint P was excluded.
Thus the full unchanged BC feature cover is exactly:

* a strict vertex port R=P+v, with st>cb; or
* the owned side normal n=−u=(−b,t), with actual port
  R=P+tau v, 0<=tau<=1.

This includes both endpoint means of the owned case. No generic
selection or force-line concurrence has been used to shorten it.

## 5. The strict B-vertex return has an actual far channel port below −1/3

Keep outward B-to-A magnitude beta>0, B-to-C magnitude xi>0, and
unique-corner multiplier lambda>0, normalized so its circle force is
lambda Z. The full B2 equations are

    beta North+xi n+lambda Z=0,

together with the unchanged moment. Put k=b−t. In the strict
vertex case R=P+v, the x equation gives lambda=xi s/X. Taking
moments about the actual P gives

    tc+bs=(s/X)(xY−gX),
    c/s=[xt−k(g+b)]/(Xt).                            (6)

Every denominator is positive. The actual strict-vertex inequality
st>cb now gives

    0<Xt²−b[xt−k(g+b)]
       =k(1+bg−xt).

Since x<=d<1 and t<1, its last factor is strictly positive.
Thus b>t. Also st>cb between two first-quadrant unit pairs is
equivalent to c<t. The far original channel point (3) is

    Q=R+n=(x−t−s,−g−b+c).

Its actual height consequently satisfies

    Q_y<−g−b+t<−g<−1/3.                              (7)

All original strict normal limits remain covered by the separate
owned-side row below. No proper radial point, inside-unit assertion,
or deleted B force was used.

## 6. The entire actual owned-side return has the same low endpoint

Here n=−u=(−b,t), s=b,c=t, and R=P+tau v with the original
tau in[0,1]. The full x force gives lambda=xi b/X. The full
moment about P gives exactly

    tau=b(xY/X−g).                                   (8)

An exact rearrangement, using X=x+b−t, is

    tau−1=−(b−t)(1+bg−xt)/X.

Its positive last factor and tau<=1 imply b>=t, including b=t
and tau=1. The far actual channel point is

    Q=R+n=(x−tau t−b,−g−tau b+t).

The complete scalar theorem
`OWNED_SOUTH_BOUNDARY_CHANNEL_HEIGHT_BOUND.md` applies literally to
(2),(8), with R>2 and 1/3<g<21/50. It proves

    Q_y<−1/3.                                        (9)

This theorem retains the actual tau and uses two exact univariate
polynomial inequalities, with all 30 Bernstein coefficients supplied
and checked by its rational arithmetic file. It neither chooses a
new mean nor assumes the original tau is interior.

## 7. The actual D return supports are acute

The physical A-C-D triangle and (5) narrow the original AD cover
without using D's force equation. A-owned North AD would have
negative dot product with A-to-C=−m, contradicting the owned-axis
triangle theorem. A strict Northeast AD would expose the vertex
opposite the strict Southwest AC vertex; two touching neighbors
cannot occupy opposite strictly exposed vertices of a unit square.
This is the pure actual-feature statement in Section 2 of
`END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md`.

The remaining actual AD normal is West or strict Northwest. Its
unchanged D-to-A reverse normal has positive x and nonpositive y.
The actual D-to-C normal is −n=(s,−c), with s,c>0. Their dot
product is strictly positive. The actual AD application is

    P_D=(-a,y), y>29/50,                              (10)

by the original boundary annulus on A's left face. The original
DC application is exactly the Q in (7) or (9).

We use the following elementary complete supporting-feature fact:
two points of an actual unit square with supporting outward normals
of positive dot product have distance at most one. Two opposite
vertices have closed normal cones with nonpositive mutual dot
product; adjacent vertices are distance one. For two relative side
interiors, positive dot product forces the same face. For a vertex
and a relative side interior, a nonincident side's normal has
nonpositive dot product with every normal in the vertex cone; an
incident side is within distance one. Coincident points and axis
normals at vertices are included in those cases.

Applying this fact at D, to its two unchanged original supports,
gives

    |P_D−Q|<=1.                                      (11)

All D3 forces, including DT, remain. The statement (11) is physical
and does not replace D by a loaded degree-two tip.

## 8. No upper circle corner of the actual D can then exist

Equations (7),(9),(10) give

    y−Q_y>29/50+1/3=137/150>sqrt(3)/2.

Together with (11) this implies

    |Q_x+a|<1/2,  |Q_x|<1/2+1/15=17/30.             (12)

Every actual physical circle corner Z_D of D has positive height
by the original domain theorem, whereas Q_y<0. Thus
Q·Z_D<=R|Q_x|. The actual two points of the same unit would have

    |Z_D−Q|²>=(R−|Q_x|)²
                 >(43/30)²=2+49/900>2.

This contradicts its actual diameter sqrt(2). The argument uses all
physical circle corners, independently of their individual weights.

The contradiction covers both entire original BC feature rows,
every side mean, both channel-axis endpoint alternatives before
their physical exclusion, and the full canonical all-nine slide.
It excludes the entire low aligned house hub-TDB S row at the
admissible canonical counterexample, with no altered positive
degree or omitted force. No numerical pose, Lean compilation, CI,
workflow dispatch, shared metadata edit, or remote action is used.

## 9. Exact new dependencies and canonical scope

The new necessary-domain source is
`HOUSE_HUB_TDB_S_ROOT_COMPLETE_DOMAIN.md`, SHA-256
`f9461dd33f28e0419fd023583ecff96c95d7076b53d47b8cc6236ab9ab7c4dec`.
Its complete independent review is
`REVIEW_HOUSE_HUB_TDB_S_ROOT_DOMAIN_TRIANGLE_BRIDGES_2026_10_27.md`,
SHA-256 `6720c8c09e46051b1a6d6b4a631f16ebec111107f565d10172ff9cf4cb105d10`.

The new scalar source is
`OWNED_SOUTH_BOUNDARY_CHANNEL_HEIGHT_BOUND.md`, SHA-256
`550cb41f99ecb61408fa71272eb45dc9461cfa50aebf1cf2be4d7b533ddb5f7d`.
Its exact arithmetic file is
`certificates/house_tdb_owned_south_channel_height_check.py`, SHA-256
`589814e33139f431e222c9e8da16291fb3893998f27d6e64df6d2d9fb72bf005`.
Full independent review of this new scalar/caller chain is requested.

The readable old inputs are used only at their literal complete
physical scopes: the full unit bypass and transverse-separation
theorem; the C4 winding/area proof and true-unloaded2 equality exit;
the canonical secondary compactness, slice and inward-slide proof;
the radius-free owned-axis and opposite-vertex physical triangle
facts; and the sharp contained-unit support equality. None supplies
a shortened equation at A or D. The initial secondary choice is
valid for the lower-bound contradiction and is made before any
normal prelist or multiplier extraction.
