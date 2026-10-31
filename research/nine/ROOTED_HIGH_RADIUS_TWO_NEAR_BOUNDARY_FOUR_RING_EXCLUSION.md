# Two near-origin units cannot be opposite a boundary pair in a selected four-ring at high radius

Date: October 27, 2026.

**Status: complete fresh geometric theorem and complete original
same-role diamond/opposite-private-leaf C4 callers, frozen for full
root and separate independent review.** The historical high-radius
two-near source at prefix 5f73169d is absent from the current workspace.
This is a new complete reconstruction at a new pin, not a claim of
byte recovery or inherited acceptance.

Keep all actual contained unit squares with disjoint open interiors
in the circle about O, with

    sqrt(17)/2<R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1=1+epsilon,
    0<epsilon<1/60.                                    (1)

A physical boundary square touches the circle, whether or not each
individual corner multiplier is positive. No force equation is used
in the geometric kernel.

## 1. A complete half-lens estimate for two actual near centers

Put q=29/40. Let E,F be distinct actual units whose centers satisfy

    |c_E|<=q, |c_F|<=q.

Their centers are at least one apart, since their open radius-1/2
incircles are disjoint. Choose orthonormal coordinates, exchanging
E,F and reflecting the transverse direction as needed, so

    c_E=(m-a,b), c_F=(m+a,b),
    a>=1/2, m>=0, b>=0,
    (m+a)^2+b^2<=q^2.                                (2)

In particular a<=q and 0<=b<=sqrt(q^2-a^2).

Suppose an actual unit J touches both E and F. Its center C is
within sqrt(2) of both c_E,c_F. If C is on the origin side of their
line, namely C_y<=b, write

    C=(m+t,b-s), s>=0.

The two contact-distance bounds give

    (a+|t|)^2+s^2<=2.                                (3)

We prove the entire-domain estimate

    |C|^2<=2881/1600<(27/20)^2.                       (4)

Set z=a+|t|, so a<=z<=sqrt(2). Since m>=0,

    |C|^2
      <=(m+z-a)^2+(b-s)^2,
      0<=s<=sqrt(2-z^2).                             (5)

For fixed z the last expression is convex in s, so its maximum
occurs at s=0 or s=sqrt(2-z^2).

At s=0 it is increasing in z, so its maximum is

    F_2=(m+sqrt(2)-a)^2+b^2.                         (6)

At the other endpoint the full expression is

    2+(m-a)^2+b^2+2(m-a)z-2b sqrt(2-z^2).

It is convex on the whole closed z interval. For b=0 it is affine;
for b>0 the negative square-root term is convex, including its
continuous endpoint at sqrt(2). Its maximum is therefore again
at an endpoint. At z=sqrt(2) it is F_2, and at z=a it is

    F_1=m^2+(b-sqrt(2-a^2))^2.                       (7)

Thus every point in the closed half-lens (3), with every endpoint
included, has squared norm at most max(F_1,F_2).

### 1.1. Both full F_1 endpoint ranges

From (2), m<=sqrt(q^2-b^2)-a, with both sides nonnegative.
Equation (7) gives

    F_1<=2+q^2-2a sqrt(q^2-b^2)-2b sqrt(2-a^2).

For fixed a the right side is convex in
b in [0,sqrt(q^2-a^2)]. Its two endpoint values are

    2+q^2-2aq <= 2+q^2-q,

and

    [sqrt(2-a^2)-sqrt(q^2-a^2)]^2 <= 2-q^2.           (8)

For the last inequality, rationalize the difference of the square
roots: it is (2-q^2) divided by
sqrt(2-a^2)+sqrt(q^2-a^2), whose denominator is at least
sqrt(2-q^2). This also includes a=q and b=0.

Since q>1/2, 2-q^2<2+q^2-q. Thus the complete F_1 bound is

    F_1<=2+q^2-q=2881/1600.                          (9)

### 1.2. Both full F_2 ranges, including a>1/sqrt(2)

Use b^2<=q^2-(m+a)^2 in (6):

    F_2<=q^2+2-2sqrt(2)a+2m(sqrt(2)-2a).

If a<=1/sqrt(2), the coefficient of m is nonnegative, and
m<=q-a gives

    F_2<=(q+sqrt(2)-2a)^2
        <=(q+sqrt(2)-1)^2
        <(137/120)^2
        <2881/1600.                                  (10)

Here sqrt(2)<17/12, and the last exact reserve is 179/360.

If a>=1/sqrt(2), the coefficient of m is nonpositive. Thus

    F_2<=q^2+2-2sqrt(2)a<=q^2<2881/1600.              (11)

The equality threshold a=1/sqrt(2) is included in both valid bounds.
Equations (9)--(11) prove (4), since

    (27/20)^2-2881/1600=7/320>0.

### 1.3. Physical boundary consequence

Every physical boundary center has norm at least R-1/sqrt(2).
In the strict radius interval (1),

    R>103/50, 1/sqrt(2)<71/100,
    |c_J|>27/20.                                     (12)

It follows from (4) that no physical boundary common neighbor of
E,F can have center on the closed half-plane C_y<=b. All physical
boundary common neighbors therefore lie strictly on the same side
of the line c_E c_F, namely its side away from O.

If b=0, either choice of transverse direction is allowed in (2).
Applying the same proved bound to both choices excludes every
physical boundary common neighbor in that case. No E-F contact,
orientation, force or degree premise was used.

## 2. The exact selected-center order of a physical four-ring

We prove the needed center-order assertion directly, including its
weak endpoint. This avoids citing missing historical straight-center
or convexity files.

Every two distinct actual centers are at distance at least one.
Every contacting pair has center distance at most sqrt(2).

### 2.1. Selected positive center edges do not cross

Suppose two nonincident actual positive center segments AB and CD
cross in their relative interiors. Their four endpoints are in
convex order A,C,B,D. Each of those four interior angles is at most
90 degrees: for example at C the two adjacent distances CA,CB are
at least one, and the opposite diagonal AB has length at most
sqrt(2), so the cosine law gives cos(angle ACB)>=0. The same
argument uses CD at A and B and AB at D.

The four interior angles sum to 360 degrees, so all are exactly
90 degrees. The quadrilateral is a rectangle with side lengths at
least one and diagonals at most sqrt(2). Hence all four sides are
exactly one and both diagonals are sqrt(2).

If actual unit centers are distance one apart, their open incircles
are tangent and separation forces both support half-widths in that
direction to equal 1/2. Thus both squares have that direction as
an own side axis. Applying this to the four adjacent center pairs
makes the actual four units the aligned 2-by-2 block. Its two
crossing center edges are precisely its two opposite-sector point
contacts at the common four-square junction.

PHYSICAL_BODY_GRAPH_UNCROSSING.md Sections 1--4 guarantee that the
one selected positive graph never contains both such opposite
junction pairs. The global atom/body class preserves this
compatibility. Thus the alleged crossing is impossible.

Nor can a nonincident center lie on a positive center segment:
the two subsegments to it would each have length at least one,
whereas the whole contact edge has length at most sqrt(2).
Collinear overlaps likewise force such an endpoint and are impossible.
Consequently the selected center segments form a straight plane
drawing for the four-cycle considered below.

No force or normal is changed in this argument. It is a consequence
of the existing selected opposite-pair compatibility.

### 2.2. The only weak-convexity endpoint is the exact T configuration

Consider an actual positive four-cycle A-B-C-D-A. Suppose c_C were
strictly inside the triangle of the other three centers. In the
triangles A-C-B and A-C-D, the distances AB,AD are at most sqrt(2)
and the other two sides at least one. Therefore both angles ACB
and ACD are at most 90 degrees.

Thus c_B and c_D lie in the closed half-plane through c_C directed
toward c_A. The point c_A is strictly in that half-plane. The
triangle of A,B,D cannot contain c_C in its interior, a contradiction.
The same argument applies at every cycle vertex.

If a center lies on the segment joining a contact pair, their distance
would be at least two, already impossible. The only possible collinear
triple is therefore, after relabeling, C between its two cycle
neighbors B,D. The preceding two cosine-law inequalities must then
both be equalities: their two directions are opposite and each has
nonnegative projection toward A. It follows that

    |AC|=|BC|=|CD|=1,
    AC perpendicular BD,
    |AB|=|AD|=sqrt(2).                                (13)

This is the complete aligned T endpoint. Apart from it the four
centers are strictly convex, and Section 2.1 makes their selected
cycle order the actual convex boundary order.

It follows in particular that if two opposite cycle units E,F satisfy

    |c_E-c_F|<2,                                     (14)

then the other two centers are strictly on opposite sides of the
line c_E c_F. In the strictly convex case these are the two sides
of a diagonal. In (13), the opposite pair B,D has distance two and
cannot be E,F; for the other opposite pair A,C, the centers B,D
are strictly on opposite sides of AC. All weak cases are therefore
included.

## 3. Complete geometric four-ring exclusion

Suppose the selected positive graph contains the actual four-ring

    E-B-F-C-E,

where E,F are distinct actual units meeting the closed epsilon disk,
and B,C are physically circle-touching. Their true degrees and every
other force are arbitrary.

Their near-center bounds are

    |c_E|,|c_F|
      <=epsilon+1/sqrt(2)
      <1/60+17/24=29/40=q.                            (15)

Thus |c_E-c_F|<2q<2, and Section 2 makes c_B,c_C strictly opposite
across their line. Both are actual common-neighbor centers, so
Section 1 puts them strictly on the same side of that line, or
excludes both when it passes through O. This is a contradiction.

**Geometric theorem.** The entire displayed four-ring is impossible
at (1), with every actual orientation, contact feature and weak
selected junction retained. E and F need not physically touch.
There is no degree, load, circle-weight or force-equilibrium premise
at those two near units or at B,C beyond the stated physical
boundary status of B,C.

## 4. Complete original same-role decorated-diamond callers

Retain a genuine terminal Q0 and a distinct diamond Q1 with one
genuine leaf L at a private vertex X. The original one-private-leaf
origin theorem
ROOTED_GENUINE_FOUR_BLOCK_LEAF_DIAMOND_OPEN_ORIGIN.md gives their
unique shared H with O in int H. Its disjoint layout is already
excluded. All four ordered root/leaf roles and original private
degrees remain in that theorem.

Because X avoids O, the genuine-leaf theorem
ROOTED_ORIGIN_FREE_RADIAL_CONTACT_EXCLUSIONS.md Section 3 gives
a real S leaf with d>1, the high radius (1), and X meeting closed
D_epsilon. H itself contains O and therefore meets that disk too.

Suppose first H and X are both diamond hubs. Each of the two other
private tips has true positive degree two. It cannot be unloaded,
because a positive-width unloaded transmitter separates its two
neighbors, whereas the actual H-X diamond edge makes those two
neighbors touch. Both private tips are therefore physical boundary.
The four actual outer-ring edges are precisely the graph in Section 3,
with the near units H,X opposite. Their additional real central HX
force is retained and not used as a degree-two substitute.

Suppose instead H and X are both diamond tips. The two private hubs
have true positive degree three and no external pair. The complete
NO_UNLOADED_DIAMOND_HUB.md makes both loaded, keeping all three
original forces at each. They are again two physical boundary common
neighbors of H,X, and the same actual selected outer ring contradicts
Section 3. No nonexistent HX contact is assumed in this role.

Thus both entire same-role diamond allocations are impossible.
The two mixed hub/tip allocations remain separate and retain their
own full original force systems.

## 5. Complete original opposite-private-leaf C4 caller

Retain a genuine terminal Q0 and a distinct privately decorated C4

    H-U-X-V-H, XL,

where X has its real genuine leaf and true degree three, and U,V
retain their true degree two. The complete current theorem
ROOTED_GENUINE_FOUR_BLOCK_LEAF_C4_OPEN_ORIGIN.md gives the unique
shared open-origin H, excluding its disjoint layout. As in Section 4,
H and X both meet closed D_epsilon and the radius satisfies (1).

If either U or V were unloaded, its full genuine two-force channel
separates H and X by its actual positive projected width W>=1.
Their center projections in that channel direction then differ by
at least

    W+halfwidth_H+halfwidth_X>=2.

This contradicts their actual center distance <2q<2 from (15).
This uses the real unloaded body and its unchanged two force lines;
no new direct H-X contact is introduced.

Consequently both U,V are loaded. They are physical boundary common
neighbors of H,X, and the actual positive four-ring H-U-X-V-H
contradicts Section 3. This includes all four original private load
masks of U,V and every physical circle-corner mask.

Further forces at H remain arbitrary throughout these two caller
sections. No complete b1 or b2 coarse cell is declared closed here;
the other original attachment orbits and bridge layouts keep their
separate full source joins.

This fresh proof must receive its own complete reviews. Its elementary
half-lens calculation, selected center-order proof and original
degree/load callers are all included above; no missing historical
source or numerical diagnostic is used.

