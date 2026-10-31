# In a radial roof stack, the pocket above a nonnegative seam is empty

Date: October 29, 2026 UTC. Author: shared_terminal continuation.

**Status: complete proposed force-free hand theorem, frozen for full separate
review.** This strengthens the previously frozen individual capacity-one
theorem. The upper whole pocket is empty whenever its seam h is nonnegative;
reflection makes the lower whole pocket empty whenever h is nonpositive.
Thus the two actual hub pockets together have capacity at most one. Every
frame, physical circle mask, mean endpoint and weak extra contact remains.

Root proposed testing this one-sign emptiness conclusion after the earlier
capacity-one proof. The new circle-corner height lemma, whole-square routing,
complete separating-axis argument, far-wall rectangle and final boundary
return exclusion are authored here. Root is therefore a contributor to the
target strategy; a separate noncontributor review is required for adoption.

## 1. Complete physical hypotheses and conclusion

Keep actual closed unit squares with disjoint open interiors in the same
unchanged disk D_R, centered at O=0, with

    2<=R<=sqrt(Q), Q=1105/256,
    d=sqrt(R^2-1/4)-1, a=d-1,
    V=[d,d+1] times [-1/2,1/2],
    A=[a,d] times [h,h+1], -1/2<h<1/2.

Write H=h+1 and S=(a,H). Let B be an actual physical boundary unit with

    S in B, A intersect B={S},
    min_B y>h, max_B x<d.                            (1)

Its true degree, circle load and other forces are arbitrary. Its physical
circle point may have zero coefficient. No B force equation is used.

The upper physical pocket is the closed bounded region of the actual
occupied crosscut

    z_V -- (d,1/2) -- (d,H) -- S -- z_B              (2)

and the upper circle arc from z_V to z_B, where z_V is either actual
V circle corner and z_B is any actual B circle corner. This is precisely
the whole loop of the frozen capacity-one theorem. Its full proof of
simplicity, corner choices, strict half-disk clearance and whole-extra
localization remains at its original scope. The relevant routing is also
made explicit below for the stronger assertion.

**Theorem.** If h>=0, no whole actual additional unit E can occupy this
upper pocket. If the reflected lower stack has h<=0, its whole lower
pocket is empty. In a shared two-hub stack, at least one of the two hub
pockets is therefore empty, and the other has capacity at most one by
the frozen capacity theorem. Their combined capacity is at most one.

The conclusion is about actual contained units; it requires no loaded
endpoint concurrence, selected extra pose, extra contact with B, or
additional positive edge. Auxiliary separating axes below are geometric
proof directions and are never substituted for a selected stress normal.

## 2. Every physical B circle corner is strictly higher than S

Assume h>=0, so 1<=H<3/2. The exact radius interval gives

    -1/15<a<1/60, 14/15<d<61/60.                   (3)

The low comparison is `15/4-(29/15)^2=11/900>0`; the upper one is
`(121/60)^2-(Q-1/4)=31/57600>0`.

For completeness, the actual B center c satisfies

    |c_x|<31/40, c_y>31/30.

Indeed S is within half a diagonal of c, and 1/sqrt(2)<17/24 gives
`-31/40<c_x<29/40`. Equation (1) gives c_y>h+1/2>0. Physical circle
contact gives `|c|>=R-1/sqrt(2)>31/24`, so
`c_y^2>(31/24)^2-(31/40)^2=(31/30)^2`.
Consequently every actual B point has y>13/40>0. In particular every
actual B circle corner z has positive height.

Suppose, for contradiction, that some such z has z_y<=H. Since
H<3/2 and R>=2,

    |z_x|>sqrt(7)/2>d.

The positive sign is impossible by max_B x<d. Write

    z=(-A_0,b), A_0>sqrt(7)/2, 0<b<=H.

The horizontal displacement to the actual point S obeys

    A_0+a>sqrt(7)/2-1/15>5/4.                      (4)

The last comparison follows from
`7/4-(79/60)^2=59/3600>0`.

Let u,v be the two actual inward orthonormal edge directions of B at z.
Containment of its adjacent corners gives

    z.u<=-1/2, z.v<=-1/2.                          (5)

Write S=z+alpha u+beta v, with 0<=alpha,beta<=1. If both inward
vertical components are nonpositive, the nonnegative displacement
S_y-z_y can use only a horizontal edge, giving horizontal displacement
at most one, contrary to (4). Thus one inward edge goes upward; (5)
forces its horizontal component to be positive. Name it

    u=(C,s), C,s>0, C^2+s^2=1.

The other direction cannot be (-s,C), whose scalar product with z would
be positive. It is therefore v=(s,-C). The actual vertical displacement
and the actual horizontal displacement now give

    alpha s-beta C=H-b>=0,
    A_0+a=alpha C+beta s<=alpha/C<=1/C.             (6)

But (5) and alpha<=1 imply

    a C+H s=S.u=z.u+alpha<=1/2.

Using H>=1 and a>-1/15 yields s<17/30. Hence

    C^2>1-(17/30)^2=611/900>16/25,
    C>4/5.

Equation (6) then gives A_0+a<5/4, contradicting (4). The horizontal
inward-edge endpoint was included in the initial nonpositive case; every
side or corner position of S is retained in alpha,beta.

We have proved the whole physical-corner statement

    z_y>H for every actual B circle corner z.       (7)

No choice of a positively weighted corner, B frame, or B support owner
was imposed.

## 3. Whole-pocket routing forbids the lower-left quadrant

First take z_V=(d+1,1/2), the upper actual V circle corner. By (7) the
entire B segment S--z_B has height at least H. The top A segment has
height H. The only occupied crosscut pieces below H have x>=d.

The same is true of the upper circle arc below H. Since its endpoint
z_B has height greater than H, any portion of this upper arc with
y<H is on the right side of the circle and has

    x>sqrt(R^2-H^2)>sqrt(7)/2>d.

Thus the whole original loop misses the open lower-left quadrant

    {x<d,y<H}.                                      (8)

Every point of (8) can reach infinity horizontally to the left without
meeting the loop. It is therefore on the unbounded side. The closed
bounded pocket, and in particular any whole actual extra E in it, has
no point in (8). This is a whole-square conclusion, not a bound on the
center of E.

If instead the original loop uses the lower physical V circle corner,
the additional free component is the circular cap beyond V's outer side
x=d+1 between its two circle corners. The other difference between the
two chosen crosscuts lies inside the occupied V. That cap has horizontal
width R-(d+1)<1, whereas every unit has horizontal width at least one.
It cannot contain a whole unit. An extra's connected open interior cannot
pass between this cap and the upper component through the occupied V or
its circle corner. Thus every whole extra must still occupy the upper
component considered above. Both original circle-corner choices are
included without moving a force, a mean, or an actual packing unit.

## 4. Every hypothetical E must lie entirely above y=H

The following elementary complete separating-axis argument is useful.
If a closed square E avoids the open quadrant (8), there is a separating
unit direction n=(c,s) with c,s>=0 such that

    min_E n.z>=dc+Hs,                              (9)

and n is either East, North, or an own side axis of E.
One proof applies the separating-axis theorem to E and the rectangles
[-M,d] times [-M,H] as M tends to infinity. All possible axes belong
to the same finite list: the two rectangle axes and the two E axes,
with their signs. A fixed axis separates along an infinite subsequence.
A negative coordinate would make the rectangle's maximum projection
unbounded, impossible since E is bounded. Hence it has nonnegative
coordinates and gives (9). This covers weak side and vertex separations.

Every contained unit has center norm at most d+1/2, from its actual
farthest-corner inequality

    R^2>=|c_E|^2+|c_E|+1/2.

Its width in any unit direction is at least one. Thus its minimum
support in every direction is at most d. Equality forces the unique
radial S square in that direction: equality in both the center and
half-width bounds makes the center (d+1/2)n and the frame axial.

If n=East in (9), this equality forces E=V, contrary to distinct actual
interior-disjoint units. If n=North, the required conclusion min_E y>=H
already holds.

It remains that c,s>0 and n is an E own axis. Put b_0=min_E n.z.
Equations (9) and the support cap give

    dc+Hs<=b_0<=d.

If H>=d this is impossible because c+s>1. Hence H<d, and

    b_0>=H(c+s)>H>=1,
    c<=(d^2-H^2)/(d^2+H^2)<121/7321<1/60.         (10)

The first inequality for c follows by squaring
Hs<=d(1-c), dividing by 1-c>0, and using s^2=1-c^2.
The numerical bound uses H>=1 and d<61/60.

In the actual (n,Jn) frame, E is a unit side rectangle with n interval
[b_0,b_0+1]. Its two far-side vertices and b_0>=1 give

    |(Jn).z|<=sqrt(Q-4)=9/16 for every actual z in E.

Also n.z<=b_0+1<=d+1<121/60. Consequently

    max_E x<(1/60)*(121/60)+9/16
            =1073/1800<3/5<d.                     (11)

Since E avoids (8), (11) forces min_E y>=H in this final case too.
The separating-axis cover is exhaustive; no orientation branch is omitted.

Therefore every hypothetical pocket unit satisfies

    E subset {y>=H}, H<=d.                         (12)

In particular d<1 is already impossible. All remaining cases have
d>=1 and 0<=a<1/60, including the exact critical case d=H=1.

## 5. Every far-wall E contains one fixed closed interior rectangle

Assume (12). Let b_0=min_E y>=H>=1, and let C>=s>=0 be the larger
and smaller nonnegative own-axis vertical projections of the actual E.
Write w=C+s, C^2+s^2=1. Its actual center height is

    (c_E)_y=b_0+w/2<=|c_E|<=d+1/2,

so

    1<=w<=1+2(d-b_0)<31/30.

The increasing function s+sqrt(1-s^2) shows s<1/10, since at 1/10
it exceeds 109/100>31/30. Thus C>99/100. Moreover

    2Cs=w^2-1<61/900,
    s<61/1782<7/200,
    C>999/1000.                                    (13)

The last inequality follows from
`1-(7/200)^2>(999/1000)^2`. Both actual tilt signs are retained.

Take the two corners of the upper, almost horizontal edge. Their
horizontal separation is C, and each has height at least
b_0+C>=1+C>1999/1000. Containment therefore puts each of their
horizontal coordinates strictly between -567/1000 and 567/1000,
because

    (567/1000)^2+(1999/1000)^2-Q=867/800000>0.

Their midpoint has horizontal absolute value less than
567/1000-C/2<27/400. It differs from the actual center horizontally
by s/2, with either sign. Hence

    |(c_E)_x|<17/200,
    H+1/2<=(c_E)_y<=d+1/2.                        (14)

Consider the whole closed rectangle

    K=[-7/20,7/20] times [H+3/50,H+47/50].          (15)

For every z in K, (14) gives

    |z_x-(c_E)_x|<87/200,
    |z_y-(c_E)_y|<137/300.

Together with (13), both absolute own coordinates of z relative to the
actual E center are strictly less than 1/2. The exact two reserves are

    1/2-[87/200+(7/200)*(137/300)]=2941/60000>0,
    1/2-[(7/200)*(87/200)+137/300]=3373/120000>0.

Thus the entire closed rectangle K lies in int E. This statement includes
the axial case, both tilt signs, both support endpoints and every allowed
actual b_0. No frame or center of E has been changed.

## 6. Any B disjoint from that actual E is physically circle-clear

Since the actual B and E have disjoint open interiors, choose a geometric
unit separator g=(g_x,g_y) with

    max_B g.z<=min_E g.z.

This auxiliary separator need not be a positive pair normal and introduces
no contact or force. Since S=(a,H) belongs to B and the closed K is
strictly inside E,

    g.S<=min_E g.z<min_K g.z.                       (16)

If g_y<=0, the minimum over (15), minus g.S, is at most

    -(7/20-a)|g_x|+(47/50)g_y<0,

using 0<=a<1/60 and |g|=1. This contradicts (16). Thus g_y>0.
Using the bottom edge of K in (16) now gives

    (7/20-a)|g_x|<(3/50)g_y,
    t=|g_x|/g_y<9/50,
    1/g_y=sqrt(1+t^2)<51/50.                       (17)

The support cap for the actual contained E gives min_E g.z<=d.
Consequently max_B g.z<=d. Every z in B also satisfies

    |z_x|<=a+sqrt(2)<1/60+17/12=43/30,
    z_y>h>=0,

by its actual point S, the unit diameter, and (1). Combining with (17),

    z_y<=d/g_y+t|z_x|
        <(61/60)*(51/50)+(9/50)*(43/30)=259/200.

The entire actual B therefore lies strictly inside radius two, since

    |z|^2<(43/30)^2+(259/200)^2<4,
    4-(43/30)^2-(259/200)^2=96671/360000>0.         (18)

This contradicts its actual circle contact at R>=2. Thus no E from
Section 1 exists. The upper pocket is empty whenever h>=0.

## 7. Reflection, shared-hub entry and exact scope

Reflecting y and exchanging the two actual shared hubs sends the lower
pocket at seam h to the upper pocket at seam -h. It is therefore empty
whenever h<=0. At h=0 both pockets are empty. At either strict sign,
one is empty and the other has capacity at most one by the unchanged
complete capacity-one theorem. Their combined capacity is at most one.

The full shared-hub/parallel-roof entry of that frozen theorem proves
the exact chart, the strict seam interval, the actual B/C return points
and support bounds from the entire original unloaded A3,D3 and loaded V2
stars. It covers every original V physical mask before deriving radial S,
including coincident roof means. All original means on the positive
shared A--D, A--V and D--V segments remain free in their true closed
intervals. The present argument is force-free after that entry.

For the original D02 substitutions A=0,D=2,V=1,B=5,C=3,N=4,
the conclusion is valid in both L135 and L1345 throughout the whole
parallel-roof, positive-length A--D feature. Other owner features and
nonparallel roof normals are not discarded. A separate whole-feature
assembly must retain the real central region and B--N--C outer region
before deriving the complete three-extra contradiction. In L1345, N
is loaded and must not be called a transmitter.

## 8. Frozen input and verification boundary

The complete prior capacity source is preserved unchanged:

`SHARED_TRIANGLE_HUBS_PARALLEL_ROOF_BOTH_EXTERIOR_POCKETS_CAPACITY_ONE_2026_10_29.md`,
18880 bytes, 405 lines, SHA256
`ccc05fb4a7a8a633b9ba3abf5ad8712f71c50e2f754b75c1b5847297e5e5b1e5`.

Its operative scope is the original physical chart and loop, complete
half-disk clearance, individual capacity one, and the full shared-hub
parallel-roof entry. The new height lemma, complete quadrant/SAT cover,
fixed interior rectangle and whole B contradiction are proved above.
The center support inequality and equality are also rederived at the
degree-free scope used. The separating-axis theorem is elementary
convex-polygon geometry; its actual normals never replace stress data.

Exact rational arithmetic corroborated the new displayed reserves
867/800000, 2941/60000, 3373/120000 and 96671/360000. The proof is over
the complete continuous physical domain. No numerical pose, packing
certificate, graph contraction, normal reselection, force deletion,
mean movement, compilation, CI, remote mutation or merge was used.
No ledger or original gate is changed. Full separate review remains
required before adoption.
