# The all-side strict-turn C6 central region has capacity at most one

Date: October 25, 2026.

**Status: accepted complete whole-family hand proof after independent
source and scope review in REVIEW_C6_ALL_SIDE_CENTRAL_CAPACITY_2026_10_25.md.**
No computational certificate, angle subdivision, numerical
pose, normal reselection, or new gate identifier is used.

This proves a joint completion restriction for the entire remaining
all-unique, all-side alternating C6, including both the one-share and
two-share families and every actual shared-mean endpoint. The original
six physical bodies and all three completion squares remain present.

## 1. Original physical scope and theorem

Let the complete selected positive component be the original alternating
six-cycle of three loaded squares S_i and three unloaded side-normal
transmitters W_i. Retain its proper counterclockwise force-polygon
orientation and write its positive channel forces as

    f_i=mu_i n_i,       mu_i>0,       |n_i|=1,
    pi/2<theta_i=angle(n_(i-1),n_i)<pi,
    sum theta_i=2pi.

Let p_i^- and p_i^+ be the original incoming and outgoing application
means on S_i. Assume the already accepted actual-port conclusion:

    p_i^- and p_i^+ are distinct points of one physical side of S_i.

Put

    p_i^+-p_i^-=ell_i u_i,       |u_i|=1,       0<ell_i<=1.

The actual side-transmitter displacement is

    p_(i+1)^- - p_i^+ = n_i.                           (1)

Every remaining all-unique all-side C6 satisfies these premises by
`SIX_CYCLE_UNIQUE_STRICT_TURN_AND_SHARED_NORMAL_FORM.md`; that theorem
includes theta_i=3pi/4 and all original side-mean endpoints. This source
does not assume that genuine sharing forces ell_i<1.

**Theorem.** The entire bounded central free union of the actual six-body
ring contains at most one additional unit square.

The theorem only uses the displayed original port-side and strict-turn
premises, together with the physical ring embedding. In particular it
does not use any unique-corner force-value identity or any ratio of
circle weights. A different physical mask may use the theorem once its
own original port-side and strict-turn premises are established. Those
premises are not asserted here for the entire strictly obtuse one-radial
family.

## 2. The actual contact hexagon is strictly convex and has perimeter at most six

The incoming original application minimizes n_(i-1) on S_i, and the
outgoing application maximizes n_i. Hence

    n_(i-1) dot u_i >=0,       n_i dot u_i >=0.          (2)

Rotate n_(i-1) to angle zero and n_i to angle theta_i in (pi/2,pi).
The intersection of the two closed semicircles in (2) puts the actual
direction of u_i at an angle eta_i satisfying

    theta_i-pi/2 <= eta_i <= pi/2.                      (3)

Thus

    0<eta_i<theta_i,       0<theta_i-eta_i<pi.          (4)

Both inequalities remain strict when either scalar product in (2)
vanishes. Those are precisely the side-axis/shared-mean limits that
must not be discarded.

Consider the closed polygonal chain with the actual vertices

    p_0^-, p_0^+, p_1^-, p_1^+, p_2^-, p_2^+.

Its edges alternate between ell_i u_i and n_i. All six lengths are
positive; by (3)--(4), their directions turn strictly counterclockwise,
once in total. The total turn is the original sum theta_i=2pi.

Here is a direct convexity verification that does not assume the chain
is already a generic simple polygon. Fix any one directed edge as the
horizontal axis. Along the remaining edges in their cyclic direction
order, the vertical increments are first nonnegative and then
nonpositive, since their arguments pass once through (0,pi) and then
(pi,2pi). The chain closes, so its vertices never drop below the line
of the fixed edge. The strict direction changes at the two neighboring
edges make every other vertex strictly above that line: the first
increment is positive, the last is negative, and no further sign change
can return to height zero early. Thus every edge is a distinct supporting
edge of the convex hull. The chain is its boundary, with six strict
vertices.

Call this strictly convex contact hexagon H. Its exact perimeter is

    Per(H)=3+ell_0+ell_1+ell_2 <=6.                     (5)

This retains ell_i=1 at every body where it actually occurs, including
an original shared-side application at a side endpoint.

## 3. Every central completion square lies in this one hexagon

Each loaded chord p_i^-p_i^+ lies in the actual closed square S_i.
Each channel edge in (1) lies in the actual closed transmitter W_i.
Therefore the entire boundary of H lies in the closed occupied core.

We need inclusion of the whole central free union, not just a region
suggested by the contact diagram. Use the compatible physical
center/contact ring embedding already supplied by
`PHYSICAL_BODY_GRAPH_UNCROSSING.md` and used in
`CONTACT_RING_HOLE_AREA.md` and
`SIMPLE_CYCLE_CHANNEL_POCKET_CAPS.md`.

Fix a point in the open interior of any central completion square.
Its distance from the closed core is positive. Indeed an open point
of one unit cannot belong even to the boundary of another unit without
its small neighborhood meeting the latter's interior. Choose the
arbitrarily small physical routing closer to the core than this positive
distance. Its winding number at the chosen point is one, by the original
central region label.

Within each actual convex core square, replace the center/contact path
between its two applications by their straight chord. This is a homotopy
inside that occupied square. For a transmitter the straight chord is
exactly the corresponding segment in (1). The homotopy avoids the chosen
point and yields the contact chain in Section 2. Its winding number at
that point is therefore still one. Since H is a convex simple hexagon,
the point belongs to its open interior.

The same argument applies simultaneously to any finite collection of
compact inner portions of all central extra interiors. At a coincident
junction or a shared endpoint, choose the routing sufficiently small
for those compact portions first; all replacements still occur within
the occupied core or its arbitrarily small routing neighborhood. Their
positive distances are retained. Passing to the portions' closures
shows that every whole central extra lies in the closed H.

This includes every component of the bounded central free union.
Additional zero-force contacts may subdivide that union but cannot
change the winding argument or add a central extra outside H. No
transmitter is moved, and no original application mean is replaced.

## 4. Any two disjoint unit squares require convex-hull perimeter at least six

We prove an elementary general lemma. Let K and L be any two
interior-disjoint unit squares, with centers c_K,c_L, and let
d=c_L-c_K. Translate c_K to zero. Write h_K(n), h_L(n) for the support
functions of the centered squares; central symmetry gives
h_K(-n)=h_K(n) and h_L(-n)=h_L(n).

For Q=conv(K union L), the width in unit direction n is exactly

    width_Q(n)
       =max(h_K(n),d dot n+h_L(n))
          +max(h_K(n),-d dot n+h_L(n))
       =h_K(n)+h_L(n)
             +max(|d dot n|,|h_K(n)-h_L(n)|)
       >=h_K(n)+h_L(n)+|d dot n|.                    (6)

Cauchy's perimeter formula integrates width over a half-turn. Since
both squares have perimeter four and are centrally symmetric,

    Per(Q) >= (Per(K)+Per(L))/2 + 2|d| =4+2|d|.       (7)

For clarity, the only general perimeter fact used here is
Per(C)=integral_0^pi width_C(n_theta) dtheta for a convex planar set;
for polygons it follows by integrating the absolute projections of
their oriented edges. Also
integral_0^pi |d dot n_theta| dtheta=2|d|.

Interior-disjoint convex squares admit a weak separating line with
unit normal n directed from K toward L. Every unit square has support
half-width at least 1/2, so

    |d| >= n dot d >= h_K(n)+h_L(n) >=1.              (8)

Combining (7)--(8) gives Per(Q)>=6 for arbitrary orientations.

The equality case is equally useful. If Per(Q)=6, (7)--(8) force
|d|=1. Equality in (8) then forces d=n and
h_K(n)=h_L(n)=1/2. A unit square has half-width 1/2 exactly in one
of its side-axis directions. Thus both squares have the same axes,
their centers differ by one unit along a common axis, and they are
adjacent along a complete side. Their convex hull Q is exactly a
2-by-1 rectangle.

## 5. Complete central-capacity contradiction

Suppose two original extra unit squares were central. Section 3 puts
their convex hull Q inside H. Perimeter is monotone under inclusion
of convex planar sets, so Sections 2 and 4 give

    6 <= Per(Q) <= Per(H) <=6.

All three perimeters therefore equal six. Section 4 makes Q a 2-by-1
rectangle. Moreover Q=H: if a convex set properly contains another
convex set with nonempty interior, their support functions differ
positively on an open interval of directions, and Cauchy's perimeter
formula makes its perimeter strictly larger.

But H has six strict vertices by Section 2, whereas Q has four.
This contradiction proves the theorem, including the limiting case
ell_0=ell_1=ell_2=1. No strict chord-shortening premise was needed.

## 6. Joint effect on the remaining completion families

At the original checkpoint, every remaining all-unique all-side C6
had exactly one or two genuine shares by the accepted matching
exclusions. Both entire families satisfy the premises here.
Their three completion units therefore have at most
one member in the whole central free union, and **at least two members
in the union of the actual exterior channel caps** supplied by
`SIMPLE_CYCLE_CHANNEL_POCKET_CAPS.md`.

This eliminates the two-central/one-exterior allocation at once, with
no reliance on diagnostic contact areas and no restriction on the
physical sharing pattern, force ratios, or transmitter positions. It
does not assume those two exterior extras occupy distinct pockets;
such a conclusion needs the relevant whole-pocket capacity theorem.

The remaining joint capacity obligation is still genuine: exclude every
placement of the remaining extras among those actual caps, coupled with
the possible one central unit. The strictly obtuse one-radial C6 may
use this theorem only where its original port-side and strict-turn
premises have been proved. No unrestricted nine-square closure, equality
classification, or Lean verification is asserted here.

## 7. Subsequent complete contact and cap reductions

SIX_CYCLE_TWO_SHARE_COMPLETE_EXCLUSION.md now excludes all two-share
orbits. The exact one-share cover in
SIX_CYCLE_ONE_SHARE_FULL_ORBIT_COVER_AND_RESIDUE.md leaves only
mixed corner word 110 with its sole outgoing share at unit 0.
This entire surviving type still satisfies the hypotheses proved
in Sections 1--3; its actual closure additionally gives a strict
perimeter less than six.

SIX_CYCLE_REMAINING_ONE_SHARE_CHANNEL_1_EMPTY.md now excludes the
whole actual exterior pocket 1 by a strict circle-chord height
inequality. Consequently the three extras have at most one
central member and every other member in actual caps 0 and 2.
All repeated-pocket count allocations and every original
transmitter position remain. These later exclusions strengthen the
necessary allocation cover; they do not prove central capacity
zero or finish the three-extra completion.

