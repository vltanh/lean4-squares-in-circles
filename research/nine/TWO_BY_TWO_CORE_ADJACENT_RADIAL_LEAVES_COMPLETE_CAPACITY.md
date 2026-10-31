# Any two-by-two core with radial leaves at one outer edge has capacity at most eight

Date: October 27, 2026.

**Status: complete force-free hand capacity theorem, submitted for
full root and separate independent review.** This removes the explicit
parameter interval from
`TWO_BY_TWO_CORE_WITH_RADIAL_SIDE_LEAVES_CAPACITY.md` and states the
actual geometric premise without an assumed origin placement. It
does not supply a reduction of every original high LCD.SS pose to
that premise.

Let all actual unit squares be contained in a common disk of radius
R with

    R^2<=Q=1105/256,

and have pairwise disjoint open interiors. Suppose four of them tile
one actual square of side two. Suppose two other actual squares have
the common radial-S form

    S(e)=[d,d+1]e+[-1/2,1/2]Je,
    |e|=1,       d>0,

and their actual inner-face midpoints d*e are the two endpoints of
one outer side of that two-by-two core. In particular these hypotheses
hold for genuine S leaves of the same containing circle at those two
outer vertices, with d=sqrt(R^2-1/4)-1.

**Theorem.** There are at most two other actual unit squares in the
collection. Thus this six-square geometry cannot occur in the original
nine-square packing, with arbitrary orientations, contacts, physical
circle masks or forces of the other three units.

Neither a contact-normal selection nor an equilibrium equation is
needed. Even outer-circle equality at the radial leaves is unnecessary;
their actual containment and the common radial support d suffice.

## 1. Containment forces the complete origin position and parameter interval

Rotate about the original circle origin so that the indicated outer
side of the core is horizontal and the core lies above it. Write its
actual endpoints as

    (xi-1,-q),       (xi+1,-q).

Both are actual radial-S inner midpoints of norm d. Subtracting their
squared norms gives 4xi=0. Hence xi=0, and the four actual units
tile exactly

    P=[-1,1] times [-q,2-q],
    d^2=1+q^2.

No translation of the circle origin has been made. In particular the
perpendicular bisector condition is a consequence of the two actual
leaf radii, rather than an assumed symmetry of the pose.

The far corners of either radial unit give

    (d+1)^2+1/4<=Q,
    d<61/60,
    q^2<121/3600.

The second strict bound follows from
Q-1/4=1041/256<(121/60)^2. Thus |q|<11/60<3/16.
The actual far core corner (1,2-q) also belongs to the containing
disk, and therefore

    (2-q)^2<=849/256<(51/28)^2.

The exact last reserve is 15/12544. It follows that

    q>5/28>1/8,       q<11/60<3/16.              (1)

In particular q is positive. These are consequences of the six
actual units' containment, with no preselected numerical pose.

## 2. Each additional unit supplies a single long inner-circle arc

Put

    rho=9/8,       gamma=arccos(4/5).

Any additional unit E has open interior disjoint from the entire
closed rectangle P: an open neighborhood of any point on any tile
side or junction would meet the interior of one of the actual four
tiles. Since P contains the open disk of radius q, this also gives
dist(O,E)>=q>1/8, including all possible touching limits.

Apply the complete arbitrary-orientation theorem
`NINE_EIGHTHS_INNER_ARC_OUTSIDE_ONE_EIGHTH.md`, independently
accepted in
`REVIEW_NINE_EIGHTHS_ARC_ONE_EIGHTH_CLEARANCE_ROOTED_BLOCKS_2026_10_27.md`.
The actual open interior of each E intersects the radius-rho circle
in exactly one connected open arc longer than gamma. The arcs of
different additional units are disjoint.

For completeness, (1) even gives q>sqrt(2)/8, since
(5/28)^2-1/32=1/1568>0. Thus the earlier independently accepted
`NINE_EIGHTHS_INNER_ARC_AWAY_FROM_CENTRAL_DISK.md` would also
suffice for this particular capacity caller.

## 3. Actual occupied arcs and the complete free-gap routing

Define

    theta_0=arccos(8/9),
    phi=arctan(q),
    alpha=arccos(d/rho).

The actual containment bounds ensure 1<d<61/60<rho. On the
radius-rho circle, |x|<=1 gives |y|>=sqrt(17)/8>q, and its
upper height is at most rho<2-q. Consequently the complete closed
core arc is

    [theta_0, pi-theta_0].

The actual radial leaf directions are -phi and pi+phi. Each leaf
occupies the complete closed arc of half-width alpha about its own
direction: the normal coordinate is at least d exactly on that arc,
the outer normal bound is automatic from rho<d+1, and the tangent
bound is strict because

    rho^2-d^2=17/64-q^2<1/4.

We have

    phi<alpha<theta_0,
    phi<pi/6,       alpha<pi/6.

Indeed alpha<theta_0 uses d>1. The other comparison follows from
d^2=1+q^2<265/256<rho, so cos(alpha)=d/rho<1/d=cos(phi).
The two pi/6 bounds follow respectively from q<3/16 and
sin(alpha)<4/9.

Thus the three actual closed occupied arcs are disjoint and have
exactly three open complementary intervals. The two side gaps have
equal lengths

    G_side=theta_0+phi-alpha<theta_0<gamma,        (2)

and the bottom gap has length

    G_bottom=pi-2phi-2alpha.                     (3)

An additional unit's open arc avoids all three closed occupied arcs.
This includes their boundary endpoints: an open interior neighborhood
there would meet the interior of the actual core or actual leaf.
Its connected arc must therefore lie wholly in one of these three
gaps. By (2) neither side gap can contain even one such arc.

## 4. The bottom gap is strictly shorter than three required arcs

The exact cosine identity is

    cos(phi+alpha)
       =(8/9)*(1-(q/d)*sqrt(17/64-q^2)).          (4)

From (1) and d<61/60,

    q/d>75/427,
    sqrt(17/64-q^2)>19/40.

For the second inequality use q<3/16 and sqrt(59)/16>19/40.
Hence (4) gives the strict rational bound

    cos(phi+alpha)
       <(8/9)*(1-1425/17080)
       =3131/3843
       <49/60.                                 (5)

The last rational reserve is 149/76860. All estimates refer to the
actual common parameter of the unchanged leaves and core.

Now cos(3gamma)=-44/125, and

    cos((pi-3gamma)/2)=13/(5sqrt(10))>49/60.

The positive-square difference for the last comparison is exactly
163/18000. Both phi+alpha and (pi-3gamma)/2 belong to (0,pi/2),
so (5) implies

    phi+alpha>(pi-3gamma)/2,
    G_bottom<3gamma.

Three additional actual units would have three disjoint open arcs,
each longer than gamma, all in that bottom gap. Their total length
would exceed 3gamma, contradicting the strict gap bound. This
proves the capacity theorem for the whole stated physical geometry.

## 5. Exact uses and retained boundary of the result

The six original units in
`ADJACENT_TWO_S_LEAF_C4_HIGH_CORE_WITNESS.md` satisfy the theorem:
the four aligned cycle units tile the core and their two actual
genuine S inner midpoints are its two lower outer vertices. Their
exact stress, contact means and individual circle weights remain
valid. The theorem rules out the three additional original units,
while preserving all of those six-body identities.

More generally a later original-domain proof need only establish
the physical two-by-two tiling and the two genuine radial leaf
applications at one outer side's endpoints. It need not assume an
origin alignment, solve the witness's algebraic radius, bound its
parameter in advance or prescribe any additional square's angle.
All those geometric bounds used here follow from actual containment.

This is a complete physical capacity family, not yet a whole high
LCD.SS graph-family join. No numerical pose, compilation, CI,
remote mutation, force deletion or shared metadata edit is used.
