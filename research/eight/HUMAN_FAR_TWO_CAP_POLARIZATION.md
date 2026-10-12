# A far two-square cap forces both centers at least seven twenty-fifths across the diameter

## Theorem (arbitrary rotations; exact n=8 ceiling)

Let two unit squares S,T, of completely independent orientations,
have disjoint open interiors and lie wholly in

    D_R intersection {y>=h},

with

    R^2<=9789/2500,       h>=3/5.

Then, after exchanging S,T if necessary, their center
coordinates satisfy the *strict, quantitative sign split*

    (p_S)_x < -7/25,          (p_T)_x > 7/25.         (1)

Thus the two centers lie on opposite sides of the
perpendicular origin diameter, each at distance
strictly greater than 7/25 from it. This improves
the previously proved one-tenth split at h>=1/2
for the more distant part of the cap range.

No frame alignment, contact, stress, or selected
square-square separating direction is assumed.

## Hand proof

Put q_plus=9789/2500. For the center
p=(x,y) of either square, whole-cap membership
implies

    y>=h+1/2>=11/10,                                (2)

because every unit square has vertical
projection half-width at least 1/2.

The exact single-square cap center envelope
HUMAN_ONE_SQUARE_CAP_ENVELOPE.md applies
since h>=3/5>2/5. It gives

    (1+h)^2+(|x|+1/2)^2<=R^2<=q_plus.

Consequently

    |x|<=sqrt(q_plus-(8/5)^2)-1/2
         =sqrt(3389)/50-1/2
         <133/200.                                   (3)

For the strict rational comparison, it is
equivalent to sqrt(3389)<233/4, and
16*3389=54224<54289=233^2.

Independently, the exact greatest squared
vertex norm formula bounds every unit
square center by

    |p|<=sqrt(R^2-1/4)-1/2
        <=sqrt(q_plus-1/4)-1/2
         =sqrt(9164)/50-1/2
         <48/25-1/2,

because 9164<96^2. In particular

    y<48/25-1/2=71/50.                              (4)

Combining (2),(4) for the two centers gives

    |(p_T)_y-(p_S)_y|
        <71/50-11/10=8/25.                         (5)

Their open inscribed radius-1/2 disks are
interior-disjoint, so

    |p_T-p_S|>=1.                                   (6)

If both x coordinates had the same weak sign,
equation (3) would give |dx|<133/200,
and (5) would give

    |p_T-p_S|^2
       <(133/200)^2+(8/25)^2
       <1,

contradicting (6). Therefore the x
coordinates have strict opposite signs.

Suppose, contrary to (1), that one
has absolute x coordinate <=7/25.
The other is less than 133/200
in absolute value, so

    |dx| < 133/200+7/25=189/200.

Together with (5) this implies

    |p_T-p_S|^2
       <(189/200)^2+(8/25)^2
        =(35721+4096)/40000
        =39817/40000 <1,

again contradicting (6). Hence both
absolute x coordinates are >7/25.
Because their signs are opposite, (1)
follows upon relabeling. QED.

## New branch consequence: the saturated Type C square ring

Consider a full eight-square packing at q<=q_plus
whose central square C has center (a,b) in its
own side frame. Suppose the four central
side populations are

    N_R=N_L=N_U=N_D=2,                             (7)

and exactly one exterior square has double
central-owned separator status RU. This is
saturated Type C in SATURATED_SIDE_STATUS_BRANCHES.md.

The sharp one-square double-corner cap bound gives

    a+b<-1/5,                                      (8)

as proved in TRIPLE_DOUBLE_STATUS_PRUNING.md.
Consequently **at least one** of a,b is
strictly less than -1/10.

* If a<-1/10, the **left** central side has
  offset h_L=1/2-a>3/5. Its two whole-cap
  squares must have center y coordinates of
  opposite signs and magnitudes >7/25.
* If b<-1/10, the **lower** central side has
  offset h_D=1/2-b>3/5. Its two whole-cap
  squares must have center x coordinates
  of opposite signs and magnitudes >7/25.
* If both a,b<-1/10, **both** of these
  signed center-polarization conclusions
  hold simultaneously.

Thus **every** Type C branch has at least one
pair of outer side-cap squares forming a
quantitative +/-7/25 *transverse center
split*. This is stronger than knowing
simply that opposite side populations
are both two, and needs no common square
frame or circle contact.

The theorem applies equally to any other
surviving branch for which two whole
squares occupy a side at offset >=3/5.

## Scope

A statement about two center coordinates
of opposite sign is **not** a statement
that their *whole squares* lie in opposite
origin quadrants. The displayed x intervals
may still cross the origin diameter if the
squares are rotated, and no perpendicular
central-owned separating axis is inferred.

In particular this new necessary
geometry does not by itself eliminate
saturated Type C or establish the
unrestricted sharp lower bound R8>=Rhat.
It provides exact narrow, disjoint
real-variable subdomains for its
remaining orientation/placement analysis.
