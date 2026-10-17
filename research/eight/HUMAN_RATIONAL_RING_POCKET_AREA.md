# Exact area obstruction to inserting an eighth, central square into the rational seven-ring

## Statement

Take the seven unit squares and the seven rational contact
points `z01,z12,z23,z34,z45,z56,z60` of
RATIONAL_SEVEN_EXTERIOR_CONTACT_CYCLE.md.
Let P be the closed contact polygon joining those points
in cyclic order. The previous note proves that P is a
positively winding simple polygon, contains the origin in
its interior, and its sides traverse the seven actual
square interiors (or boundary segments).

**Theorem.** The area inside P not occupied by the seven
squares is exactly

    23288171643871/26015100250000 < 1.             (1)

In particular **no eighth unit square containing the
origin in its open interior** can be added to this
seven-square ring, regardless of the eighth square's
orientation, center or contacts, without overlap.

This shows explicitly how the central obstacle invalidates
a ring-only proposed lower bound. It is a certificate for
the *particular rational ring*, not a sharp inequality
for all seven-ring geometries.

## 1. The winding argument places an eighth central square inside P

Suppose another packed unit square C has the origin in
its open interior. Its open interior is connected and
avoids every one of the seven closed ring squares; in
particular it avoids the contact polygon P contained
in their union. The polygon has winding number +1 about
the origin, by section 5 of the ring note.
Winding is constant on the connected set int(C).
It is therefore one throughout int(C), so all of
int(C) lies in the **bounded interior** of P.

Moreover C's open interior is disjoint from the seven
ring squares' open interiors. Therefore a necessary
area inequality is

    1=area(int(C))
      <=area(int(P) minus union_(i=0)^6 S_i).         (2)

We will prove that the right side is <1.

## 2. Exact signed polygon area

For 2D vectors write `a cross b=a_x*b_y-a_y*b_x`.
The ordinary shoelace formula for the seven rational
contact points gives

    area(P)=(1/2)*sum_(j=0)^6 z_j cross z_(j+1)
           =120475483627389/41624160400000
           <29/10.                                  (3)

The sign is positive in the cyclic orientation
and the polygon is simple, so this is its ordinary
(nonmultiplicity) area. The last comparison is just
positive integer cross multiplication.

## 3. The ring squares take almost two units of inner area

Number the squares S_0,...,S_6 and choose the
oriented chord for S_i from its **incoming**
contact point `z_(i-1)` to its **outgoing**
contact point `z_i`, indices mod seven.
Every chord lies in S_i by convexity.

For each i, let A_i be the area of the part
of S_i strictly to the **left** of this oriented
chord (up to its boundary). In the interior
of S_i, the contact polygon has no other
edge: every other edge lies in a different
packed square with disjoint open interior.
Across the oriented chord its winding jumps
up by one from right to left. Since P is simple,
positively oriented, and bounds a region of
winding one, the left-hand part of S_i is
precisely the portion of int(S_i) that lies
inside P, up to area-zero boundaries.

This also covers a chord running along a
square side (the inward piece may then have
area zero); in the present construction every
listed piece is positive. The seven inner
pieces are pairwise interior-disjoint, because
the squares themselves have disjoint interiors.

**Exact rational area computation.**
To audit each entry, use the actual rational
four corners of S_i from section 1 of the
ring note. Clip that convex quadrilateral
by the single oriented half-plane

    (z_i-z_(i-1)) cross (x-z_(i-1)) >= 0.

Every new clip vertex is the intersection of
a rational side segment with this rational
line; its coordinates are therefore rational.
Apply the elementary shoelace formula to
the resulting three- or four-vertex piece.

| i | Exact inner-piece area A_i | Convenient strict lower bound |
|---|---|---|
| 0 | 1597/2000 | 79/100 |
| 1 | 3481959/50500000 | 6/100 |
| 2 | 17/160 | 10/100 |
| 3 | 13419/80000 | 16/100 |
| 4 | 189/400 | 47/100 |
| 5 | 6849263399/40804000000 | 16/100 |
| 6 | 90486952161533/416241604000000 | 21/100 |

Every strict comparison in the final column is
a single integer multiplication. Summing these
elementary bounds gives

    sum_(i=0)^6 A_i
      >(79+6+10+16+47+16+21)/100
      =195/100=39/20.                              (4)

The exact sum is
`area(P)-23288171643871/26015100250000`;
no approximate polygon geometry is used.

## 4. The central free area is strictly below one

The polygon P and the seven squares are all
compact polygons, hence their boundaries
have area zero. Subtracting the seven
disjoint portions of its area covered
by the ring squares gives exactly

    area(int(P) minus union S_i)
       =area(P)-sum_i A_i
       =23288171643871/26015100250000.

Even without multiplying out the large
fractions, (3)--(4) give the short
strict rational estimate

    area(int(P) minus union S_i)
      <29/10-39/20=19/20<1.

This contradicts the necessary inequality (2).
Thus no central unit square can be inserted,
regardless of its frame orientation. QED.

## Consequence and limitations

Seven exterior squares with a **genuine,
positively winding contact ring** fit in
squared radius 1957/500, slightly below
the proposed eight-square candidate.
But in this explicit ring the available
central pocket has area **less than a
single unit square**, so it cannot be
extended to an eight-square packing.

This identifies one quantitative central
obstruction—*available interior area*
in addition to the enclosing circle—
which a sharp seven-ring proof may try
to generalize. The current computation
does not establish a universal bound
on that area across all orientations,
contacts and radii, and is not a proof
of the unrestricted inequality R8>=Rhat.
