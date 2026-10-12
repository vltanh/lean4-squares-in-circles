# Two-square outer caps force center signs across the perpendicular diameter

## Theorem — exact arbitrary-frame sign pruning

Let two interior-disjoint unit squares `S,T` of **independent,
arbitrary orientations** be wholly contained in a disk with

    R^2 <= 9789/2500

and wholly beyond a line at nonnegative radial offset

    y >= h >= 3/7.

Then their centers have **strictly opposite horizontal signs**:

    (p_S)_x * (p_T)_x < 0.                           (1)

In particular neither center lies on the perpendicular diameter
`x=0`. The same conclusion holds after rotating and reflecting
the coordinate system: any two whole squares in a cap whose
outward offset is at least `3/7` have center projections on
the perpendicular direction of opposite, nonzero sign.

This is a genuine continuum exclusion for *every orientation*,
not an assignment of an unproved separating axis to the pair.
It relies on the previously proved exact one-square cap-center
envelope; its only new estimate uses center distances and three
integer square comparisons.

## 1. All cap-square centers lie in a very narrow rectangle

Write the center of one square as `p=(x,y)`.
The square has horizontal/vertical half-width at least `1/2`
in any orthonormal coordinate frame. Since the whole square is
contained in `{y>=h}`,

    y >= h+1/2 >= 13/14.                             (2)

The universal center-radius bound for a contained unit square
is

    |p| <= sqrt(R^2-1/4)-1/2.

For completeness, with the square's own unit axes `e,f`,
the farthest squared vertex norm is exactly

    |p|^2 + 1/2 + |p dot e|+|p dot f|
       >= |p|^2+|p|+1/2.

Rearrange this quadratic to get the bound. It implies

    y <= sqrt(R^2-1/4)-1/2.

The single-square arbitrary-frame cap envelope in
HUMAN_ONE_SQUARE_CAP_ENVELOPE.md gives, whenever
the whole square lies in `y>=h>=2/5`,

    (h+1)^2+(|x|+1/2)^2 <= R^2.

It follows that

    |x| <=sqrt(R^2-(1+h)^2)-1/2.                    (3)

Both upper bounds increase with R and decrease appropriately
with h. In the present search domain they imply

    |x| < 87/100,
    13/14 <= y < 13/14+49/100.                     (4)

To check the first strict inequality, put
`h=3/7` and `q_+=9789/2500` in (3).
The required square-root comparison is simply

    (137/100)^2 - [q_+-(10/7)^2]
       =1037/490000>0.

For the height range, note

    sqrt(q_+-1/4) -(10/7) <49/100,

because, after squaring two positive quantities,

    (10/7+49/100)^2 -(q_+-1/4)
      =1501/98000>0.

This proves (4) with exact rational bounds.

## 2. Centers on the same side would be too close

Suppose both square centers have `x>=0`.
Equation (4) puts their x coordinates in the interval
`[0,87/100)`, and their y coordinates in the
same interval of length strictly less than `49/100`.
Therefore

    |p_S-p_T|^2
       < (87/100)^2+(49/100)^2
       = 997/1000 <1.                                 (5)

But each unit square contains the open Euclidean disk of
radius `1/2` centered at its center. Those inscribed
disks are interior-disjoint, so

    |p_S-p_T| >=1,                                    (6)

contradicting (5).

The case where both x coordinates are nonpositive
is identical under the reflection `x -> -x`.
If either center had x=0, it would necessarily
share one of those weak sign half-planes with
the other center, so that case is also excluded.

Thus the x coordinates must have opposite *strict*
signs, proving (1). QED.

## 3. Consequences for the eight-square classification

Let C contain the disk center in its open interior,
and write its center in its own frame as `(a,b)`,
with signed central side distances

    h_R=1/2+a,  h_L=1/2-a,
    h_U=1/2+b,  h_D=1/2-b.

If a signed central side with outward offset
`h>=3/7` serves **two or three** complete exterior
squares, then those squares include centers of
**both strict transverse signs**.

In fact, three such whole squares on that side
are now impossible: applying the theorem to
*each* of the three pairs would require three
real numbers to have pairwise strictly opposite
signs. This recovers part of the three-square
cap restriction for sufficiently large h,
though the existing sharp three-square cap
theorem already gives the stronger bound
`h<7/24`.

The new contribution is for **two-square side caps**.
If both opposite sides of one central axis serve
at least two squares (a 2+2 count profile),
then their offsets are `1/2+t,1/2-t`.
At least the farther side has offset >=1/2>3/7,
so its two centers necessarily have opposite
signed projections on the *perpendicular diameter*.
If `|t|<=1/14`, both side offsets are >=3/7,
and **both cap pairs** have transverse centers
of opposite strict signs.

This is new sign information beyond the
numeric interval `|t|<5/24` in
HUMAN_ALL_SIDE_OFFSET_INTERVALS.md.
It does not assert that the squares are
wholly in the respective origin quadrants,
and a square's center sign cannot be
silently substituted for a second available
whole-square central-owned separator.

The sharp global lower bound `R8>=Rhat`
remains unproved.


## 4. Stronger one-tenth clearance in caps beyond offset one half

**Corollary.** Under the theorem's eight-square search ceiling,
suppose two entire unit squares lie beyond the same line
`y=h>=1/2`. Their centers satisfy, after labeling,

    (p_S)_x < -1/10,       (p_T)_x >1/10.                (7)

Furthermore both centers have Euclidean norm **strictly greater
than one**, so the pair consists of outer-center squares.

**Hand proof.** By the orientation-free one-square center
envelope, every center (x,y) in the cap obeys

    |x|<=sqrt(q-(1+h)^2)-1/2
         <=sqrt(q_plus-9/4)-1/2
         <4/5,

because `q_plus-9/4=4164/2500<(13/10)^2`.

The universal center-radius bound and the cap support give

    h+1/2<=y<=sqrt(q-1/4)-1/2.

Therefore any two such centers have

    |dy| <=sqrt(q_plus-1/4)-(1+h)
          <=sqrt(2291/625)-3/2 <5/12,

where the final inequality is verified by

    (23/12)^2-2291/625
       = 721/90000 >0.

If either center had `|x|<=1/10`, the other one's
absolute x coordinate <4/5 would give

    |dx| <9/10.

Their squared distance would then be strictly less than

    (9/10)^2+(5/12)^2
       =14164/14400<1,

contradicting their disjoint inscribed radius-1/2
disks. Hence both centers have |x|>1/10.
Section 2 of this note already proved that the
two x signs are opposite, giving (7).

Finally y>=h+1/2>=1 and |x|>1/10,
so |p|>1 for both squares. QED.

Thus whenever a central side serves two whole squares
at outward offset >=1/2, **both are outer** and
their centers occupy the two separated transverse
lanes `x<-1/10` and `x>1/10`.
In a 2+2 opposite-side profile, at least the more
distant side always has this conclusion, since
its offset equals `1/2+|t|>=1/2`.
The closer cap has only the weaker opposite-sign
conclusion when its offset is >=3/7.

These are geometric filters on continuous center
positions and outer/inner status, not a proof that
any particular coarse side-count profile is
unrealizable.
