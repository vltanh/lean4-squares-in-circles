# Every 3+1 opposite central-side profile contains a true three-square diameter chain

## Theorem (whole-square status, arbitrary frames)

In an eight-square packing in D_R with
R^2<=9789/2500, let C be the unique square
containing the disk origin in its open interior.
Fix one signed central side normal n and
write m=Jn. Suppose **three** distinct exterior
squares are wholly beyond C's outward n side,
and **one** other exterior square T is wholly
beyond C's opposite -n side.

Then there exist two **distinct single-side
status** exterior squares S_+ and S_- such that:

* int(S_+) meets the **positive n ray** from zero;
* int(S_-) meets the **negative n ray** from zero;
* the positive and negative ray intersections
  lie on opposite sides of C, and the diameter
  through n meets the open interiors of
  **at least three** distinct packed squares
  in the order S_-, C, S_+.

Here S_+ is one of the three n-cap squares,
and S_- is the unique opposite-cap square T.
In particular the opposite singleton cannot
lie wholly in either of the two origin
quadrants adjoining its far side: it
necessarily **straddles their common cardinal
diameter in its open interior**.

The conclusion is a ray-level straight
three-part separation chain; it does not
say the three squares have parallel frames
or that either exterior square has an
actual-contact edge with C. It is valid
for all possible orientations and central
side offsets, with no stress hypothesis.

## Hand proof

Rotate to n=(1,0); write p_C=(a,b),
where -1/2<a,b<1/2.
The positive central side has offset

    h_+=a+1/2>0,

and the negative side has offset

    h_-=1/2-a=1-h_+>0.

The orientation-independent three-square
disk-cap theorem, together with
R^2<2257/576, forces

    h_+<7/24,      h_->17/24.                    (1)

By HUMAN_TRIPLE_SIDE_RAY_PENETRATION.md,
one of the three positive-side members,
called S_+, intersects the open positive
x ray through its **open interior**.
Its status is single R, not RU or RD.

Let S_- be the opposite-side singleton T.
Because it lies wholly in the distant cap

    {x<=-h_-}

and h_->17/24, the sharp
one-square cap center-height theorem gives

    |p_(S_-).y|<1/2.                                (2)

The total vertical projected half-width
of a unit square in any orientation is

    (|cos theta|+|sin theta|)/2>=1/2.

Thus y=0 lies *strictly between* the
bottommost and topmost y coordinates of
S_-. A convex square's open horizontal
section at any ordinate strictly
between its vertical extremes is a
nonempty open interval. Hence

    int(S_-) intersects {y=0}.

All points of S_- have x<=-h_-<0,
so this section lies on the negative
x ray. The square cannot have a U
or D whole-side separator: those would
put it strictly above or below y=0.
Thus its exact status is single L.

The central square C contains zero
openly. In its own side frame the
intersection of its open interior
with y=0 is the interval

    (a-1/2,a+1/2)

since |b|<1/2. The entire S_-
lies at x<=a-1/2, and the entire
S_+ lies at x>=a+1/2, by the two
whole-side hypotheses. Therefore
the three intersections with the
diameter have nonempty **open**
intervals, are pairwise disjoint,
and occur in the precise order

    S_- , C , S_+.

The square labels differ because
the two opposite caps are disjoint.
This proves the claimed three-part
radial-chain skeleton. Reflection
and quarter-turn symmetry cover
every signed central side. QED.

## Consequences for the finite case taxonomy

Every surviving 3+1 opposite-side
count profile, including S1 and S3
of SINGLE_SIDE_SEVEN_BRANCHES.md
and the maximally saturated Types
A/B of SATURATED_SIDE_STATUS_BRANCHES.md,
has this **mandatory geometry** on
its 3+1 axis.

It rules out subconfigurations
that place the far-side singleton
wholly in its upper or lower origin
quadrant, or that attempt to avoid
the diameter with all three
near-side squares. These are
genuine whole-shape exclusions,
not just an assignment count.

The second perpendicular axis
still requires its own pair and
corner-exception analysis.
The present diameter chain alone
does not imply all five sharp
five-corner projected inequalities,
and it does not establish R8>=Rhat.
