# Translated four-square junction capacity: two completing centers per axis

Date: October 30, 2026 UTC.

**Status: complete proposed force-free family theorem, awaiting
independent review. Earlier frozen junction sources are unchanged.**

This extends the central-junction capacity theorem to a substantially
larger region. It allows a cap to contain two centers and uses the
opposite cap's disappearance to preserve the total count. The result
also gives a necessary height for any four-square junction at the
middle mean of a genuine long channel in a nine-square packing.

## 1. General translated region and useful full boxes

Let actual unit squares have pairwise disjoint open interiors and lie
in the disk centered at O of squared radius at most Q=1105/256.
Suppose four actual squares meet at one point p. Their four local
interior sectors have angle at least pi/2 and total angle at most
2*pi. Thus all four are vertex sectors, their frames agree up to
quarter turns, and their union in that common frame is exactly

    B=[p_x-1,p_x+1] x [p_y-1,p_y+1].                    (1)

Put

    M=91/60, P=|p_x|, T=|p_y|.

**Theorem 1 (translated-junction capacity region).** If

    P,T <=5/16,                                         (2)
    (1-P)^2+(1-T)^2+1-max(P,T)+1/4 >= M^2,              (3)

then the entire actual packing contains at most eight unit squares.
The other units have arbitrary independent orientations and need no
stress or contact relation to the block.

The theorem includes each of these whole closed parameter boxes:

    |p_x|,|p_y|<=1/5;                                   (4)

and

    |p_x|<=1/20, |p_y|<=5/16,                            (5)

as well as the coordinate-swapped version of (5). The bounds are in
the actual common square frame, without translating the disk center.

## 2. Center bounds and clearance from the actual block

For any contained unit square with center c and orthonormal side axes
u,v, its farthest actual corner has squared norm

    |c|^2+1/2+|c.u|+|c.v| >= |c|^2+|c|+1/2.

Since

    M^2+M+1/2-Q=31/57600>0,

all actual centers satisfy

    |c|<M.                                              (6)

The open radius-1/2 incircles of distinct physical units have disjoint
interiors, so their centers are at distance at least one.

If E is outside the four block squares, its incircle avoids int(B).
Any nonempty open intersection with int(B) would contain a point off
the block's internal seams and would overlap an original block-square
interior. Hence

    dist(c_E,B)>=1/2.                                    (7)

This includes all closed boundary contacts: a point of B at distance
less than 1/2 would have nearby points of int(B) in the same incircle.

## 3. No completing center escapes diagonally around a block corner

Suppose a completing center c is outside both coordinate intervals
of B. Write

    |c_x-p_x|=1+s, |c_y-p_y|=1+t, s,t>0.

Equation (7) gives s^2+t^2>=1/4 and therefore s+t>=1/2.
Since P,T<=5/16<1, the reverse triangle inequality gives

    |c_x|>=1-P+s, |c_y|>=1-T+t.

Put a=1-P and b=1-T. These numbers are positive. Then

    |c|^2 >= (a+s)^2+(b+t)^2
           >=a^2+b^2+2*min(a,b)*(s+t)+s^2+t^2
           >=a^2+b^2+min(a,b)+1/4
           >=M^2,                                       (8)

where the last step is exactly (3). This contradicts the strict
center bound (6), including equality in (3).

A center inside both coordinate intervals also contradicts (7).
Consequently each completing center is outside precisely one of
the two closed coordinate intervals. If it is outside horizontally,
then (7) says

    |c_x-p_x|>=3/2.                                     (9)

The analogous vertical alternative is

    |c_y-p_y|>=3/2.                                     (10)

Thus actual centers are covered by four side caps, and no omitted
corner region requires an extra capacity allowance.

## 4. Two center-cap estimates

### 4.1 A deep cap contains at most one center

In a cap x>=89/60, |c|<M, all coordinates satisfy

    89/60<=x<M,
    |y|<sqrt(M^2-(89/60)^2).

Its squared diameter is at most

    (M-89/60)^2+4*(M^2-(89/60)^2)=361/900<1.            (11)

It therefore contains at most one actual unit center. Reflection
and coordinate interchange give the same conclusion for every
directional cap at this depth.

### 4.2 A shallower cap contains at most two centers

Consider x>=19/16, |c|<M. Split it into the part with y>=0 and the
part with y<0. Each part has coordinate ranges of lengths at most

    M-19/16 and sqrt(M^2-(19/16)^2),

so its squared diameter is at most

    (M-19/16)^2+M^2-(19/16)^2
       =2*M*(M-19/16)
       =7189/7200 <1.                                  (12)

The exact reserve is 11/7200. Each half therefore contains at most
one actual center, and the cap contains at most two. Assigning its
y=0 points to the nonnegative half handles the splitting boundary
without duplicating or losing a center. The same statement holds
in every reflected or rotated direction.

## 5. At most two completing centers per coordinate axis

Consider the horizontal alternatives in (9), and put d=|p_x|.
Reflection allows p_x=d>=0 for this count. The two caps are

    c_x>=3/2+d,
    c_x<=-(3/2-d).                                      (13)

There are two exhaustive cases.

If d<=1/60, both cap depths are at least

    3/2-1/60=89/60.

Each cap then has capacity one by (11), for a total at most two.

If d>=1/60, the positive cap is empty, because

    3/2+d>=91/60=M

contradicts (6). By (2), the other cap has depth at least

    3/2-d>=3/2-5/16=19/16.

It has capacity at most two by (12). This again gives at most two
horizontal completing centers. The common boundary d=1/60 satisfies
both arguments and creates no exception.

Apply the identical reasoning vertically, using T<=5/16. There are
at most two vertical completing centers. Section 3 covers every
additional unit by one of these two axis groups. Therefore there
are at most four additional units and at most eight units in total.
This proves Theorem 1.

## 6. Exact checks of the two whole parameter boxes

For the symmetric box (4), a,b>=4/5, so the expression in (3) is
at least

    2*(4/5)^2+4/5+1/4=233/100
                             =M^2+107/3600>M^2.         (14)

For the asymmetric box (5), a>=19/20, b>=11/16 and
min(a,b)>=11/16, so the same expression is at least

    (19/20)^2+(11/16)^2+11/16+1/4
       =M^2+713/57600>M^2.                              (15)

Both boxes satisfy (2), so each is included in the complete region.
These are whole closed-box corollaries, not a finite sample of
translations. Condition (3) also permits further translations
outside those displayed boxes.

## 7. A necessary height for a long-channel middle junction

Consider a genuine long force-and-torque channel A-U-V-B with two
unloaded true-positive-degree-two internal bodies and original middle
mean p. Its complete straight-line theorem is
`LONG_CHANNEL_OUTER_STRIP_EXCLUSION_AND_STRAIGHT_LINE_BARRIER_2026_10_30.md`.
In the actual long-normal frame it gives

    p=(s,t), |s|<1/60, |t|<=9/16,                        (16)

and both internal squares have the long normal as a side axis.
Suppose this actual middle mean is also a common point of four
physical squares. Their common block frame is therefore the same
long-normal frame, up to signs and coordinate interchange.

If |t|<=5/16, then (16) lies in the asymmetric box (5), and the
whole packing has capacity at most eight. Consequently, in a
nine-square packing such a middle four-square junction necessarily
obeys the strict band restriction

    5/16<|t|<=9/16.                                     (17)

This conclusion retains every original completing square and uses
no assumption about its force or its side of the original line.
The endpoint degrees, actual means and masks remain unchanged.
The force-free Theorem 1 itself has no channel hypothesis.

The record geometry is preserved: the four aligned central/upper
units with centers (±1/2,1/16),(±1/2,17/16) meet at

    p=(0,9/16).

Together with outer units (±3/2,1/16) and the three lower units
(-1,-15/16),(0,-15/16),(1,-15/16), they give nine units at Q.
Thus a blanket capacity-eight claim for every translated junction,
or for every long-channel middle junction, would be false. The
remaining one-axis band in (17) still needs a sharp Q-bound argument.

## 8. Verification boundary and frozen channel input

The principal theorem is self-contained apart from elementary
Euclidean convex geometry and the exact farthest-corner formula.
All cap and translation comparisons are displayed rational
identities, with strict positive reserves where stated.

The only imported input for the optional channel corollary is:

| Source | SHA256 |
| --- | --- |
| `LONG_CHANNEL_OUTER_STRIP_EXCLUSION_AND_STRAIGHT_LINE_BARRIER_2026_10_30.md` | `dd1d91f8e49f4a5f507a70b53a75a30b299757f9f04a0976da3e674674ae7b05` |

The earlier one-sixtieth and one-fifteenth junction sources remain
literal unchanged inputs for their existing callers. No numerical
pose search, finite certificate, Lean compilation, CI run, original
ledger mutation or remote publication is asserted here.
