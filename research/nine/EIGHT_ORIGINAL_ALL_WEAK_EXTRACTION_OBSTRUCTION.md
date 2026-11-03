# An eight-original obstruction to promoting a weak-chain witness

November 3, 2026. Exact hand argument. This is a statement about eight
physical squares, not a counterexample to any nine-original mask.
It changes zero mask, original-cell, or roadmap statuses.

## Explicit physical packing

Take eight axis-aligned unit squares with these centers in the original
physical coordinate system (X,Y):

| Label | X | Y |
|---|---:|---:|
| A | -1 | -19/24 |
| B | -1 | 5/24 |
| C | 0 | 5/24 |
| D | 1/2 | 29/24 |
| E | 0 | -19/24 |
| F | 1 | -19/24 |
| G | 1 | 5/24 |
| H | -1/2 | 29/24 |

The bottom and middle rows each have three centers spaced by one; the
top row has two centers spaced by one. Distinct rows are separated by
at least one vertically. Consequently all 28 pairs have disjoint open
interiors, including the allowed touching boundaries.

For the bottom row, every squared corner norm is at most

    (3/2)^2+(31/24)^2 = 2257/576.

For the middle row the corresponding bound is 1585/576. For the top row,
the bound is

    1+(41/24)^2 = 2257/576.

Thus all eight squares fit below the sharp target, with exact slack

    Q-2257/576 = 1105/256-2257/576 = 917/2304 > 0.

## An exact 111/11 witness and failure of the 001 geometric conclusions

Use witness axes e=(1,1)/sqrt(2), f=(-1,1)/sqrt(2), and select the main
chain A,B,C,D and short chain E,F,G. Every physical square has witness
halfwidth h=1/sqrt(2) and inset halfwidth g=1/(2sqrt(2)). The five
consecutive center differences in witness coordinates are

    AB = (1,1)/sqrt(2),
    BC = (1,-1)/sqrt(2),
    CD = (3/2,1/2)/sqrt(2),
    EF = (1,-1)/sqrt(2),
    FG = (1,1)/sqrt(2).

All are center-cone comparisons. Every horizontal gap is strictly less
than 2h=sqrt(2), so the marked mask is exactly 111/11. H is an additional
physical original outside the selected seven.

The normalized CD transverse gap is positive but equals
1/(2sqrt(2))<2/3. Moreover

    y_G = -19/(24sqrt(2)) < 17/(24sqrt(2)) = y_D,
    x_F = x_C = 5/(24sqrt(2)) > 0,
    y_F = -43/(24sqrt(2)) < 5/(24sqrt(2)) = y_C.

Thus the low-gap exclusion, G-above-D order, and C bottom exclusion
used in the original 001/00 proof do not transfer to this eight-original
111/11 relaxation. These are actual physical squares, so all universal
pair-distance, inset-distance, and orientation-dependent support
inequalities are satisfied.

## No frame admits even one actual link in a cone four-chain

For any unit witness axis e=(p,q), all eight physical squares have the
same halfwidth h=(|p|+|q|)/2, with 1/2<=h<=1/sqrt(2). Their centers lie
in a rectangle of horizontal and vertical side length two. Hence their
total center-projection span is at most

    2(|p|+|q|)=4h.

Every center-cone link has horizontal gap at least 2g=1/(2h), by
physical disjointness of its original aligned insets. If any consecutive
link of a four-chain were actual, its three gaps would therefore have
total at least

    2h+1/h >= 4h.

The inequality is strict unless h=1/sqrt(2). At that equality value e is
a diagonal direction. In either diagonal direction the explicit centers
have projection span exactly 7/(2sqrt(2)), strictly less than
4h=2sqrt(2). Thus the equality case is impossible too.

Consequently every cone four-chain of this eight-square packing, in
every frame and with every original relabeling, has main mask 111.
In particular there is no relabeling/rotation into 001/00, its reversal,
or any of the already closed outer-actual masks.

The ninth original is therefore essential to any global stronger-chain
extraction that would remove this obstruction. This note neither adds
that ninth square nor asserts that an arbitrary nine-square caller
forces a common orientation or the displayed bounding rectangle.
