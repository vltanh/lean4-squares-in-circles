# An exact obstruction to the proposed one-third main-height strengthening

November 2, 2026. This six-square configuration disproves the proposed
local implication that a lower side outsider, even with a second upper
side outsider, forces its inner main above -1/3. It is not a nine-square
packing and does not challenge the target packing theorem. Its purpose is
to prevent that unsupported stronger local gate from entering the proof.

Put

\[
 r=\sqrt{901},\quad a=30/r,\quad b=1/r,\quad h=31/(2r),
 \qquad\lambda=1000001/1000000.
\]

The clockwise frame is the orthonormal pair (a,-b),(b,a). An aligned
frame is (1,0),(0,1). Take the following six original unit squares, and
multiply every listed center coordinate by lambda while keeping every
frame fixed.

| Original unit | Center before the common expansion | Frame |
| --- | --- | --- |
| M0 | (-1-h,0) | Aligned |
| M1 | (-1/2,-67/200) | Clockwise |
| M2 | (h,0) | Aligned |
| M3 | (1+h,0) | Aligned |
| L | (-1/2,7/10) | Aligned |
| B | (-29/60,-2673/2000) | Clockwise |

Before expansion, the three main horizontal center gaps equal their
projection-halfwidth sums. After expansion every main gap is strictly
greater than that sum. Each consecutive main displacement also lies
strictly in the horizontal cone. The two original side outsiders L,B
have x<-29/60 after expansion, and they lie respectively above and below
the same original M1.

Every original corner is strictly inside the disk of squared radius
1105/256, and every pair of the six closed squares is strictly separated.
The exact check retains all frames and corners. It gives a uniform
squared-circle reserve greater than 1/100000 and a uniform physical
separator reserve greater than 999/1000000000, including the three actual
main links. Meanwhile

\[
                     y_1=-\lambda\,67/200<-1/3.
\]

The standard-library checker `verify_lower_side_third_obstruction.py`
verifies all 24 original corners and all 15 original pairs with Fraction
interval arithmetic and outward 80-bit radicals. It additionally checks
the three actual main edges, their cone comparisons, the two side
positions and vertical orders, and the displayed strict reserves. Its
report is `lower_side_third_obstruction_replay.json`.

The valid completed replacement is
`LOWER_SIDE_MAIN_SEVENTEEN_FIFTIETHS_HAND_TABLE.md`, which proves the
weaker local lower bound -17/50. This fixture is consistent with that
bound. A stronger conclusion using additional original outsiders would
need their additional constraints explicitly.
