# An axis-aligned eleven-square counterexample below q equals five

The statement that every eleven-square common-coordinate-separable packing has
squared radius at least 5 is false. The accompanying
`AXIS_ALIGNED_COUNTEREXAMPLE.json` gives eleven **axis-aligned** unit squares
with rational centres and an exact squared-radius upper bound 491/100 = 4.91.
This is above the current unrestricted witness bound 49013/10000 = 4.9013,
and the common-coordinate class has already been excluded at that smaller
bound by AXIS_ALIGNED_EXCLUSION.md.

Every centre below has denominator 1000000:

| Label | x numerator | y numerator |
| --- | ---: | ---: |
| 0 | -1220684 | -895857 |
| 1 | -1631706 | 104153 |
| 2 | -220674 | -1595185 |
| 3 | -220674 | -595175 |
| 4 | -631696 | 404835 |
| 5 | -631696 | 1404845 |
| 6 | 779336 | -1308997 |
| 7 | 368314 | 503956 |
| 8 | 368314 | 1507629 |
| 9 | 1369525 | -308987 |
| 10 | 1368324 | 691023 |

The exact verification gives

    maximum of all 44 corner squared norms
        = 981834263569 / 200000000000 < 491/100 < 5;

    minimum over all 55 pairs of max(|dx|,|dy|)
        = 1 + 1/100000.

Consequently all closed squares lie in the claimed disk and their open
interiors are pairwise disjoint. The standard-library script
`check_axis_counterexample.py` checks all those inequalities with rational
arithmetic. The numerical search is not a premise of this witness.

In the fixed unit grid whose cell index is
`(floor(x+1/2), floor(y+1/2))`, the thirteen possible cells consist of the
central 3 by 3 grid and its four outer axial neighbours. The witness leaves
exactly the central cell (0,0) and the east outer cell (2,0) empty. Thus the
centre-plus-outer-arm orbit is a real branch and cannot be discarded by a
bound of 5.

## A useful conditional terminal below the present upper bound

The witness suggests a six-square chain structure with a rigorous lower
certificate slightly above 4.9013. Let A,B,C,D,E,F be six axis-aligned unit
squares in a disk of radius R about the origin. Suppose the following seven
coordinate inequalities have been proved, directly or by telescoping chains:

    x_C-x_A >= 1;       x_E-x_C >= 1;
    x_F-x_B >= 3;       x_F-x_D >= 2;
    y_B-y_A >= 1;       y_D-y_C >= 3;
    y_F-y_E >= 2.

The axis-aligned witness has this structure with A=0, B=1, C=2, D=5,
E=6, F=10. The displayed inequalities are a **conditional contract**. The
cell-hole pattern alone has not been proved to imply them.

Multiply the seven inequalities, in the displayed order, by

    1, 4, 4, 5, 1, 9, 6.

Their right sides sum to 67, and their left sides collect into
`sum_i b_i dot p_i`, where

    b_A=(-1,-1), b_B=(-4,1), b_C=(-3,-9),
    b_D=(-5,9),  b_E=(4,-6), b_F=(9,6).

An axis-aligned unit square at p_i has support
`b_i dot p_i + (|b_ix|+|b_iy|)/2`; disk containment bounds this by
`R ||b_i||`. The six half-width support terms sum to 29. Thus

    96 <= R (sqrt(2)+sqrt(17)+3sqrt(10)+sqrt(106)+5sqrt(13)).

The five rational comparisons

    sqrt(2)   < 1.415;
    sqrt(17)  < 4.124;
    sqrt(10)  < 3.163;
    sqrt(106) < 10.296;
    sqrt(13)  < 3.606

follow by squaring positive rational numbers. They bound the parenthesized
sum by 43.354, which is less than 43.36 = 1084/25. Therefore

    R > 600/271;
    q = R^2 > 360000/73441 > 49013/10000.

The final strict comparison has exact difference
`436267/734410000`. This closes any terminal branch for which the seven
coordinate inequalities are established. The complete extraction and case closure are supplied separately by the
exact trace and THREE_AXIS_TERMINAL_LEMMAS.md.

