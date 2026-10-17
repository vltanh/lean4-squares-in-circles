# Gate 3B.2 / M5: exact limits of the four-projection relaxation

2026-10-13. Two completely rational genuine eight-square configurations.
They do NOT disprove the candidate disk radius. They identify what an M5
proof must retain and supply regression targets for the curvature theorem
in `GATE3B_M5_OBLIQUE_CHAIN_CURVATURE.md`.

## 1. The two conclusions

**Four-strip no-go.** There are eight interior-disjoint unit squares of
actual maximum orientation-window count five, satisfying all full-square
support inequalities

    |u_k dot p_i|+H_i(u_k) < 13*(191/100),
    u_k=(12,5),(5,12),(-5,12),(-12,5).

Here H_i is the true projected half-width of square i and |u_k|=13.
Since 191/100<79/40, these strips are narrower than those at the proved
lower endpoint for the sharp five-corner family radius. Thus even actual
pair geometry, exact M5 maximality, canonical owners, simultaneous order
realizability, and ALL FOUR full-square strips do not exclude M5 below
the target radius. The missing condition is genuine disk containment.

The witness is therefore a counterexample to a projection-only exclusion
strategy, NOT to the true disk theorem. Any valid consequence of just
those relaxed hypotheses must admit it.

**Radius-two shortcut is false.** A second genuine M5 packing fits in
squared disk radius 397/100<4. It still does not fit under the research
ceiling 9789/2500. Consequently a proposed stronger claim that every M5
packing has radius at least two would also be false.

## 2. Exact common frames

Index squares from 0 through 7. Set z_i=N_i/10^12, with

    N=(0, 1000000, 414211219229, 414212390801,
       414212976588, 414214148160, 414215319735, 999997000004).

Their genuine orthonormal frames are

    e_i=((1-z_i^2)/(1+z_i^2), 2z_i/(1+z_i^2)),
    f_i=(-e_i.y,e_i.x).

Each square is p_i+[-1/2,1/2]e_i+[-1/2,1/2]f_i. There are no rounded
trigonometric values in these definitions.

The exact closed 45-degree window counts at the eight actual frames are

    (5,5,5,5,4,4,4,4).

All folded positions are distinct and the generic folded word is
LHLHLHLL, so both witnesses are in M5-I itself, not just its closure.
Counts are checked by rotating direction pairs through dot/cross products
and testing whether the first-quadrant direction satisfies x>=y.
Folding a high direction by 45 degrees replaces (x,y) by (x+y,y-x), so
all these comparisons are rational as well.

## 3. Exact centers

In each column below multiply every listed integer pair by

    (10001/10000)/10^6.

This dilation changes centers only, not unit side lengths.

| i | Four-strip witness center numerator | Disk-below-two witness center numerator |
|---|---|---|
| 0 | (-61276,144607) | (-55267,9560) |
| 1 | (-500001,1144607) | (-500000,1222109) |
| 2 | (-973545,-913494) | (-1025488,-895564) |
| 3 | (973543,-913495) | (1051313,-921389) |
| 4 | (-1268382,205881) | (-1264568,279570) |
| 5 | (-1,-1354166) | (0,-1284290) |
| 6 | (1268382,205880) | (1264568,279570) |
| 7 | (500001,1144607) | (500000,1222109) |

## 4. All 28 genuine pair separators, with a common strict reserve

For each i<j the following signed axis works for BOTH configurations.
Entries on row i correspond to j=i+1,...,7. A symbol +e_k, for example,
means the actual rational unit direction e_k, directed from i to j.

| i | Signed actual axes for successive j>i |
|---|---|
| 0 | +f1, -e2, -f3, -e0, -f0, +e0, +e7 |
| 1 | -f1, -f3, -e4, -f1, -f6, +e1 |
| 2 | +e2, +f2, -f5, +e2, +e2 |
| 3 | +f4, -e3, +e6, +e7 |
| 4 | -f4, -f6, +e4 |
| 5 | +e6, +e7 |
| 6 | +f6 |

Direct substitution of the rational coordinates proves, for EVERY entry,

    n dot(p_j-p_i)-H_i(n)-H_j(n) > 1/20000.

Here H_i(n)=(|n dot e_i|+|n dot f_i|)/2. These are actual square SAT
inequalities, not center-distance surrogates. Thus all closed square pairs
are strictly separated. They admit canonical maximizing owners as well.

## 5. The four-strip inequalities really hold

For the first configuration, all 32 inequalities indexed by i and k obey

    13*(191/100)-|u_k dot p_i|-H_i(u_k) > 9/100.

Hence every ENTIRE square, not only its center, lies strictly in all four
strips. The simultaneous order and path restrictions of Gate 3A are
necessary consequences of the actual canonical owners and are preserved.
There is no incompatible independent assignment of four projected orders.

Nevertheless a true vertex has squared norm greater than 21/5. In
particular this configuration is not in the disk of radius 191/100, in
the candidate disk, or under the research disk ceiling.

## 6. Actual vertex norms, independently of strip bounds

For a square of center p and frame (e,f), its maximum vertex squared norm
is exactly

    (|p dot e|+1/2)^2+(|p dot f|+1/2)^2.

The following terminating decimals are rational OUTWARD bounds, not
floating-point estimates; each row follows by substituting the fractions.

| i | Four-strip witness: maximum squared norm lies in | Disk-below-two witness: maximum squared norm lies in |
|---|---|---|
| 0 | (0.7305,0.7306) | (0.5679,0.5680) |
| 1 | (3.7052,3.7053) | (3.9661,3.9662) |
| 2 | (3.6595,3.6596) | (3.8044,3.8045) |
| 3 | (3.6595,3.6596) | (3.9415,3.9416) |
| 4 | (3.9454,3.9455) | (3.9661,3.9662) |
| 5 | (4.2494,4.2495) | (3.9661,3.9662) |
| 6 | (3.9454,3.9455) | (3.9661,3.9662) |
| 7 | (3.7052,3.7053) | (3.9661,3.9662) |

Thus the second configuration has all 32 vertices within squared radius
397/100<4, while some are outside squared radius 99/25>9789/2500.
Convexity of the disk gives containment of the whole eight squares in
radius sqrt(397/100). Both conclusions in Section 1 follow.

## 7. Curvature resolves this particular obstruction, not all M5

Both configurations contain the seven canonical chains in
`GATE3B_M5_OBLIQUE_CHAIN_CURVATURE.md`, with A=1, B=7, H=4, L=2, D=5,
R=3, E=6. Their required frame deviations and canonical-normal deviations
are at most 1/200 radians. The exact audit proves this via the sufficient
rational test dot>0 and |cross|<=(1/200)dot against each reference direction;
then |angle|=arctan(|cross|/dot)<=1/200.

That hand theorem proves an ALL-CENTERS squared-radius bound greater than
3.920008 for every packing in this separator/frame family, above the
research ceiling. Therefore it excludes the full stated family using
the circle, even though the four strips cannot do so.

The canonical chain and near-reference frame conditions are not proved
for all M5-I or M5-II configurations. The unrestricted M5 exclusion and
Gate 3B.2 remain open.

## 8. Discovery versus proof

An exploratory full-eight-square SLSQP calculation on the closed M5-I and
M5-II domains suggested the second geometry. A fixed-owner linear strip
optimization suggested the first. Those floating-point runs are not
certificates and their small negative residuals are not ignored.
The rounded and dilated rational data above are separately checked from
scratch. `verify_m5_four_strip_counterexample.py` was executed locally
using Fraction arithmetic only: all 32 vertices, all 28 true pair SAT
inequalities, all full-square strips, actual M5 counts, the canonical
chain hypotheses, and the rational constants in the curvature proof.

The continuous curvature exclusion is the analytic argument in its
companion note, not an inference from these two examples or a PASS flag.
