# Root review of the uniform opposite-port gap and complete C6 pocket-2 join

Date: October 26, 2026.

**Verdict: PASS for the complete geometric gap theorem and the whole
original pocket-2 capacity-one join.** I read both full saved sources,
`RADIUS_TWO_OPPOSITE_PORT_INNER_ARC_GAP.md` and
`SIX_CYCLE_REMAINING_CAP_2_CAPACITY_ONE.md`, together with the actual
channel conventions, accepted sharp arc theorem, channel-2 height,
and full crosscut routing in `RADIUS_TWO_SIDE_CHANNEL_CAPACITY_TWO.md`.
No unrestricted nine-square closure is inferred from this capacity
argument by itself.

## 1. Whole scalar domain and strict projection reserve

The proof retains every ordered own coordinate a>=b>=1/2,
79/40<=R<=2, including b<1. For fixed R^2, a+b is minimized
at b=1/2. The resulting upper bound on the opposite-port norm
is strictly below the squared inner-circle radius. Also a>5/4.
Thus the claimed inner-face crossing t is strictly between a-1
and a, with no extension-of-side or sign ambiguity.

I independently differentiated the function f. Its second derivative
is exactly (uU+vV)/rho with the displayed U,V. The three whole
interval estimates use the correct signs of w and w(w+1).
In the negative interval, the w-multiplied difference in V is
nonnegative. In the two positive intervals, all discarded terms
are nonnegative and every denominator comparison has the required
direction. This gives U>-1/5,V>1/2, hence f''>19/125>3/20.

I recomputed the exact U/V rational reserves independently:

    23186977239/9440026073120,
    2611/23040, 331/13824,
    59903451/566100920, 20477343/81746504.

The comparison to R=79/40 is valid because the coefficient
(u*t-v*w)/rho of a is strictly positive on the entire interval.
The comparison a need not remain at least b, and the derivative
proof correctly covers its larger scalar domain.

I reconstructed the fixed tangent at w=1/8 and recomputed its
rational reserves 265131/625000000,
37584071/84057875000 and 662757413/18038000000.
The integrated curvature bound is valid on both sides of the
tangent and gives f>1/2+11/3000 throughout the full interval.

For the angular endpoint pi/2, I rederived the derivative of F.
For w<=0 both contributions have the required negative sign.
For w>=0 the source's multiplication reduces its negative to
t^2-a*w>0. The diagonal comparison then increases with R and
has the stated independent fixed reserve 269/312500.
For G<0 the angular projection increases; for G>=0 it is concave.
These two exhaustive sign alternatives prove the full angular
inequality, without assuming b>=1 or using sampled inequalities.

## 2. Actual ports and actual interval

Dotting P=(a-1,w) with Q=(t,w) and its own perpendicular gives
exactly F and G. The opposite own-frame orientations of the two
physical endpoints account for the opposite signs of their JQ
terms. After centering the actual free interval about the upward
direction, the horizontal port separation is the sum of the two
displayed projections. A gap at least4asin(2/5) would therefore
force separation greater than one, contradicting the original
reserve-one channel. The argument uses its actual gap shorter
than pi, not an arbitrarily selected complementary interval.

## 3. Full C6 physical join

I checked the canonical chi=(1,1,0) applications directly: p0^- and
p2^+ are both actual opposite vertices, and their exact difference
is n2. The physical S0 ordering a>b follows from its actual shared
chord. The S2 ordering L2>K2 is separately proved by dotting the
unchanged torque vector with v2; its right side
p(c1*N+s1*M) is strictly positive. No axis interchange is used
to force the needed face order.

At both facing circle points the large own coordinate exceeds5/4,
and the opposite port lies strictly inside that circle. Their
intersections are therefore actual points of the indicated inner
faces. The actual outward normal has positive product with both
large-coordinate axes, so both circle points have height greater
than the real positive channel height. The relevant outward arc
is consequently shorter than pi.

The connected endpoint intervals and their radial-center points
are supplied by the whole boundary-unit intersection formulas in
ANNULAR_CENTER_ARC_AT_23_25.md, as used in the accepted complete
side-channel routing theorem. The determinant signs identify which
facing endpoint starts or ends each interval. Their physical order
cannot reverse without overlapping occupied open arcs.

Every whole pocket extra is in the actual H2>1/4 cap. The occupied
crosscut, with its full compact-interior weak-limit argument, routes
each extra's entire connected inner-circle arc between the same
endpoint intervals. The generic gap theorem applies to that actual
interval. The sharp arc length then excludes two extras. All
circle masks, individual zero-weight endpoints, genuine means,
actual transmitter sliders and nine physical units remain.

Thus this analytic route leaves only the simultaneous allocation
(central,cap0,cap2)=(1,1,1). It does not alone eliminate that
allocation, close the original parent or classify equality.
No coefficient packet, numerical physical sample, Lean compilation,
CI or workflow dispatch was used in this audit.
