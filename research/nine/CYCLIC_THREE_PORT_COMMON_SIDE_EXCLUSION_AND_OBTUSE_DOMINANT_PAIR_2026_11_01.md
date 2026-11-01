# A cyclic three-port exit path has different support sides and one central dominant pair

Date: November 1, 2026 UTC. Complete new hand proof; independent review pending.

## 1. Original scope and conclusions

Keep nine actual closed unit squares with disjoint open interiors in the
same disk about O, with R^2 <= Q = 1105/256, and the unchanged complete
physical positive force-and-torque certificate. Keep every original pair
magnitude, support normal, application or shared-side mean, every physical
circle corner including zero coefficients, and all nine squares. Retain
the compatible selected-certificate hypotheses of the literal physical
K23 theorem and the strict singleton-normal convention used by the
common-side bypass input.

Let K be connected and entirely selected-circle-unloaded, have exactly
three edges in its FULL original positive cut, and have induced cycle
rank at least one. Use the already proved distinct-exit and no-transmitted-
exit theorems. The three cut edges are therefore at three different actual
hubs E={A,B,C}, one at each, and contain no internal exit-arm bodies.

Assume the DIRECT original positive graph on E is exactly the path A-B-C.
There can be other original internal edges, transmitted channels and
arbitrary full degrees. Let p be the original AB application, q the
original BC application, and n_1,n_2 their outward support normals at B.

**Theorem 1.** The actual p and q cannot belong to one common closed side
of B. In particular n_1 dot n_2 <= 0.

**Theorem 2.** Name the larger of the two original direct-pair magnitudes d
and the other e, so 0<e<=d. Then e/d<3/40. For the d-pair, distinguish the
original exit at each of its two endpoints. If r_1+r_2 is the sum of ALL
other original incident magnitudes, excluding that pair and those two
exits, then

    (r_1+r_2)/d < 3/40.

Its original shared application p_d satisfies

    |p_d| < 39/40,
    dist(p_d,Z) < 239/120 < 2

for every actual square Z in the packing.

These are whole-feature exclusions and necessary geometric restrictions.
They do not assert that every surviving module has a full-cut lower bound
dist(p_d,Z)>=2. In particular the third exit hub is positively adjacent
to an endpoint of the d-pair; its original weak edge remains present.

## 2. Exact previously proved inputs

The distinct-exit and original channel bookkeeping are in
`THREE_PORT_CYCLIC_DISTINCT_EXITS_AND_FORCE_CONCENTRATION_2026_10_31.md`.
The entire no-transmitted-exit theorem is in
`CYCLIC_THREE_PORT_UNLOADED_MODULES_HAVE_NO_TRANSMITTED_EXIT_2026_10_31.md`.
Their complete original work estimate, with total internal reduced-channel
magnitude W, internal transmitter work N, and total cut magnitude C_0, is

    W+N < (31/60) C_0.                              (1)

The exact common-side bypass input is
`ONE_SIDE_BYPASS_APPLICATIONS_EXCLUDE_TWO_UNLOADED_THREE_FORCE_CHANNEL_ENDPOINTS_2026_10_31.md`.
It excludes the actual graph A-U-C with U unloaded of full degree two,
A and C unloaded with full stars {U,B,Z_A} and {U,B,Z_C}, and their
actual AB/BC applications on one closed B side. B's full degree and load
are arbitrary. It retains both original exit neighbors and every mean.

Two inherited physical facts are used at their exact original scopes:

- `GENERAL_OCCUPIED_CROSS_NINE_UNIT_EXCLUSION.md`, Section 7, excludes a
  literal actual positive K23; a merely reduced subdivided K23 is not enough.
- `UNLOADED_THREE_FORCE_TOUCHING_RETURNS_STRICT_SUPPORT_SEPARATION.md`
  excludes an unloaded true-degree-three body whose actual three neighbors
  contain two physical contact edges. This is the selection-free diamond
  consequence, not a shortened equation at a higher-degree body.

The localization estimate below is a new, slightly wider constant version
of `DOMINANT_UNLOADED_CONTACT_PAIR_IS_CENTRAL_2026_10_31.md`; its changed
constants and the full application are proved here.

## 3. A terminal disk of radius one half and all singleton equality cases

Here is the elementary full-region work fact used in the common-side proof.
Let L be any nonempty connected unloaded region, with nonempty FULL positive
cut, whose actual terminal squares all meet one closed disk of center x_0
and radius rho<=1/2. For each cut edge choose a point of its terminal in
that disk; different cut edges may use different terminal points.

For its original outward cut normal u from an inside square i, the original
support relation implies

    u dot(c_i-x_0) <= rho-h_i(u) <= rho-1/2.

Dot every complete translation at i with c_i-x_0 and sum. The original
internal support work I_L is nonnegative, and the complete cut magnitude
C_L is positive. All internal pairs and all cut edges are retained. Thus

    I_L <= (rho-1/2) C_L <= 0.                      (2)

If L has an internal positive edge, its support work is strictly positive,
contradicting (2). At rho=1/2 a singleton requires a separate argument;
it is not ruled out by (2) alone.

Suppose now that p,q lie on one closed side of B. Their midpoint x_0 and
radius rho=|p-q|/2<=1/2 give a disk meeting all of A,B,C: it contains p in A,
q in C, and x_0 in B. Remove E only as a choice of vertices on which to
sum unchanged equations. Every positive component L of K minus E has its
full cut to E: all three original outside edges were direct at E.

Equation (2) shows that each such component is a singleton. If its vertex
has full degree at least three, its entire positive neighbor set is exactly
A,B,C; there cannot be more than three different neighbors in E. The
original AB and BC contacts give two edges among those neighbors, contrary
to the unloaded true-three diamond consequence. Full degree one is also
impossible by unloaded translation balance.

Thus every remaining singleton U has genuine full degree two. Its two
neighbors cannot be A,B or B,C: full two-force translation and torque give
opposite supports of positive width at least one between those two terminal
squares, whereas those terminals physically touch. The only possible pair
is A,C.

Two distinct such singletons U,V, together with B, would be three actual
common positive neighbors of A,C. This is a literal K23 with parts
{A,C} and {B,U,V}, excluded by the physical same-nine cross theorem.
There is consequently at most one singleton. There must be at least one,
since E alone has just the path AB,BC and cycle rank zero.

The only possible remaining graph is therefore K={A,B,C,U}, with the
original four-cycle A-B-C-U-A and one direct outside edge at each of
A,B,C. The full stars of A,C are exactly {B,U,Z_A} and {B,U,Z_C}.
Apply the complete common-side bypass theorem cited in Section 2 to these
same actual stars, p,q, and U. It excludes this last singleton equality
case. This proves the common-side assertion of Theorem 1.

For completeness, if two unit support normals of a square have positive
dot product, their supporting faces are contained in one common closed
side. In square coordinates, a strict quadrant of normals exposes one
vertex, while each axis normal exposes its full side. Two directions
separated by less than a right angle either expose one vertex or adjacent
vertices, or one side and one of its endpoints. Opposite vertices, two
different full sides, and a side with a nonincident vertex require an
angle at least a right angle. This covers axis endpoints as well as all
strict vertex cones, and preserves arbitrary side means. Thus
n_1 dot n_2>0 would put p,q on one side, already excluded. Theorem 1 follows.

## 4. Obtuse exit forces make one original pair dominant

Relabel the path ends if necessary so AB has magnitude d and BC magnitude
e<=d. At each exit hub take the full sum of magnitudes of its OTHER internal
channel incidences, excluding these two direct pairs. Let their total over
A,B,C be J>=0. An internal reduced channel with both endpoints in E,
other than the two displayed direct pairs, must contain an original
transmitter; otherwise it would be a third direct E edge or a duplicate
body pair. Its two incidences in J are paid by its contribution to W+N.
A channel with just one E endpoint is paid by W alone; channels with no
E endpoint contribute nothing to J and remain nonnegative in W+N. Hence

    W+N >= d+e+J.                                  (3)

The complete translations at A and C bound their respective exit magnitudes
by d plus A's other internal incidences, and e plus C's. At B, Theorem 1
gives n_1 dot n_2<=0, so the resultant of its two direct internal forces
has magnitude at most sqrt(d^2+e^2). Retain all its other incidences in J.
Summing these three triangle inequalities gives

    C_0 <= d+e+sqrt(d^2+e^2)+J.                    (4)

Combining (1), (3) and (4), with their strict work sign, yields

    29(d+e+J) < 31 sqrt(d^2+e^2).                 (5)

Put x=e/d, where 0<x<=1. Dropping only the nonnegative term J in this
necessary inequality and squaring gives

    120(1+x^2)-1682x > 0.                         (6)

The left side is strictly decreasing on [0,1], and at x=3/40 it equals
-219/40<0. Thus x<3/40.

For the actual AB pair, distinguish its original cut force at A and B.
The remaining incident magnitude sum is exactly e plus the other A/B
internal incidences. It is at most e+J. Equation (5) therefore gives

    (r_A+r_B)/d <= (e+J)/d
       < (31/29)sqrt(1+x^2)-1
       < (31/29)sqrt(1609)/40-1 < 3/40.          (7)

The last comparison is exact: 31^2*1609=1546249 is strictly less than
1247^2=1555009, and 1247=29*43. No weak channel or positive incidence was
removed from an equilibrium equation. This proves the force part of
Theorem 2.

## 5. A complete localization estimate at the wider constant 3/40

We prove a local statement applying to any actual unloaded direct pair of
magnitude d, original normal n from A to B, original common application p,
and one distinguished other original force at each endpoint. Suppose all
remaining incident magnitudes satisfy (r_A+r_B)/d<3/40. No cut or graph
assumption is needed in this section.

At A write z,u,q for the distinguished force magnitude, outward normal
and actual application, and put t=r_A/d. Complete translation gives
|dn+zu|<=r_A and z>=d-r_A. For delta=|u+n| the exact identity

    |dn+zu|^2=(d-z)^2+dz delta^2

therefore gives delta<=t/sqrt(1-t). Since t<3/40,

    delta <= sqrt(40/37)t < (26/25)t,            (8)

with both zero at t=0; the rational square comparison is 25000<25012.
Complete torque about the SAME p, retaining every remaining force, gives

    |det(q-p,u)| <= sqrt(2) r_A/z
                      <= (99/70)(40/37)t.       (9)

Every term's application is in the same unit square A, whose diameter is
sqrt(2). The estimate includes arbitrary shared-side means and endpoints.

If p supports a unit square maximally in direction n, then p-n belongs
to that square: in each own coordinate subtracting the corresponding
component of a unit vector stays in [-1/2,1/2]. The analogous minimum
support fact puts q+u in the distinguished neighbor. Write

    q-p=s u+v Ju,   lambda=1-u dot n.

The maximum-u property of q and p-n in A give s>=-u dot n and
0<lambda<=s+1. The point

    y=p+[lambda/(s+1)](q+u-p)

is in the original disk by convexity. Moreover

    |lambda u+2n|^2=delta^2(4-3delta^2/4)<=4delta^2.

Equations (8)--(9), including their zero case, imply

    |y-(p-2n)| <= 2delta+|v|
       <= [52/25+396/259]t < (37/10)t

when t>0, with zero error when t=0. The last comparison is the exact
integer inequality 233680<239575 after multiplication by 64750.

Apply the same argument at B with its original normal -n and the same p.
It gives two disk points and nonnegative errors epsilon_A,epsilon_B with

    |p-2n|<=R+epsilon_A,   |p+2n|<=R+epsilon_B,
    E:=epsilon_A+epsilon_B < (37/10)(3/40)=111/400.

Squaring, adding and dividing by two, then using R<25/12, gives

    |p|^2 < Q-4+(25/12)(111/400)+(111/400)^2/2
          =298571/320000
          <304200/320000=(39/40)^2.               (10)

Every actual center c_Z satisfies |c_Z|<91/60 by its farthest-corner
inequality |c_Z|^2+|c_Z|+1/2<=Q; substituting 91/60 has strict reserve
31/57600. Each unit square contains its concentric closed radius-1/2 disk.
If p is outside that smaller disk, it follows that

    dist(p,Z) <= |p-c_Z|-1/2
                 <39/40+91/60-1/2=239/120<2.

If p is inside it, the distance is zero. This proves the complete wider
localization theorem and finishes Theorem 2 through (7).

## 6. Exact remaining obligation

The direct exit path cannot be treated as a single-edge exit graph. Its
weaker positive edge e is still present and joins the third exit hub to
the dominant pair. For that reason, the earlier neighbor-set summation
I_L>=z need not apply after removing the dominant pair. The new upper
distance bound alone is not a contradiction. Any later use must derive
the required lower bound from the original FULL region and cut.

The literal direct triangle, and the path with applications on different
sides and obtuse or perpendicular B normals, keep their other original
obligations. No new original coarse/fine flag follows solely from this
manuscript. All constants and graph steps above are hand derivations;
no mathematical program, numerical pose search, Lean or CI is used.
