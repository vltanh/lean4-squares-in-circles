# Independent review: exact low-port cap and the complete lower high-square barrier

Date: October 28, 2026 UTC. Reviewer: review_resume continuation.

## 1. Exact source and full verdict

**PASS.** I read the complete frozen
`HIGH_SQUARE_CHORD_BARRIER_WITH_EXACT_LOW_PORT_CAP.md`
and independently rederived its entire separating-axis cover, continuous
angle estimate, far-corner contradiction, and lower-route extension.
I did not contribute to the proof discovery or motivating roof chart.
No mathematical source was edited.

The source is exactly 8,180 bytes, SHA-256

`4e04f9fd6e9b3bae2206333817744ae0f3e624819eb6ffd125929b973782b18e`,

with Git blob `56fd52416278692ce9e447de9759393e1cd25751`.

The complete accepted theorem keeps the actual unit H

    H=[h-1,h] times [g-1,g],
    h<=epsilon, 69/100<=g<=1,
    R^2=(2+epsilon)^2+1/4<=1105/256,
    0<=epsilon<1/60.

No actual unit B, interior-disjoint from H and contained in that same
circle, can contain points P,V with

    P_x<h, P_y<49/75,
    h-1<=V_x<=h, V_y>=g.

This includes both V abscissa endpoints, V_y=g, g=69/100, g=1,
epsilon=0, and h=epsilon. There is genuinely no unprinted lower bound
on h. P and V can be arbitrary actual points of B, including actual
force applications, unchanged side means, and supporting endpoints.
No positive HB edge, degree, stress, circle load, or physical mask is
a premise.

The complete lower-route theorem is also accepted at these exact new
thresholds. It uses the whole actual A extents and a positive pair
ell0,eta0 with ell0+eta0>sqrt(2), as stated in Section 4 of the
source. This review grants no original graph-family or ledger credit.

## 2. Exact direct sources and the whole-unit cap

Both printed source pins match the unchanged current bytes:

| Direct input | SHA-256 | Exact use |
| --- | --- | --- |
| HIGH_SQUARE_LOW_LEFT_PORT_BARRIER_WITH_SIGNED_SMALL_SUPPORT.md | e2463dea33c2e66b97046c5727562be354e09f3f065e3dc04028e3a79a79dc58 | Section 2's full actual-unit cap; the new separating-axis and corner argument is independently rederived at the lower threshold |
| HIGH_SQUARE_CHORD_BARRIER_WITH_LOWER_ROUTE_LENGTH.md | 11e9eb7ba47bb8e8042aed44536046dba6c98f50961e663986935e0ea41cd9a1 | Predecessor structure only; every actual lower-route position and endpoint is proved again in the new source |

No earlier height threshold is transferred to the new theorem. I read
both complete sources and the operative complete high-strip input in
this independent review sequence.

The high-strip source is
`HIGH_VERTICAL_STRIP_AND_NEAR_EAST_UNIT_CENTER_EXCLUSION.md`, SHA-256
`75def83e3a67168eb28014641ddfa3d53372028514facaab09529903ba6090f8`.
Only its full Section 1 center estimate is used. For an actual contained
unit T beyond x>=1-epsilon it gives

    89/60<(c_T)_x<91/60,
    |(c_T)_y|<3/25.

That proof covers both signs of obliquity, the aligned case, actual far
corners and limiting nonnegative radicands. Its actual directional
width w obeys

    w/2=(c_T)_x-min_T x
       <=(3/2+epsilon)-(1-epsilon)
        =1/2+2*epsilon<8/15.

A unit square has equal widths in two orthogonal directions. Therefore
every actual point of T satisfies

    |T_y|<3/25+8/15=49/75.

This is a bound on the entire unit, including every contact point or
original mean, not merely a center or a circle resultant. Reflection
gives the corresponding whole-unit cap to the left of
x=-(1-epsilon).

The high-strip input's historical center-bound digest is reconciled
without any source edit: current
`END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md` is 8,686 bytes at SHA-256
`20a845eff8bee3e9c533162df0b32ea96f9dd104a3cfec41efb3b0cf92d6e9cf`;
appending exactly one LF produces its printed historical digest
`6f3459eaf4ca425ee2001ddb27e1ba7a1b5eb0003548498f48c610776554d3bb`.
I rechecked this identity. Only that input's force-free Section 1
center estimate is used. No loaded triangle equation or separate
two-unit neighbor exclusion enters the new barrier.

## 3. All physical chord positions and all separating axes

Set A0=1-h>59/60 and U=(-A0,g), the actual top-left H corner.
Suppose P_x>-A0. Then P has abscissa strictly inside H's horizontal
interval and height below 49/75<g. V has abscissa in the closed
interval and height at least g. A point of the unchanged chord PV
just below height g has abscissa strictly inside that interval and
height strictly above g-1. It lies in int H. This includes V at
either horizontal endpoint and V_y=g. Because the entire chord is
in the full actual square B, nearby interior B points would also lie
in int H, contradicting disjoint open interiors. Thus

    P_x<=-A0.

For two actual rectangles with disjoint open interiors, the standard
finite separating-axis statement supplies a weak separating axis owned
by one of them. The Minkowski-difference polygon has only their own-axis
edge normals; separation from its open interior retains the weak case
when the actual rectangles touch. This is a geometric separator and
does not select a new original stress normal.

Every H-owned axis is excluded. P rules out an entire B on the right
or above; V rules out an entire B below. If B were wholly to the left,
its entire x extent would be at most h-1<=-(1-epsilon), and the
complete cap would give V_y<49/75<g. This is impossible too.

For a remaining B-owned separator n directed H-to-B, Northeast is
excluded by P being strictly below and to the left of H's upper-right
corner. Southwest and Southeast are excluded by V being strictly
above H's bottom while inside its closed horizontal strip. All axis
endpoints coincide with the already excluded axis cases. Therefore
the whole possible separator interval is strictly Northwest:

    n=(-s,c), t=(c,s), s,c>0, s^2+c^2=1.

Use these actual own axes to write the entire B as

    B=[k,k+1]n+[ell,ell+1]t,
    H0=U.n=A0*s+g*c,
    T0=U.t=-A0*c+g*s,
    k>=H0>0.

Since P_x<=U_x and P_y<g, while V_x>=U_x and V_y>=g,

    P.t<T0<=V.t.

Both P and V lie in the same actual tangent interval of B. Hence
T0 belongs to that closed interval even when V=U. In particular
(k+1)n+T0*t is an actual far-side point of this same B. No auxiliary
unit, altered contact, or changed force application has appeared.

## 4. Entire continuous separator interval and the first exact reserve

Containment of the actual far-side point gives

    R^2>=(k+1)^2+T0^2
        >=(H0+1)^2+T0^2
         =A0^2+g^2+2*H0+1.

If H0>=15/16, the minimum endpoint comparison already exceeds the
maximum allowed R^2. Its exact reserve is

    (59/60)^2+(69/100)^2+1+2*(15/16)-1105/256
       =2359/1440000>0.

Thus H0<15/16. If s belonged to the entire closed interval [1/3,1],
the concave function

    (59/60)s+(69/100)sqrt(1-s^2)

would have its minimum at an endpoint. At s=1 that value is
59/60>15/16. At s=1/3 it exceeds

    (59/60)/3+(69/100)*(14/15)>15/16.

Both endpoint comparisons are strict, so no direction in that whole
interval survives. Consequently

    0<s<1/3,
    c>9/10,
    T0<-(59/60)*(9/10)+1/3<0.

The last estimate uses the stated g<=1. No angle grid, orientation
sample, or subdivision of a geometric parameter is used. The boundary
s=1/3 was explicitly excluded by the same strict reserve.

## 5. The unchanged far corner and both monotone endpoint substitutions

Put eta=g-49/75, so eta>=11/300>0. The exact coordinate identity
relative to U is

    P_y-g=c*(P.n-H0)+s*(P.t-T0).

The first term is nonnegative because P.n>=k>=H0. Since P_y<49/75,
the entire actual tangent coordinate obeys

    ell<=P.t<T0-eta/s<0.

The actual far corner Z=(k+1)n+ell*t therefore satisfies

    |Z|^2>(H0+1)^2+(T0-eta/s)^2.

The strict inequality follows from squaring two negative tangent bounds
with ell strictly smaller, and from k>=H0>0. It does not require P
itself to be a vertex.

The first positive square-root expression H0+1 increases with both
A0 and g. The positive second expression can be written

    -T0+eta/s
      =A0*c+g*c^2/s-(49/75)/s.

Its derivatives with respect to A0 and g are c>0 and c^2/s>0.
Positivity is already true at the two lower endpoints A0=59/60,
g=69/100: using the full direction bounds just proved gives the
strict lower estimate

    (59/60)*(9/10)-(69/100)/3+(11/300)*3>0.

Thus both squares can legitimately be bounded below by substituting
those endpoint values. No reversal from squaring a possibly negative
expression occurs. This also explains why no lower bound on h was
needed: making h smaller only increases A0 and both expressions.

## 6. Exact expansion, AM-GM bound, and final circle contradiction

Let

    A=59/60, G=69/100, E=11/300,
    K=1+A^2+G^2-2*G*E=5383/2250.

I independently expanded the two exact endpoint squares, using only
s^2+c^2=1:

    [1+A*s+G*c]^2+[A*c-G*s+E/s]^2
      =K+2*A*s+2*G*c+2*A*E*(c/s)+E^2/s^2.

The mixed 2AGsc terms cancel, and the cross term from -Gs and
E/s is exactly -2GE. All remaining variable terms displayed on the
right are positive.

Since c>9/10 and s>0,

    2*A*s+2*A*E*(c/s)
      >2*A*s+2*A*E*(9/10)/s
      >=2*sqrt((2*A)*(2*A*E*(9/10)))
      >7/10.

The middle step is the arithmetic-geometric mean inequality on two
strictly positive terms. The exact squared reserve for the last step is

    4*(2*A)*(2*A*E*(9/10))-(7/10)^2
       =1541/75000>0.

Also 2G*c>621/500. Discarding only the positive E^2/s^2 term gives
the complete continuous lower bound on the same actual far corner:

    |Z|^2>K+621/500+7/10
           =3901/900
           =1105/256+1039/57600.

The final reserve is strictly positive, whereas actual containment
requires |Z|^2<=R^2<=1105/256. This contradiction proves the entire
closed-strip statement at the claimed lower g threshold.

I checked the six printed rational values independently with exact
fraction arithmetic: the first reserve, K, the AM-GM squared reserve,
the final corner lower bound, its difference from the upper circle
bound, and the later 17/12 diameter reserve. These arithmetic checks
support the displayed identities; they are not a numerical geometric
exclusion or a substitute for the whole-domain proof.

## 7. Every position in the lower-route extension

Let the actual A be interior-disjoint from H and B, in the same circle,
and retain the full hypotheses

    ell0,eta0>0, ell0+eta0>sqrt(2),
    min_A x>=h-1,
    min_A y>g-1+eta0,
    P in B, P_x<=h-ell0, P_y<49/75.

Suppose V belongs to actual A intersect B. Its height is strictly
above g-1 and its abscissa is at least h-1.

For h-1<V_x<h, a height V_y<g would put V in int H. For the
exact left endpoint V_x=h-1 and V_y<g, the whole-A minimum forces
nearby interior A points to have x>h-1; sufficiently near V they
also have x<h and g-1<y<g. Both alternatives violate physical
interior disjointness. Thus in the half-closed strip h-1<=V_x<h
one has V_y>=g, and the newly proved barrier applies directly.

At V_x=h and V_y>=g, that same barrier includes its closed right
endpoint. At V_x=h with g-1<V_y<g, the actual B segment toward P
immediately moves left from a height strictly between H's bottom and
top, entering int H. The vertical sign of the chord need not be fixed
for this local interior conclusion.

Only V_x>h remains. The actual chord PV has a unique intersection E0
with x=h, strictly between its endpoints because P_x<=h-ell0<h.
The whole chord and E0 belong to the unchanged actual B.

If E0_y<=g-1, the two actual collinear subsegments satisfy

    |P-E0|>=h-P_x>=ell0,
    |E0-V|>=V_y-E0_y>eta0.

Their lengths add exactly because E0 lies between P and V:

    |P-V|=|P-E0|+|E0-V|>ell0+eta0>sqrt(2).

This contradicts the diameter of that same unit B. The argument adds
lengths of consecutive collinear subsegments; it does not incorrectly
add independent coordinate projections of one vector. It includes
E0_y=g-1 and P_x=h-ell0.

If g-1<E0_y<g, the segment from E0 toward P immediately enters
int H. If E0_y=g, it enters as well, since P_y<49/75<g forces
the initial motion downward and left. Finally, if E0_y>g, the
actual points P,E0 satisfy the proved closed-strip barrier at its
included right endpoint E0_x=h. This covers every remaining chord.

Hence actual A and B cannot touch under the complete stated minimum
bounds. The displayed instance ell0=2/3, eta0=3/4 is valid because
their sum is 17/12 and

    (17/12)^2-2=1/144>0.

The extension permits any other actual positive pair satisfying the
same strict length condition. Its auxiliary E0 is solely a point of
the actual B segment and is never inserted into an original force
or torque equation.

## 8. Scope, preserved endpoints, and source identity completion

The theorem is force-free and uniform over all actual B orientations
and all actual P,V positions satisfying its inequalities. It covers
the critical epsilon=0 endpoint and the upper allowed circle equality.
Its h hypothesis remains only h<=epsilon. Every V strip endpoint,
top-height equality and lower-route crossing equality was checked
directly. The strict P-height cap and whole-A minimum-height condition
are genuine stated hypotheses, not conclusions supplied automatically
to a future graph caller.

The complete predecessor lower-route source has exact current SHA-256
`11e9eb7ba47bb8e8042aed44536046dba6c98f50961e663986935e0ea41cd9a1`.
The new source pins that exact value. No predecessor threshold of
37/50 or low-port bound 7/10 is silently imported here; the new proof
uses 69/100 and 49/75 at every crossing and corner step.

A future original-family application must establish the unchanged
actual H chart, the actual low port, and the complete actual A extents
in the lower-route variant. The theorem does not alter any other
physical unit or original equation and does not itself close an
original graph/load family. Every all-nine-unit caller must retain
its other actual units and all original forces, normals, applications,
shared means, physical masks, and individual zero coefficients.

Only this new independent review file was written. No mathematical
source, metadata, ledger, family flag, commit, remote state, Lean
compilation, CI, workflow, or merge was changed. There was no discovery
contribution by this reviewer, no geometric sampling, and no finite
computational exclusion packet.
