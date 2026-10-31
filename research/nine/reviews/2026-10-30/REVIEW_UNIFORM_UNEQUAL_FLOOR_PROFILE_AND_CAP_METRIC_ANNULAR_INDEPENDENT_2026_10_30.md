# Full review of the unequal-floor profile and sharp two-unit cap metric

**Date:** October 30, 2026 UTC. **Reviewer:** annular-capacity agent.

**Verdict: PASS at the complete stated scope. No source repair is required.**

## 1. Frozen source and disclosed contribution

I read the complete source
`UNIFORM_UNEQUAL_FLOOR_SECTION_PROFILE_AND_TWO_UNIT_CAP_METRIC_2026_10_30.md`
and reconstructed all statements, strict cases, equality cases and cycle
callers. Its frozen size is 19,344 bytes and SHA256 is

`abfb4887037851d2715c8ff746ff11dc238109692b2cc0fbc42598bb4dae9d94`.

The source was not edited. I authored the separately frozen positive-tilt
lemma reproduced with attribution in Section 3. That contribution is disclosed:
this is a full assembly review and an independent reconstruction of the
negative-tilt family, metric argument, equality analysis and force caller.
The positive-tilt input has separate full reviews by axial_chain and
block_ears. I checked that its reproduction preserves every hypothesis
and every exact interval.

All five input pins in the final table match their current bytes. I have
also independently reviewed the complete long-channel barrier, coupled
return-side usage, and the full long-endpoint alignment assembly used in
the caller. No unspecified assertion from an older C7 selection source is
needed by the analytic profile.

## 2. Entire one-square domain and positive-tilt import

For every floor `f in [3/8,1/2]`, the square's top height is at least
`f+a+b>=11/8>5/4`. Its bottom is at most `R-a-b<=R-1<9/8`.
Thus the actual section is a nondegenerate interval strictly between the
horizontal supporting lines. Its relative interior is inside the square's
open interior. This remains true at both floor endpoints and for aligned
units.

The complete orientation reduction to the two signed tilt forms is valid
up to quarter turns of the square's description. The left endpoint formulas
come from the original four side inequalities. The actual top and right
corners used in each estimate have the stated minimum heights, so all
radicals occur in their defined domains.

The positive-tilt reproduction is faithful. The first edge uses the whole
permitted top-vertex height interval and the elementary strict inequality
with bracket `3+2a-a^2-7ab>=1/4`. The active second edge retains `a/b`,
first lowers the actual floor continuously and then minimizes over the
whole admissible tilt interval. The derivative identity in (14) agrees
with the frozen independent lemma. The final value has the stated strict
`81/80` lower bound. No inactive edge or diagonal boundary is lost.

## 3. Negative first edge: floor monotonicity

The rightmost actual vertex yields the exact upper estimate in (17), so
it suffices to prove positivity of

    V(f,a)=1-a+b*(a-k)-a*(g(f+a)-g(f+1)).

On the full integration interval, `0<=Y<=3/2`. Since
`-g''(Y)=Q/g(Y)^3` increases with Y, its maximum there is
`17680/12167<3/2`. Differentiation in f therefore gives

    V_f>b-(3/2)*a*(1-a)>b/4>0.

The sign of the integral term is correct: `g'(f+a)-g'(f+1)`
is positive. The last strict comparison follows from
`a(1-a)=ab^2/(1+a)<b/2`. Consequently lowering f to `3/8`
is legitimate over every negative tilt, without changing its a or b or
discarding a relevant corner constraint.

## 4. Negative first edge: quadratic remainder and exact polynomial

On the smaller interval `[3/8+a,11/8]`, the lower endpoint is
strictly greater than `17/16`. Thus `g(Y)^2<51/16` and
`-g''(Y)>3/4`. The exact square reserve is

    Q^2-(9/16)*(51/16)^3=13583/32768>0.

Integrating this curvature bound from the upper endpoint produces

    g(3/8+a)<=C_0+K_0*(1-a)-(3/8)*(1-a)^2.

The sign of the quadratic remainder is negative, as required for a
concave circle boundary. It is preserved rather than replaced by a
linear tangent estimate.

The half-angle substitution `tau=b/(1+a)` maps the entire tilt
interval into `(0,sqrt(2)-1]`, contained in `[0,5/12]`. The exact
square difference for `K_0<221/250` is `80261/38812500>0`.
Substitution and division by positive b give the polynomial numerator

    1+(116/125)tau-14tau^2+22tau^3-15tau^4+(1134/125)tau^5

over `8(1+tau^2)^2`, with the strict inequality in the source.
I independently expanded this rational expression: the cubic coefficient
22 and quintic coefficient `1134/125` include the quadratic curvature
remainder with the correct signs.

I then expanded the complete degree-five identity after `tau=5xi/12`.
All six Bernstein coefficients match the displayed values exactly:

    1, 404/375, 16409/18000, 142987/216000,
    343139/864000, 24119/115200.

Each is positive, and the last is their minimum. The corresponding basis
functions are nonnegative on the full closed interval and sum to one by
the binomial theorem. This is a single exact polynomial positivity
identity over the continuum, not evidence from finitely many tilt values.
It proves the claimed uniform positivity of V and hence the strict bound
for the complete first negative-tilt edge.

## 5. Negative second edge, reflection and equality

The original top corner gives `b*m_2<=R-a*z-1`. The needed lower
bound on `a*z+b*(C-1)` follows from concavity in a and its two
endpoint values. Since `C-1>=7/16`, those values are at least
`5/4` and `27/(16sqrt(2))`; both are strictly greater than `9/8`,
which is greater than `R-1`. Thus the second negative edge is strict
throughout, independent of which edge is active.

For an aligned square, the actual farthest-corner formula gives the
left endpoint bound directly. Every equality in the chain is needed:
the center's x coordinate is nonnegative, its height is exactly
`f+1/2`, and its outer coordinate is exactly `C(f)`. Hence the
claimed equality center is forced. Conversely the stated aligned square
fits the disk and attains equality. Reflection exchanges the two signed
tilt descriptions and gives the right-endpoint bound and its complete
equality statement.

The resulting profile is therefore valid for every orientation and every
specified floor in the closed interval, and both inequalities are strict
for every nonaligned unit.

## 6. Actual two-square metric and sharpness

Both actual sections lie on the same line. If they overlap, the set
distance is zero, strictly below the positive claimed upper bound. If
they are disjoint, their two nearest section endpoints are actual square
points, so the square set distance is at most their horizontal gap.
Applying the appropriate left and right profiles gives

    dist(S_1,S_2)<=C(f_1)+C(f_2)-2.

Either section order is covered. If one square is tilted, one of the
two profile bounds used for that order is strict. No separating-axis
assumption or physical intermediate square enters this argument.

The claimed aligned extremizers are correct for every pair of floors in
the domain. Their vertical intervals overlap because the floor difference
is at most `1/8`, while their horizontal intervals have precisely the
positive displayed gap. Hence their Euclidean set distance equals that
gap. Their outer upper corners are on the original circle and their other
corners are inside it. This verifies the full sharp metric profile, not
only its equal-floor specialization.

Under the sum-floor and distance hypotheses, strict concavity and decrease
of g force every inequality in (30) to be equality. Equality in concavity
gives equal floors; strict decrease gives their sum exactly `7/8`.
The strict tilt clause then forces both units to align, and the exact
one-square equality description pins their centers to `(-1,15/16)`
and `(1,15/16)`. Their corners have squared norm Q, so any original
smaller containing disk must actually have squared radius Q. Every
rigidity conclusion follows from a checked equality implication.

## 7. Full vertical-return cycle caller

The source explicitly retains full true degree two at A and B for its
endpoint equilibrium argument. Their other positive contact is the long
horizontal force. Under the stated actual upward return normals, full
y-force balance therefore requires a negative total circle y resultant.
An aligned physical-boundary endpoint with positive center height has
only an upper outer circle corner and cannot supply that resultant.
Thus both endpoint center heights are nonpositive. At height zero,
both physical circle corners and their independent weights remain; no
mask is silently selected.

The actual upward support equations give whole-square floors for C,D.
The coupled long-endpoint height bound puts both floors in `[3/8,1/2]`
with sum at least `7/8`. The short unloaded full-degree-two transmitter
propagates its original normal, and its actual unit width supplies set
distance at least one. This does not presume that the short normal is
horizontal or that the short internal square stays above either floor.
The sharp metric corollary applies directly.

The reflected or unordered equality anchors are assigned correctly using
their actual endpoint contacts: a left equality return square cannot
meet the right long endpoint, and conversely. The boundary equations for
the aligned long endpoints then force centers `(+-3/2,-1/16)`.

Finally the short normal is horizontal in equality. For the two actual
aligned return squares the difference set has closest vector `(1,0)`
and distance one. A signed support gap at least one is at most the
projection of that actual vector, itself at most one; all comparisons
are equalities only for the horizontal unit normal. The internal width
is then exactly one, which makes the short transmitter side-normal.
Its transverse center position and actual mean are correctly left free.

The caller thus closes precisely the vertical-return branch and gives
the claimed four-anchor equality geometry. The source itself explicitly
retains oblique corner returns as a separate obligation; their later
wrapper analysis is not assumed in this review.

## 8. Verification boundary

The full rational Bernstein identity, both curvature constants, all
source pins and the imported positive-tilt arithmetic were checked
exactly. This review performed no numerical pose or stress search and
does not rely on the research diagnostic disclosed in the source.
The proof itself supplies the entire continuous domain and equality
analysis. No source mutation, original gate change, Lean compilation,
CI execution, certificate replacement or publication was performed.
