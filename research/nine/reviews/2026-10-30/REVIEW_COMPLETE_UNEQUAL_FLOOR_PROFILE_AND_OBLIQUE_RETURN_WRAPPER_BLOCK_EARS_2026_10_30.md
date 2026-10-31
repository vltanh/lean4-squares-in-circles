# Full independent review: unequal-floor profiles and the aligned-endpoint corner return theorem

**Date:** October 30, 2026 UTC. **Reviewer:** block-ears agent.
**Result:** PASS for both complete frozen sources. No repair requested.

## Frozen sources and review scope

I read both sources in full and reconstructed every continuous family,
exact identity, geometric contact join, and equality consequence:

1. `UNIFORM_UNEQUAL_FLOOR_SECTION_PROFILE_AND_TWO_UNIT_CAP_METRIC_2026_10_30.md`, 19,344 bytes, SHA256 `abfb4887037851d2715c8ff746ff11dc238109692b2cc0fbc42598bb4dae9d94`.
2. `ALIGNED_ENDPOINT_CORNER_WRAPPERS_OBEY_THE_UNEQUAL_FLOOR_SECTION_BOUND_2026_10_30.md`, 10,936 bytes, SHA256 `55607f2ab5a25c056fcc12e893b3d4c7e60814c6d2e607c21b806277d29de5bc`.

The positive-tilt floor input was separately read and reviewed in full in
`REVIEW_UNIFORM_FLOOR_POSITIVE_TILT_SECTION_BLOCK_EARS_2026_10_30.md`.
I also fully reviewed the long-endpoint contact-locus and alignment inputs
before reading these assemblies. I authored a separate tangent proof of
the below-floor return estimate; the present review checks the displayed
independent squared-identity/Cauchy proof, rather than substituting that
alternative argument.

## 1. Complete one-square floor profile

The unit's top is at least `f+a+b>=11/8`, and its bottom is at most
`R-a-b<=R-1<9/8`. Thus its section at `5/4` is always nondegenerate.
Quarter-turn side descriptions cover the two signs of tilt with
`a>=b>=0`. The two left-edge formulas in each sign follow directly
from the actual own-coordinate inequalities.

For positive tilt, the full previously reviewed argument is reconstructed
correctly. The top-vertex first-edge estimate uses a decreasing linear
functional on the appropriate circle arc, with the actual top-height
lower bound. Its auxiliary strict inequality has the exact positive
factor `b/(1+a)*(3+2a-a^2-7ab)`. The active second edge forces `a<=k`.
The entire floor interval then reduces monotonically to f=3/8; the
remaining tilt function increases over `[1/sqrt(2),7/8]` and has the
strict diagonal-endpoint bound `81/80>1`. The source retains the
inactive-edge alternative and all radical-domain endpoints.

## 2. Negative first edge: full floor and orientation interval

For negative tilt, I checked the rightmost-vertex identity
`a m1=a P_x-b P_y+b z-1`. The actual height lower bound f+a and
monotonicity of `a g(Y)-bY` give exactly the displayed comparison with
`-V(f,a)`. All integration endpoints in its floor derivative are at
most `3/2`.

The bound `-g''(Y)=Q/g(Y)^3<3/2` is valid throughout that interval;
at its upper endpoint its exact value is `17680/12167`, below `3/2`
by `1141/24334`. The formula for the floor derivative is

    partial_f V=b-a*integral_(f+a)^(f+1) Q/g(Y)^3 dY.

Because `a(1-a)=a b^2/(1+a)<b/2`, this derivative is strictly above
b/4. Hence the smallest floor is the only floor that must be analyzed.

At that floor, the entire interval of the circle tangent estimate has
Y>17/16 and g(Y)^2<51/16. Positive squaring gives the lower curvature
bound `-g''>3/4` with exact reserve `13583/32768` in the displayed
squared comparison. Integrating it in the correct direction yields

    g(3/8+a)<=C0+K0(1-a)-(3/8)(1-a)^2.

The negative quadratic remainder has the correct sign. Replacing K0
by its strict upper bound `221/250` has the squared reserve
`80261/38812500` and yields a strict lower bound on V/b.

The substitution `tau=b/(1+a)` covers the full nonzero-tilt interval.
I independently expanded the resulting numerator, obtaining exactly

    1+(116/125)tau-14tau^2+22tau^3-15tau^4+(1134/125)tau^5.

I also expanded all six displayed Bernstein terms after `tau=5xi/12`
using rational arithmetic and the binomial theorem. Every ordinary
coefficient agrees with this numerator. Each Bernstein coefficient is
positive and at least `24119/115200`, while its basis terms are
nonnegative and sum to one on `[0,1]`. This is an exact polynomial
identity over a continuous interval, not a sampled orientation check.
Thus V>0 and the entire negative first-edge bound is strict.

## 3. Negative second edge and exact aligned equality

For the second negative-tilt edge, the top-vertex identity gives
`b m2<=R-a z-1` by a unit-direction Cauchy bound. The needed lower
bound `a z+b(C-1)>R-1` follows from concavity in a and the two endpoint
values. The chain through `27/(16sqrt(2))>9/8>R-1` is strict on the
complete domain. Thus both negative-tilt edges are covered without an
activity restriction.

At b=0 the actual farthest aligned corner gives the chain
`ell<=|x|-1/2<=g(y+1/2)-1<=C(f)-1`. Equality forces nonnegative x,
y=f+1/2, and x+1/2=C(f), exactly as stated. Reflection proves the
right-endpoint profile, including strictness for every nonzero tilt and
its reflected aligned equality case. This completes every orientation
and every floor in the original interval.

## 4. Two-square metric and all equality joins

The metric proof compares actual section intervals on the same horizontal
line. If they overlap, the actual set distance is zero, below the positive
claimed upper bound. If they are disjoint, their actual adjacent endpoints
bound the set distance from above. Applying the right profile to the
left interval and the left profile to the right interval gives precisely
`C(f1)+C(f2)-2`. Exchanging the interval order covers the other placement.
A rotated square makes the appropriate profile inequality strict.

The two aligned examples stated in the source attain this bound: their
vertical intervals overlap because the two floors differ by at most
one eighth, and their horizontal gap is positive. The actual outer-upper
corners lie on D_Q. Therefore the profile is sharp for all unequal floors
in the stated continuous range.

If the floor sum is at least 7/8 and the actual set distance is at least
one, the concavity/decrease chain has equal endpoints equal to one.
Strict concavity forces equal floors, strict decrease fixes their sum,
and the one-square equality clauses fix both actual aligned centers.
The resulting corners have squared norm Q, so an actual smaller containing
disk is impossible. No common normal or actual intermediary is presumed.

The vertical-return C7 caller uses genuine full U/V/W degrees, actual
long support telescoping, and A/B full true degree two. Positive return
y-components force nonpositive aligned endpoint center heights; the
radial two-corner masks at zero height remain. The actual vertical
supports give the two full-square floors, and the true short channel
gives actual set distance at least one. The equality anchors and their
left/right assignment follow from the original contacts. The final
horizontal short direction is justified by the unique minimum vector
of the aligned return-square difference set, rather than assumed at
the start. The source correctly leaves the oblique-return branch out
of its standalone caller.

## 5. The oblique supporting-side return: section existence

The second source's core theorem retains the exact chart
`p+[0,1]n+[r-1,r]u`, with all r in `[0,1]` and arbitrary strictly
positive alpha,beta. It does not impose a whole-square floor. Its
original endpoint-corner inequality gives q>15061/3600>4.

If the actual top were at most 5/4, then beta<=k and
alpha>=sqrt(15)/8>7/16. The complete slider gives the upper x-bound
349/240<3/2 and the lower bound greater than -1/2. Every y coordinate
would lie between -5/8 and 5/4. Thus every actual corner would have
squared radius below 61/16<4<q, contradicting physical circle contact.
The bottom is already below 5/4. This proves the nondegenerate section
without assuming the square lies above zero or above its nominal floor.
The two left candidates and their maximum then follow from the original
side-coordinate inequalities, including r=0 and r=1.

## 6. Both oblique candidates are bounded over the whole domain

For the first candidate, I checked the upper-corner identity
`beta ell1=u.P-1-alpha z` and its Cauchy bound using
`E=n.P=1-alpha x+beta f`. The radical is defined because the same
actual corner P is contained in the disk.

Expanding the two squares gives exactly the displayed identity (9).
The comparison quantity `1+alpha z+beta d` is positive. The estimates
`2(z-x)>7/15`, `zd-xf>=37/960`, and the lower quadratic bound are
valid without ordering alpha,beta. The latter has rational reserve
`1471/57600`. The remaining fraction is below 17/8, so its bracket
is above -3/16 and the full braces above `67/240`. The expansion is
strictly positive for every alpha>0. Positive squaring therefore gives
`ell1<C_f-1` on the entire parameter domain, without an active-edge
assumption.

For the second candidate, the original endpoint-corner inequality gives
`D=x+1-C_f<=g(1-f)-C_f`. Its difference-of-squares expression is
`4f/(g(1-f)+C_f)`. That denominator decreases with f and stays strictly
above `55/16>24/7`, so `0<D<7f/6`.

The convex quadratic `(7f/6)^2+(5/4-f)^2` has endpoint values
`245/256` and `65/72`, with the first larger. Hence
`D^2+k^2<245/256<1`. Cauchy for the original unit pair(alpha,beta)
then gives `alpha D+beta k<1`, which rearranges exactly to
`ell2<C_f-1`. Both candidates are strictly bounded, and their maximum
is therefore strictly bounded as claimed.

## 7. Complete actual contact-type cover

For an actual aligned endpoint, a relative-interior top-side contact
has the unique upward normal and puts the whole return square above
the side. A non-above-floor return must therefore meet the upper-inner
corner. The horizontal-left common axis is excluded by the complete
inner-face lemma: its literal parameters satisfy
`kappa=x+1`, `ell=1-f>=1/2`, `kappa-ell=x+f>1`, and
`kappa^2+ell^2=q`.

If the return contact is a vertex, the two inward/support normal cones
are closed angular intervals of equal length pi/2. Their nonempty
intersection contains an endpoint direction of the first interval.
The horizontal endpoint is impossible by the preceding face lemma;
the vertical endpoint proves an actual whole-square floor. That
auxiliary geometric separator does not replace the original stress
normal. If the return contact is a relative side-interior point, its
unique original inward normal is an own axis. In the non-above-floor
branch its two components are strict, and the full actual slider gives
exactly the chart used in Sections 1--5. No other contact type remains.

The imported full floor theorem therefore handles the first alternative,
and the new strict oblique theorem handles the second. Reflection
supplies the left endpoint's right-section statement. This is a complete
physical cover with unchanged square poses and original means, not an
assumed vertical return or a replacement of a square by a convex hull.

Both frozen sources pass their complete stated scopes. Their proofs are
continuous and exact, their original force callers retain full true
degrees, and their sharp equality statements follow from actual occupied
sections. No repair, source mutation, global nine-body closure, original
ledger credit or automated formal verification is asserted by this review.

