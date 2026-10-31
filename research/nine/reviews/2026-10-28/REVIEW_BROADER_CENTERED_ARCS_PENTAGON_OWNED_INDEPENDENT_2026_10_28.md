# Independent full review of the three-quarters arc and the stronger forty-degree arc

Date: October 28, 2026 UTC. Reviewer: pentagon_owned.

**Verdict: PASS for both exact frozen targets below, at their separate
literal physical scopes.** No mathematical blocker was found. This is
a complete source and scope review, not a spot check or a confirmation
of only the new threshold arithmetic. Root adoption remains separate.

## 1. Independence, targets and complete reads

I did not construct either target, suggest either threshold, supply
either affine or completed-square bound, or contribute the low-center
displacement argument. The three-quarters source attributes construction
to pentagon_audit and root; the forty-degree source is root's construction.
I received their frozen versions as an independent reviewer. I have
not changed any target, caller, source pin, flag or shared ledger.

The complete targets read and checked are:

| Target | SHA256 | Extent |
| --- | --- | --- |
| THREE_QUARTERS_CENTER_UNIT_CENTERED_NINE_EIGHTHS_ARC.md | c511df67ca7857c3aa85d62c768cb87da428c7eaedd4328d6a9d6bf36dcba16a | All 269 lines / 9988 bytes |
| THIRTY_SEVEN_FIFTIETHS_CENTER_UNIT_CENTERED_FORTY_DEGREE_ARC.md | aef1a6c7a6ac6631c5b236f50301b31db2f87441b1f9e22883686d8f70032282 | All 280 lines / 10415 bytes |

I also read in full the operative prior source and its expanded
table-free replacement:

| Source | SHA256 | Reviewed role |
| --- | --- | --- |
| BOUNDARY_UNIT_CENTERED_NINE_EIGHTHS_ARC.md | b1f647212d0a1fe44e3cce2f3ea6e2ba12591131445aa1518da063e74c3a118b | Full accepted actual-coordinate proof, original statement, endpoint handling and exports |
| BOUNDARY_CENTERED_NINE_EIGHTHS_ARC_WITHOUT_COEFFICIENT_TABLES.md | a7227187917d53d0012bc04c002b0d24e33e5419da798381e899477a3861d1ab | Full expanded affine and completed-square replacement, including its exact dependency boundary |

The earlier five-sixths construction source 261dec was also read
completely as provenance. It is not a mathematical premise of either
reviewed target and receives no separate adoption claim in this review.
Neither reviewed target depends on a claimed conclusion from an
unexamined orientation table: both print the needed arguments in full.

## 2. Common actual geometry and coordinates

For an actual unit centered at c, choose signs and, if needed, the
order of its own axes so that c=r(x,y), x,y>=0 and x^2+y^2=1.
An interchange preserves these inequalities and supplies positive
orientation for the displayed angular-coordinate formulas. Equivalently
reversing orientation only exchanges the allowed signs of tau, which
are both retained. The positive thresholds make r nonzero.

The actual farthest corner has squared radius

    r^2+r(x+y)+1/2.

This is exact: in the chosen own frame its two displacements from
c are both +1/2. Thus containment in the actual disk of squared
radius at most Q=1105/256 gives the printed farthest-corner inequality.
The complete orientation parameter satisfies 1<=x+y<=sqrt(2),
including own-axis and diagonal directions. No frame is varied.

A radius-rho point displaced by tau from c's actual direction has
the two relative coordinates used in both targets. Membership in
(-1/2,1/2)^2 in this actual own frame is exactly membership in the
open square. The open disk of radius 1/2 centered at c lies in that
same open square independently of its orientation. Both proof routes
therefore have the claimed physical meaning.

## 3. Complete review of c511: center radius at least 3/4

### 3.1. The whole-orientation affine estimate

For L(t)=28/15-(7/20)t, direct expansion gives

    L(t)^2+tL(t)+1/2-Q
      =-(91/400)t^2+(14/25)t-19121/57600.

The constant, linear and quadratic terms all match. L is positive
throughout [1,sqrt(2)]. The quadratic is concave, so a positive lower
bound at both endpoints is a valid lower bound on the whole interval.
I checked P(1)=31/57600 and the endpoint comparison
P(sqrt(2))>3799/1440000 using sqrt(2)>141/100. The squared reserve
119/10000 is exact. Since z^2+tz+1/2 strictly increases for z>=0,
the resulting strict r<L(t) follows at every orientation, including
t=1 and t=sqrt(2). It has no hidden high-center premise.

### 3.2. The complete inward estimate

The old two-square identity expands to

    (9/20)x^2+(7/20)xy+(1/10)y^2
      -(13/16)x-(3/8)y+2/5.

In particular the constant is exactly 2/5: the two squared constants
sum to 145/368, and adding 11/1840 gives 2/5. Its difference from
the left side is precisely (x^2+y^2-1)/10. Both squared coefficients
and the reserve 11/1840 are positive.

Together with 28/15-135/128=1559/1920<13/16 and x>=0 this proves
the complete inward-coordinate bound, including x=0 or y=0. No sign
of r-135/128 or r-rho*cos(beta) is assumed.

The exact beta=atan(7/20) comparisons are correct:
cos(beta)=20/sqrt(449)>15/16 and sin(beta)=7/sqrt(449)<1/3.
The printed integer reserves 1375 and 8 have the correct signs.

### 3.3. Both closed center-radius ranges and every endpoint

For 3/4<=r<=rho=9/8, the exact displacement formula and
cos(tau)>=cos(beta)>15/16 give a strict upper bound by

    G(r)=r^2+rho^2-(15/8)r*rho.

G is convex. An upper bound by its larger endpoint value is valid
on this full closed interval. Direct substitution gives
G(3/4)=63/256 and G(9/8)=81/512. Their reserves below 1/4 are
exactly 1/256 and 47/512. Hence the displacement is strictly below
1/2 even at r=3/4 and |tau|=beta. This is an orientation-free
inclusion in the actual unit's open incircle, not an axis estimate
applied with a missing sign assumption.

For r>=rho the radial coefficient rho*cos(tau)-r is nonpositive.
The positive coordinate side is therefore bounded by
rho*sin(beta)<3/8. The other side follows from the full inward
estimate, with both signs of tau and with x,y interchanged for the
second coordinate. The two radius arguments overlap at r=rho.
Both axes, both angular endpoints and both containing-radius
endpoints are retained with strict interior margins.

### 3.4. Its exact physical exports

The boundary-center consequence uses the actual circle corner:

    |c|>=R-1/sqrt(2)>79/40-17/24=19/15>3/4.

The inequality remains strict at R=79/40. It uses physical boundary
contact only, with no positive-force requirement at that corner.
For any two qualifying distinct actual units, overlapping closed
arcs would give a point in both open interiors. Their minor center
separation is therefore strictly greater than 2beta, including
the putative endpoint-contact equality. Because 4beta<pi, two
successive gaps inside the stated minor interval have exactly the
minor angular distances used in the no-third-center consequence.
They cannot have sum at most 4beta. Nonqualifying actual units are
explicitly retained and are not counted by this export.

**Verdict for c511: PASS** at its complete r>=3/4, beta=atan(7/20)
scope, with the physical boundary consequence on the full original
radius window. Its main theorem uses only the squared upper radius.

## 4. Complete review of aef1: center radius at least 37/50 and a forty-degree arc

### 4.1. Exact angle bounds

For theta=pi/9, both polynomial monotonicity intervals are valid.
Cos(theta)>1/2, and 4u^3-3u strictly increases for u>1/2.
At u=109/116 its value minus 1/2 is exactly -111/390224.
Thus the cosine comparison has the asserted strict direction.

Sin(theta)<1/2 and 13/38<1/2. The polynomial 3v-4v^3 strictly
increases on this range. Its value at 13/38 is the positive
number 5941/6859. Squaring and subtracting 3/4 gives exactly
44281/188183524>0. Positivity justifies taking the comparison
with sqrt(3)/2; hence sin(theta)<13/38 follows. No branch of a
triple-angle inverse was used without its monotonicity domain.

### 4.2. The sharper affine bound

For L(t)=2243/1200-(141/400)t, the three expanded terms are exactly
those in the target. In particular the quadratic coefficient is

    (141/400)^2-141/400=-36519/160000,

and the linear coefficient is 2243*59/240000=132337/240000.
L(t)>0 even using t<2. Its concavity minimum argument is valid
on the whole closed interval. At t=1, L=91/60 and P=31/57600.
At t=sqrt(2), substituting only the lower bound 707/500 in the
positive linear term leaves numerator 207277 over 360000000.
The quadratic term keeps t^2=2 exactly, and the square-root
reserve 151/250000 is correct. Thus strict r<L(t) is uniform.

### 4.3. The new completed-square identity and every coefficient

I expanded the full new identity independently. Its right side is

    (37/80)x^2+(141/400)xy+(11/100)y^2
      -(13/16)x-(117/304)y+39/100.

Here the two y-square contributions are 19881/296000 and
12679/296000, whose sum is 11/100. The two y-linear contributions
sum exactly to -117/304. For the constant, a common denominator
43704104000 gives numerator 17044600560, exactly 39/100 of that
denominator. This check includes the printed reserve 3497/29529800.

Subtracting the target left side therefore gives precisely
(11/100)(x^2+y^2-1). Both squared coefficients are positive,
as is the reserve. Its stronger comparison with 1/10000 has the
printed positive difference 27201/1476490000.

The two coefficient substitutions also match exactly:

    2243/1200-(9/8)(109/116)=56519/69600
      =13/16-31/69600,
    (9/8)(13/38)=117/304.

Replacing the coefficients in the actual inward expression is
legitimate because x,y>=0, regardless of the sign of the radial
difference. The reserve proves strictness on the axes as well.
This establishes the full displayed inward bound without a table,
an orientation interval split, or an omitted coefficient sign.

### 4.4. The complete low and high center ranges

For 37/50<=r<=rho, the exact actual displacement is strictly below
G(r)=r^2+rho^2-2r*rho*(109/116). This quadratic is convex.
Direct substitution yields 288491/1160000 at 37/50 and 567/3712
at 9/8, with exact reserves 1509/1160000 and 361/3712 below 1/4.
The lower-center argument therefore includes its exact new threshold,
both angular endpoints and the joining center value with strict
open-incircle inclusion at every frame.

For r>=rho, the positive coordinate side is below
rho*sin(theta)<117/304<1/2. The new inward identity bounds the
negative side strictly below 1/2. The signs of tau and the exchange
of own axes cover all four coordinate inequalities. The entire
closed arc lies in the actual open square. The two closed ranges
overlap at rho and exhaust all r>=37/50. Only R^2<=Q is required.

### 4.5. At most eight qualifying centers, with the strict threshold

Two qualifying actual units cannot have common closed arc points,
because these points belong to both open squares. Distinct qualifying
centers also cannot have the same angular direction. For cyclically
ordered qualifying directions, each successive gap exceeds 2pi/9;
otherwise the two adjacent closed arcs would meet. This includes a
gap equal to 2pi/9, since the shared endpoint would be interior to
both squares. Nine such gaps would have sum strictly greater than
2pi. Hence at most eight actual units qualify.

The stated nine-unit consequence is exactly that some actual center
has radius strictly less than 37/50. Equality qualifies and was
excluded from a set of nine. The proof does not identify that unit,
place O in it, assign it a force or degree, or remove any other unit.

### 4.6. Boundary contacts and the no-skipping export

Every physical boundary unit qualifies on the complete original
window by the same strict center bound 19/15. If two such units
physically touch, their actual centers are at distance at most
sqrt(2), since each is at distance at most 1/sqrt(2) from a common
point. No positive stress edge is required.

For their radii r,s and minor separation gamma, the cosine identity
and r^2+s^2>=2rs give cos(gamma)>=1-1/(rs)>136/361. The next
comparisons 136/361>1/3 and cos(2pi/5)<1/3 have the correct strict
directions; sqrt(5)<7/3 verifies the latter exact value. Cosine is
strictly decreasing on the minor-angle interval [0,pi], so
gamma<2pi/5<4pi/9. A third qualifying direction strictly between
them would give two successive gaps each exceeding 2pi/9 and
contradict that bound. A third qualifying center on an endpoint
direction is already impossible by the closed-arc argument.

Thus the last sentence's conclusion for every other actual center
in the minor interval is justified as well. Centers below 37/50
are not ruled out there; their capacity and routing remain separate.

**Verdict for aef1: PASS** at the complete squared upper-radius,
r>=37/50, closed halfwidth pi/9 scope, including all three exact
packing exports and the full-window boundary-contact premise where
the latter is used.

## 5. Adoption boundary

The reviewed results are force-free physical facts about actual
unit squares. All original graph edges, true degrees, complete force
and torque equations, supports, normal owners, mean applications,
physical masks and individual zero circle weights remain unchanged.
No generic selected-normal condition is a premise of these arc proofs.

The stronger source implies an actual center below 37/50 in every
nine-unit packing in its disk, but does not alone close any remaining
graph/load family, capacity statement, sharp bound or equality case.
No original gate or additional computational-certificate retirement
is credited by this review. A later caller must retain all units and
prove every needed actual center threshold, graph identification or
route condition at its literal scope.

No Lean/Lake, compilation, CI, workflow, pose search, geometric
enumeration, generated coefficient table, source mutation, metadata
edit, staging, commit or remote action was used in this review.
