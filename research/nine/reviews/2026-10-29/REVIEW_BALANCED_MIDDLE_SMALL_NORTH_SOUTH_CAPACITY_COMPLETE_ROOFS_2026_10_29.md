# Independent full review: balanced-middle North/South capacity theorem

Date: October 29, 2026 UTC. Independent reviewer: roofs.

**Verdict: ACCEPT at the exact stated physical scope.** I did not
contribute to the source proof. I read the entire 525-line manuscript,
reconstructed every geometric and trigonometric argument, and checked
the exact endpoint arithmetic independently. This is a review of a
complete manuscript, not adoption of a conversational summary.

The reviewed source is

    BALANCED_MIDDLE_TWO_SMALL_NORTH_SOUTH_ROOTS_FORCE_FREE_NINE_UNIT_EXCLUSION_2026_10_29.md
    bytes: 20087
    lines: 525
    SHA256: c3978aecc0dbe3f3ff0645f224d7d8e9f18d9353059862d3618deb7ec451afbf

No different revision is covered by this verdict without a comparison.

## 1. Exact theorem and honest caller boundary

The theorem assumes six distinct actual units: the balanced middle T,
small chart roots H,K, and their three distinct actual radial-S leaves.
It assumes the original positive high-S radius interval
0<epsilon<1/60, R^2=(2+epsilon)^2+1/4<=1105/256, actual pairwise
interior disjointness, containment, the full displayed root charts,
a,b>=1/4 at T, and the near-North/near-South real-leaf directions.

It concludes that at most two further actual units can be added.
This is a force-free physical capacity theorem. It uses no shortened
stress equation and imposes no root or exterior true-degree condition.
Original selected normals, physical circle masks, individual zero
weights and shared means are untouched because they are not arguments
of any step of the physical proof.

The theorem does not prove that every original house/fan root has the
balanced middle or the two small North/South charts. It supplies a
whole exit once those hypotheses are independently established. Section
7 correctly retains this restriction and does not give whole-original-
row credit merely from the theorem.

## 2. Complete reconstruction of the one-eighth clearance lemma

On the radius-1/4 circle the actual T occupies exactly x>epsilon.
Its transverse distances a,b>=1/4 include every such circle point;
the far first side is farther than the circle. The occupied angle is
pi-2asin(4epsilon), including the balanced transverse endpoints.

For any unit meeting D_delta, selecting an actual z in that disk
and choosing the longer own-coordinate directions produces an actual
contained half-side quadrant. The circle conditions x.u>delta and
x.v>delta imply the coordinates of x-z are strictly between zero and
1/2, since r+delta<1/2. The resulting open angular piece has measure
pi/2-2asin(delta/r). The proof needs only this included piece, and
never assumes the whole intersection of an arbitrary near unit is
connected.

The two other near units each contribute pi/2-2asin(4epsilon).
A proposed fourth unit meeting D_(1/8) contributes pi/6. The four
pairwise disjoint open-interior circle sets would have measure at least

    2pi-6asin(4epsilon)+pi/6.

The derivative estimate asin(1/15)<1/14 gives the strict excess.
In particular 6asin(4epsilon)<3/7<1/2<pi/6. It excludes the
closed distance endpoint 1/8, not merely distances strictly below it.

The radial-S support premise supplies a real point d e of each root.
The segment from it in direction -e of length one lies in that
original root by own-coordinate support geometry, even at a side
endpoint. Its endpoint is epsilon e. Thus all three roots genuinely
meet D_epsilon. No leaf resultant has been mistaken for a physical
root support point. The clearance lemma applies to each actual
completion square.

## 3. The stronger arc lemma: all coordinates and both full domains

I independently checked the claimed angle gamma=acos(19/25).
Its sine is sqrt(264)/25, with 3/5<S<13/20. Its half-angle
squares are 22/25 and 3/25. The increasing triple-cosine polynomial
on (1/2,1) gives gamma>2pi/9; gamma<pi/3 is immediate.

Choosing signs/order of the actual square axes gives its exact box
[A,a] x [B,b], a>=b>=1/2, A=a-1, B=b-1. This is an
orthogonal coordinate transformation about the unchanged origin.
The radius cap gives A<61/60, B<1/2; these bounds do not erase
negative B or any physical circle-mask endpoint.

### 3.1. Full a>rho domain

Here A>1/8 and the entire circle intersection is genuinely on the
positive first-coordinate semicircle. The inactive outer first face
and the other three actual face inequalities give exactly

    [max(-alpha,beta), min(alpha,eta)],

with alpha=acos(A/rho), beta=asin(B/rho) and
eta=asin(min(b/rho,1)). No disconnected second component exists
in this domain, since the positive first coordinate restricts to
one angular lift before the remaining monotone face bounds.

At fixed q=a^2+b^2, the exact expression
A^2+B^2+2SAB is convex in t=a+b. Enlarging to the complete
fixed-q interval with b>=1/2 places its endpoints at b=1/2
and a=b. I checked both endpoint bounds 97/144 and
72897/100000, both strictly below rho^2 C^2=29241/40000.

The resulting inequality

    (A+S B)^2<C^2(rho^2-B^2)

implies A<C sqrt(rho^2-B^2)-S B regardless of the sign
of A+S B. Since 0<beta+gamma<pi/2, it yields
alpha-beta>gamma with the correct branch of acos.

The other three endpoint differences are 2alpha, alpha+eta
and eta-beta. The half-angle bounds give the first two. The
unit-strip difference has minimum 2asin(4/9) at b=1/2 when
b<=rho; for b>rho it exceeds pi/3. I checked the derivative
and the b=rho joining endpoint. All four differences exceed
gamma, proving a single nonempty open arc for the whole domain.

### 3.2. Full a<=rho domain

Clearance forces B>0: otherwise distance is at most A<=1/8.
It then gives 0<B<=A<=1/8 and A^2+B^2>1/64.
In particular A>1/(8sqrt(2))>1/12, a>13/12 and b>1.

The exact first-quadrant intersection is

    [max(beta,theta), min(alpha,eta)],

where theta=acos(a/rho). Its four endpoint differences are
alpha-beta, alpha-theta, eta-beta and eta-theta.
The first exceeds gamma by its explicit cosine; the middle two
unit-strip differences are at least asin(8/9)>gamma.

For the outer-face difference, the radical estimate is strict over
the full domain, including a=rho or b=rho:

    (rho^2-a^2)(rho^2-b^2)
      <(53/576)(17/64)<(31/192)^2.

Together with ab>13/12 this gives
sin(eta-theta)>59/81>S. The entire difference interval is
[-pi/2,pi/2], where sine is increasing, so no wrong inverse
branch is used. Again all four differences exceed gamma and
the full open intersection is one connected arc.

Finally the actual incircle proves |c_E|>rho-1/2 from the
strict clearance. The independent farthest-corner estimate gives
|c_E|<91/60<rho+1/2. The point in the actual center direction
therefore lies strictly in that incircle and in the unique arc.
No component is discarded in this final argument.

## 4. The two real root arcs and the western gap

The near root vertices satisfy |P|<1/40 by the exact squared
bound 221epsilon^2/100<9epsilon^2/4<1/1600.
For each actual orthonormal root chart, the origin-centered quadrant
arc whose two inward coordinates are less than 39/40 has its smaller
coordinate greater than sqrt(63/200)>1/40. Subtracting P therefore
leaves both coordinates strictly in (0,1), so this is an actual
open-interior root arc, not the arc of a translated substitute.

Its measure is pi/2-2acos(13/15)>pi/6, with the correct strict
reserve (13/15)^2-3/4=1/900. The displayed world-angle endpoints
for H and K follow from their actual reflected frames. The full
small tilt bounds put both arcs strictly between the North and South
leaf directions because theta_0>pi/8>nu.

Both arcs avoid the closed real-leaf sets: an interior point of one
actual square cannot be a closed point of another square with
disjoint open interiors. They consequently lie in the western
complementary leaf interval, and are mutually disjoint. Their total
actual occupied measure there is strictly greater than pi/3.
The proof does not claim that either whole root intersection or the
remaining western free set is connected.

For clarity, the three *closed* leaf arcs are strictly disjoint here
already from the explicit angles, in addition to physical disjointness:
alpha<=beta_0<pi/6, the smaller East/vertical center gaps are at
least pi/2-nu, and nu<1/25<pi/6. Their differences
pi/2-nu-2alpha are positive. The western center gap is at least
pi-2nu and also exceeds 2alpha. Thus no hidden touching-arc
ambiguity affects the three-gap enumeration.

## 5. Complete three-gap allocation and the empty-small-gap join

The full actual radial-S intersection is exactly the closed arc of
halfwidth alpha(d)=min(acos(d/rho),asin(4/9)). The strict bound
alpha>alpha_0=acos(122/135), with pi/8<alpha_0<pi/6,
is valid at the original closed upper R endpoint because d<61/60
is itself strict there. Both transverse endpoints of each real leaf
are included.

Each of the three completion squares has its entire connected open
arc longer than gamma and avoids all closed leaf arcs. Hence its
whole arc lies in exactly one of the three complement intervals.
There is no discarded disconnected completion component.

In the western interval, subtracting the two actual root arcs leaves
total available measure below
2pi/3+2nu-2alpha_0<5pi/12+2/25<4pi/9<2gamma.
This forbids two completion arcs whether or not the remaining set is
connected. The only delicate numerical comparison is
2/25<pi/36; pi>3 gives it with reserve 1/300 before multiplication
by the common positive scale.

Each small interval likewise has measure below
pi/4+1/25<4pi/9<2gamma, so each has capacity at most one.

At least one middle transverse extent is at least 1/2. If a>=1/2,
the real East leaf together with actual closed T blocks every angle
from 0 to beta_0=asin(4/9). The argument correctly treats both
alpha=beta_0 and alpha<beta_0, using the actual T face interval
epsilon<x<=d and 0<y<=1/2<=a. All endpoints are physically
occupied, including a=1/2.

Thus the upper completion arc would have to fit into an interval
shorter than D=pi/2+nu-alpha_0-beta_0. Section 6 proves D<gamma,
so that small gap is empty. Reflection handles b>=1/2; if both
equal 1/2, both gaps are empty. No reflected stress equation is
needed because this whole argument is geometric.

The resulting capacities are zero, one and one. They contradict
the three actual completion squares. This completes the stated
six-unit-to-nine-unit exclusion.

## 6. Full tilted endpoint comparison and exact arithmetic

I independently reconstructed both addition formulas for
A=alpha_0+beta_0 and for sin D=cos(A-nu).
The numerator of cos A is positive (greater than 744), which
justifies multiplying its radical upper bound by sqrt(6391)<80.
The exact resulting rational is 63059/97200, not an approximate
angle evaluation. The comparison with 649/1000 and then
sqrt(264)/25 is strict.

Both D and gamma are in (0,pi/2): A>nu gives the upper D bound,
and A<pi/3 gives its lower bound. Hence the sine comparison proves
D<gamma on the correct monotone interval. It includes both extreme
permitted leaf directions, every middle equality endpoint, and the
closed original radius limit.

The following 23 positive rational differences were independently
evaluated using exact fractions; they corroborate the hand inequalities.

| Check | Exact positive difference |
| --- | --- |
| Triple-cosine comparison | 753/31250 |
| Sine upper bound | 1/10000 |
| Universal center endpoint | 31/57600 |
| First far-domain endpoint reserve | 20669/360000 |
| Second far-domain endpoint reserve | 411/200000 |
| Alpha half-angle reserve | 1154/18225 |
| Eta half-angle reserve | 157/2025 |
| Outer-face radical reserve | 5/3072 |
| 59/81 versus sine gamma, squared | 443521/4100625 |
| Small-vertex coefficient | 1/25 |
| Root arc above thirty degrees | 1/900 |
| Leaf transverse-cap comparison | 259/18225 |
| Leaf alpha lower bound | 2429/72900 |
| sqrt(65)<129/16, squared | 1/256 |
| sqrt(3341)>289/5, squared | 4/25 |
| sqrt(6391)<80, squared | 9 |
| sqrt(217165)<467, squared | 924 |
| Final rational comparison | 119/486000 |
| Final sine comparison, squared | 1199/1000000 |
| Auxiliary western-gap reserve | 1/300 |
| Diagonal fixed-q endpoint bound | 863/160000 |
| Unit-strip sine comparison | 18616/50625 |
| Root-quadrant smaller coordinate | 503/1600 |

The exact scalar upper-bound numerator equals 63059 by rational
evaluation. None of these finite arithmetic checks is a packing
certificate or a substitute for the continuous proofs above.

## 7. Literal small-chart transfer and final acceptance scope

The aligned upper charts with q=epsilon or
q=sqrt(1+2epsilon)-1 meet the displayed theorem with s=0 and
0<q<=epsilon. Their lower reflections are literal.
For a tilted North leaf, the owned j direction has horizontal
component -s. At the strict root vertex P+j, the actual radial
direction is (P+j)/d; its horizontal component is
(epsilon-s)/d. The stated full bound follows from
s<=9epsilon/4 and d>1, including the own/strict boundary.
The lower chart is its physical reflection.

These calculations transfer the theorem to each original balanced
parallel-middle branch that independently has both small North/South
root charts. They do not establish the balancing hypothesis or
exclude a remaining West-type leaf assignment. The source explicitly
retains those obligations; this review does likewise.

I found no mathematical gap in the stated theorem or its explicit
scope. The complete stronger clearance and connected-arc statements
are accepted as independent force-free consequences at their printed
hypotheses. The manuscript may be adopted at the exact hash above.
It gives no original coarse/fine flag change on its own and does not
resolve the prior global selection compatibility or the global
sharp inequality/equality classification.

Only this independent review was written. No source, original graph,
force, mean, physical mask, ledger or remote state was altered.
No numerical pose search, angle mesh, packing certificate, Lean/Lake,
CI/workflow dispatch or merge was used.

