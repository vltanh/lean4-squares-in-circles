# Independent full review: four near-origin units have total capacity at most eight

Date: October 27, 2026.

Reviewer: rooted-blocks agent, independent of the author and root review.

**Verdict: ACCEPTED.** I read the complete source
FOUR_NEAR_ORIGIN_UNITS_CAPACITY.md, checked every geometric and
angular implication, and independently recomputed every stated
rational reserve with exact fractions. The theorem is valid for
arbitrary interior-disjoint contained unit squares with R^2<=1105/256:
four distinct actual units meeting closed D_(1/60) imply total
capacity at most eight. It requires no stress, graph, load or common
orientation premise.

## 1. Every actual center bound and closed endpoint is correct

For an actual unit with center z, the farthest corner norm squared
is |z|^2+1/2+|z.u|+|z.v|, which is at least
|z|^2+|z|+1/2. Solving the resulting increasing quadratic gives
the stated universal bound |z|<M=91/60. The exact comparison
(121/60)^2-1041/256=31/57600 is positive. The existence of a
contained unit itself supplies the nonnegative square-root domain.

Each selected near unit has an actual point of norm at most 1/60,
including a side or vertex endpoint. Its center is at distance
at most 1/sqrt(2) from that point. Thus its radius is strictly
less than m=3619/5000, because
(m-1/60)^2-1/2=8449/225000000>0. This strict rational slack
is why the source retains the closed small-disk boundary.

The distance of distinct actual centers is at least one by their
disjoint open incircles. A selected center cannot be zero or have
the same direction as another selected center: either would violate
that separation since their radii are below m<1. All following
angular directions and cyclic gaps are therefore well defined.

## 2. The four selected directions surround O and every radius exceeds s

The function f(a,b)=(a^2+b^2-1)/(2ab) bounds the cosine of
the minor angle between centers of radii a,b. On (0,m]^2 it
is strictly increasing in either variable because the relevant
derivative numerator is a^2-b^2+1>0. The exact values are

    f(m,m)=597161/13097161,
    57(13097161)-1250(597161)=86927>0.

Thus every pairwise minor angle of the selected centers is
strictly greater than alpha=acos(57/1250). Each cyclic gap is
also greater than alpha, including a hypothetical gap above pi.
Since alpha>pi/3, such a gap cannot reach pi: its three remaining
gaps would already total more than pi. All gaps are consequently
minor and lie strictly between alpha and beta=2pi-3alpha.
This proves the required surrounding order without assuming that
the four original square frames agree.

If one selected radius were at most s=6577/10000, monotonicity
would give each of its adjacent angle cosines strictly below
f(s,m)=-4354427/95208652. The exact cross-product reserve
1250(4354427)-57(95208652)=16140586 is positive, so both
adjacent gaps would exceed pi-alpha. The other two exceed alpha,
and their sum would exceed 2pi. Hence every selected radius is
strictly greater than s, as claimed.

The auxiliary inequalities pi/2<beta<3pi/4 are also exact.
The first follows from alpha<pi/2. For the second,
c<1/4<cos(5pi/12), and the latter radical comparison follows
from sqrt(6)>1+sqrt(2). No decimal angular estimate is required.

## 3. All other centers are genuinely outside the unit circle

The maximum selected angular gap is below beta, so every other
nonzero center direction is within angle less than beta/2<3pi/8
of some selected direction. The selected radius a obeys
a<m<3/4<2cos(3pi/8), with the last comparison equivalent to
sqrt(2)<23/16 after squaring positive quantities.

For fixed a and that angle, the squared center distance is the
convex quadratic t^2+a^2-2ta cos(omega) in the other radius t.
It is strictly below one at both t=0 and t=1, using respectively
a<1 and a<2cos(omega). It is therefore below one throughout
0<=t<=1. This contradicts actual center separation. The proof
also excludes a center at O directly, so every other center has
the full strict radius range 1<t<M. This step is necessary for
the unequal-radius capacity estimate later, and it is complete.

## 4. Exactly four possible angular intervals remain

For t in (1,M) and a in (s,m), f(t,a) increases in t. The
function f(M,a) decreases in a on this interval because its
derivative numerator a^2-M^2+1 is negative: m<3/4 and M>3/2
give a strict bound already. Thus every remaining center has
minor angular distance greater than gamma=acos(k) from every
selected center, where the exact value is

    k=f(M,s)=222794623/256503000.

Inside each of the four original gaps, a gamma interval is
removed at both ends. The available interval has length less
than theta=beta-2gamma. Each remaining center is in its unique
original cyclic gap; a gap too short to leave an interval holds
no center. There is no wraparound or endpoint duplication.

The comparisons k>1737/2000>sqrt(3)/2 and k<1 give
0<gamma<pi/6. Hence pi/6<theta<3pi/4, since beta>pi/2.
Any two points in one available interval therefore have their
ordinary minor angle strictly below theta, in the range where
cosine decreases. This checks the domain needed by the final
cosine estimate rather than relying on an approximate angle.

## 5. Every rational and trigonometric reserve checks exactly

The addition formula is correctly signed:

    cos(theta)=(4c^3-3c)(2k^2-1)
      +(1-4c^2)sqrt(1-c^2) 2k sqrt(1-k^2).

Here cos(3alpha)=4c^3-3c is negative, while sin(3alpha) is
negative, explaining the positive second displayed product.
The first product's negative sign is retained when applying
the strict upper bound 2k^2-1<509/1000.

Independent exact-fraction checks give

    k-1737/2000 = 8707/102601200 > 0,
    4343/5000-k = 9707/641257500 > 0,
    (1737/2000)^2-3/4 = 17169/4000000 > 0,
    1-c^2-(9989/10000)^2 = 11943/100000000 > 0,
    1-4c^2-2479/2500 = 129/1562500 > 0.

For u=4343/5000, the function 2x sqrt(1-x^2) is decreasing
on (1/sqrt(2),1). The exact square comparison

    4u^2(1-u^2)-(4303/5000)^2
      =55615750799/156250000000000>0

therefore proves the required strict lower bound at k. Also
2u^2-1=12723298/25000000<509/1000. All the factors being
squared or multiplied in these comparisons have their stated
positive signs.

Substitution gives exactly

    -(171/1250)(509/1000)
      +(2479/2500)(9989/10000)(4303/5000)
      =97850131493/125000000000,

which exceeds b=1957/2500 by 131493/125000000000. Thus
cos(theta)>b has a genuine strict exact reserve. The source
does not use a floating-point angle, numerical pose, angle grid
or optimized sample to infer any geometric conclusion.

## 6. The full annular interval capacity includes unequal radii

For two remaining centers in one available interval, their minor
angle is below theta, so the true cosine is greater than b. Their
squared distance is strictly below

    F(t_1,t_2)=t_1^2+t_2^2-2b t_1t_2.

This polynomial is separately convex on the full closed rectangle
[1,M]^2, so its maximum is at a rectangle corner. The supplied
checks cover all four corners, including the unequal ones:

    F(1,1)=543/1250<1,
    b-M/2=367/15000>0,
    F(M,M)=4496583/4500000<1.

The middle comparison gives F(1,M)=F(M,1)<1. The final
corner has exact reserve 1139/1500000 after reduction. Thus
every pair in one available interval would have actual center
distance strictly below one. No common outer radius has been
assumed. Each of the four intervals holds at most one center,
so there are at most four other units and at most eight total.

## 7. Accepted physical scope

All inequalities are derived from the actual occupied squares,
their centers, the enclosing radius and the four real small-disk
points. Every orientation of every unit is permitted. The selected
near units need not be loaded, genuine leaf roots or graph-adjacent;
they need only be four distinct original squares. Closed small-disk,
square-side, vertex and circle endpoints are retained by the strict
rational reserves.

The theorem therefore applies to any four distinct original units
meeting D_epsilon with 0<=epsilon<1/60, once an exact caller has
proved those four physical incidences. It changes no actual normal,
force, graph degree, circle mask, zero atom or mean. No Lean
compilation or CI was used. The independent arithmetic check used
exact rational identities only, and every substantive inequality
already has its human derivation in the reviewed source.
