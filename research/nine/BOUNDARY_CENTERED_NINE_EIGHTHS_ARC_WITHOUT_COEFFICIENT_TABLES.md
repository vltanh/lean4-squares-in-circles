# A centered inner arc from one affine bound and two completed squares

Date: October 28, 2026 UTC. Author: pentagon continuation.
Read base: `c31ecd109097dde3c8faa1db11a84655575e87ab`.

**Status: complete proposed hand replacement for the centered-arc theorem,
submitted for full root and separate independent review.** This source
proves the complete mathematical exports of
`BOUNDARY_UNIT_CENTERED_NINE_EIGHTHS_ARC.md` without either of its seven-entry
Bernstein rows. It uses no coefficient-sign table, numerical enclosure,
angle subdivision, pose search, or computational proof premise.
No original gate, old source, or old review is changed here.

## 1. Exact whole-domain statement

Put

    Q=1105/256,       rho=9/8,       beta=atan(7/20).

Let E be any actual closed unit square contained in the disk of squared
radius Q about the original origin. If its actual center c satisfies
|c|>=27/20, the entire **closed** radius-rho arc centered at the direction
of c with halfwidth beta lies in the **open** interior of E.

The theorem includes every square orientation, circle mask, contact owner,
original mean and endpoint. There is no force, graph, degree or circle-load
premise. Consequently it applies to a physical boundary square throughout

    sqrt(17)/2 <= R <= sqrt(1105)/16.

Every actual unit and every original datum stays unchanged. The proof
below is about the actual square, not an auxiliary favorable orientation.

## 2. An affine bound on the actual center radius

Choose signs of E's own orthonormal axes so that its center coordinates
are r(x,y), where

    r=|c|>0,       x,y>=0,       x^2+y^2=1.

The actual farthest corner gives

    r^2+r(x+y)+1/2 <= Q.                                (1)

Let t=x+y. Then 1<=t<=sqrt(2). Define

    L(t)=28/15-(7/20)t.

We claim the complete strict bound

    r < L(t).                                          (2)

The function z -> z^2+tz+1/2 is strictly increasing for z>=0, and L(t)>0
on this interval. It is therefore enough to show its value at L(t)
strictly exceeds Q. Direct expansion gives

    L(t)^2+t L(t)+1/2-Q
      = -(91/400)t^2+(14/25)t-19121/57600 =: P(t).       (3)

This is a concave quadratic in t, so it is at least the smaller of its
two endpoint values on [1,sqrt(2)]. Those values are strictly positive:

    P(1)=31/57600>0,

    P(sqrt(2))=-(91/200)+(14/25)sqrt(2)-19121/57600
               >3799/1440000>0.                         (4)

For the second comparison use sqrt(2)>141/100, whose squared reserve is
2-(141/100)^2=119/10000>0. Equations (3)--(4) prove (2) on the complete
orientation interval, including its endpoints.

This affine bound is a separate uniform physical consequence of disk
containment. It needs neither a high center radius nor physical boundary
contact. Only r>0 was used to choose its center direction.

## 3. One elementary two-square identity replaces the fourteen coefficients

We next prove exactly the scalar estimate used in the centered-arc
construction, with a uniform strict margin:

    (r-135/128)x+(3/8)y < 1/2.                           (5)

In fact the left side is at most 1/2-11/1840. By (2), x>=0, and

    28/15-135/128=1559/1920 <13/16,

it is enough to bound

    (13/16)x-(7/20)x^2-(7/20)xy+(3/8)y.                 (6)

For every real x,y satisfying x^2+y^2=1, the following exact identity
holds:

    1/2-(13/16)x-(3/8)y+(7/20)x^2+(7/20)xy
      = (9/20)(x+(7/18)y-65/72)^2
        +(23/720)(y-85/92)^2+11/1840.                   (7)

To check (7) directly, the right side expands to

    (9/20)x^2+(7/20)xy+(1/10)y^2
      -(13/16)x-(3/8)y+2/5.

Subtract the left side. The difference is precisely
(1/10)(x^2+y^2-1), which is zero on the actual unit-circle domain.
Both displayed squared terms have positive coefficients, and
11/1840>0. Thus (6) is at most 1/2-11/1840. This proves (5).

There is no hidden positivity table in this argument: (7) is one
completed-square identity whose remainder is a single positive rational.
The proof works across the whole quadrant at once. The cases x=0 or y=0
are included without a limit or deleted endpoint.

## 4. The complete closed arc lies inside the actual square

For beta=atan(7/20), exact trigonometry gives

    cos(beta)=20/sqrt(449)>15/16,
    sin(beta)=7/sqrt(449)<1/3.                            (8)

The squared integer reserves are
400*256-225*449=1375>0 and 449-49*9=8>0, respectively.

Let |tau|<=beta. In the actual positively oriented own frame, a
radius-rho point at angular displacement tau from c's direction has
first coordinate relative to c

    (rho cos(tau)-r)x-rho sin(tau)y.                     (9)

Because r>=27/20>rho, the first term is nonpositive. The positive
part of (9) is therefore bounded strictly by
rho sin(beta)<3/8<1/2.

For its negative part, use (8), x,y>=0, and (5):

    (r-rho cos(tau))x+rho sin(tau)y
      <=(r-rho cos(beta))x+rho sin(beta)y
      <=(r-135/128)x+(3/8)y
      <1/2.                                             (10)

The same calculation, with x,y exchanged and tau's sign reversed,
gives both strict bounds for the second own coordinate. Thus both
coordinate deviations lie strictly between -1/2 and 1/2. This is exactly
membership in the open interior of the original unit E.

The argument includes tau=beta and tau=-beta, so the entire **closed**
angular arc is contained in the **open** square. No disjointness or
capacity conclusion is obtained merely by naming center angles; each
caller must still supply the appropriate actual arc routing.

For the stated physical boundary consequence, an actual circle corner
is at distance 1/sqrt(2) from c. Therefore

    r>=R-1/sqrt(2)>103/50-71/100=27/20,

where sqrt(17)/2>103/50 and 1/sqrt(2)<71/100. Their squared reserves are
4/625 and 41/10000. This verifies the entire original high-radius
boundary domain, including R=sqrt(17)/2.

## 5. The original mixed-gap angle comparisons are retained in full

The prior source also exports two comparisons with alpha=atan(2/5):

    alpha+beta>2pi/9,
    atan(6)-alpha-beta<2pi/9.                            (11)

They require no coefficient table and are included here so this source
replaces the complete old mathematical export rather than only Section 2.
The ordinary addition and subtraction formulas give, with each angle
in (0,pi/2),

    alpha+beta=atan(75/86),
    atan(6)-alpha=atan(28/17),
    atan(6)-alpha-beta=atan(441/536).

The rational comparisons 441/536<5/6 and 75/86>6/7 reduce (11) to

    atan(5/6)<2pi/9<atan(6/7).                           (12)

Both arctangents are between pi/6 and pi/4; their triples are in the
second quadrant. The triple-angle formula gives

    tan(3 atan(5/6))=-415/234,
    tan(3 atan(6/7))=-666/413.

The strict squared comparisons

    415^2-3*234^2=7957>0,
    3*413^2-666^2=68151>0

and tangent monotonicity on that quadrant compare the triples with
2pi/3, proving (12) and both statements in (11). Every branch and
strict endpoint is thereby accounted for.

## 6. Precise dependency replacement and count boundary

At the read base the source being replaced is

    BOUNDARY_UNIT_CENTERED_NINE_EIGHTHS_ARC.md

with SHA-256 recorded below. Its orientation proof used two degree-six
Bernstein rows, seven coefficients in each row, for one polynomial on
two closed half-angle intervals. Sections 2--3 above instead give one
whole-domain affine radius bound and the identity (7). No half-angle
subdivision or coefficient-sign list remains a premise of this theorem.

The statement, high-radius boundary corollary, exact beta, strict
open-interior membership of the closed arc, and both additional angle
comparisons are unchanged. After complete reviews, any caller of those
exports may substitute this source without changing its geometric
hypotheses or conclusions. The fourteen Bernstein coefficients can
therefore be removed from that caller's operative centered-arc dependency
chain. Historical proof and review files may remain for provenance.
This is a replacement of this exact fourteen-coefficient proof, not a
claim that all other scalar certificates in the repository are retired.

The source makes no new original fine or coarse closure claim by itself.
It neither assumes nor proves the remaining pentagon pocket capacities,
chorded-hexagon families, global sharp bound or equality classification.
It preserves all actual squares and physical masks; no force, original
mean or selected normal is changed. No Lean compilation, CI, workflow
dispatch, or remote write is performed.

The exact old source SHA-256 at the read base is

    1d0be3caa6be9257a6f4a3998281fe0c858229ccffde8ec6fa8942fae31aa8f6.

That old proof is used only to identify the exports and the replaced
fourteen-coefficient dependency; it is not a mathematical premise of
Sections 1--5, which are self-contained elementary square geometry,
quadratic identities, and trigonometry.
