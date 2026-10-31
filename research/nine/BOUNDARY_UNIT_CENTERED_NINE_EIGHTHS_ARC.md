# Every high boundary unit contains a centered inner arc of halfwidth arctan(7/20)

Original theorem: October 27, 2026. Table-free proof adopted October 28, 2026 UTC.

**Status: complete accepted force-free hand theorem.** The statement and all
four original exports are unchanged. The operative proof now uses one affine
center-radius bound and one completed-square identity. Its former two
seven-entry Bernstein rows are no longer mathematical dependencies.

The complete expanded replacement is
`BOUNDARY_CENTERED_NINE_EIGHTHS_ARC_WITHOUT_COEFFICIENT_TABLES.md`, SHA-256
`a7227187917d53d0012bc04c002b0d24e33e5419da798381e899477a3861d1ab`.
Full root and separate independent reviews are
`REVIEW_UNIFORM_CHANNEL_ARC_AND_MOMENT_RESULTS_ROOT_2026_10_28.md` and
`REVIEW_BOUNDARY_CENTERED_ARC_TABLE_FREE_INDEPENDENT_2026_10_28.md`.
The exact source-version substitution and unchanged callers are recorded
in `UNIFORM_CHANNEL_ARC_MOMENT_CHECKPOINT_2026_10_28.json`.

## 1. Physical statement

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

## 2. One uniform coordinate inequality without coefficient tables

### 2.1. An affine bound on the actual center radius

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

### 2.2. One elementary two-square identity replaces the fourteen coefficients

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

## 3. The complete closed arc lies inside the actual square

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

## 4. The original mixed-gap angle comparisons are retained in full

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

## 5. Exact proof substitution and scope

The original source at commit `c31ecd109097dde3c8faa1db11a84655575e87ab` had
SHA-256 `1d0be3caa6be9257a6f4a3998281fe0c858229ccffde8ec6fa8942fae31aa8f6`.
That historical proof remains in Git. Its fourteen Bernstein coefficients
are replaced here by the identities of Section 2. The original section
numbers 1--4 and their mathematical conclusions are retained, so existing
callers can use this proof with their unchanged hypotheses. The exact
substitution record reconciles older review pins; it does not claim that
the historical source bytes equal the new source bytes.

This replacement alone closes no new original family. It retains all
physical squares, means and masks and does not resolve any caller's
additional routing or completion premise. No Lean compilation, CI or
computational exclusion certificate is an input.
