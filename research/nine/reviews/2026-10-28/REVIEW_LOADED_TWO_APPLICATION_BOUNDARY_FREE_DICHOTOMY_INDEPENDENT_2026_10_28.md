# Independent review: the complete boundary-neighbor-free loaded-star trichotomy

Date: October 28, 2026 UTC.

Reviewer: `return_scalar_independent` continuation.

**Verdict: PASS for the complete frozen theorem below, with no mathematical
blocker and no required source repair.** The acceptance is of the full
arbitrary-degree, at-most-two-actual-applications statement on

    sqrt(2) < R < 1 + sqrt(2),

including the one-application case, the nonparallel proper-concurrence
case, and the exact remaining parallel case. There is no boundary-neighbor
premise in this acceptance. This review does not close a graph/load family
or accept a caller that suppresses any of the three alternatives.

## 1. Exact frozen source, independence and review boundary

The complete source independently read and accepted is

    LOADED_TWO_APPLICATION_FULL_STAR_BOUNDARY_FREE_CONCURRENCE_DICHOTOMY.md
    SHA-256 3808b2b767a9e15c7270b50c4fbbb434ae0d69fe42c567d4da01f7d167f7fa78

The author supplied this completed frozen source before this review. The
reviewer did not contribute discovery, construction advice, a new lemma,
or a repair to it. The source attributes the actual-point radial test
and the enlarged coefficient range to root; neither attribution is
treated as independent acceptance. I read all ten sections and checked
the whole theorem after freezing. I supplied a complete first PASS
verdict before writing this review. No change to the frozen source was
requested or made.

I also read the complete physical stress contract and the complete
predecessor and predecessor recovery review. Their exact current hashes
are:

| File | SHA-256 |
|---|---|
| `PHYSICAL_CONTACT_STRESS.md` | `d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5` |
| `LOADED_TWO_APPLICATION_FULL_STAR_PROPER_CONCURRENCE.md` | `942ed38a7452f35e95839cc79ea15ed97091114495e9a3ab9c232ae8255a0ea0` |
| `REVIEW_LOADED_TWO_APPLICATION_FULL_STAR_PROPER_CONCURRENCE_RECOVERY_AUDIT_2026_10_28.md` | `b91f1283a238615a9a05fb849add9dd0823a9a60c4b95e3351d2512c214b6e4b` |

The frozen source hash and all three source/provenance hashes printed
in the new manuscript match the actual current bytes. The old source
and its review identify the
argument's provenance. Their boundary-neighbor exclusion is not an
operative step in the new theorem. In particular, the new proof does not
inherit an old exclusion of coincident applications or parallel groups.

The operative physical contract is explicitly stated in the new theorem:
actual contained unit squares with disjoint open interiors, actual common
support normals and actual common applications, nonnegative physical
circle-corner weights of positive total, and the full force and origin
moment equations. The implication is conditional on this contract. The
new proof does not need the old radius window, a stress sparsity bound,
a body-pair degree bound, a normal-selection rule, or any entire graph
exclusion from the physical stress source.

## 2. Original quantities and exact grouping

The theorem retains every original positive term `mu_i*n_i` at its actual
`P_i`, with `mu_i>0`. It retains a full shared-side mean as that actual
application, with endpoints included. It does not replace a mean by an
endpoint or identify two merely nearby applications.

For each distinct literal application `T`, it defines only

    G_T = sum_(P_i=T) mu_i*n_i,
    W_T = sum_(P_i=T) mu_i.

These are algebraic sums over original terms. The full original
equations give exactly

    F + sum_T G_T = 0,
    sum_T det(T,G_T) = 0.

The moment identity uses the common actual point in each group. It
would generally be false if forces at distinct points were grouped
without retaining their moments. No such operation occurs here.

The statement correctly distinguishes an exact group line from each
of its original constituent lines. If two or more nonparallel original
normals share `T`, the resulting line through `T` is not claimed to be
a new physical contact to a hypothetical square. Nor does the theorem
claim that its concurrence lies on every separate original line unless
the concurrence equals `T`. True degree two is a direct special case
because its two distinct-application groups have one term each.

## 3. Circle masks, unchanged origin and support reach

### 3.1 Complete physical circle masks

Loadedness ensures at least one actual corner lies on the containing
circle. In its orthonormal side coordinates about the same unchanged
origin, ordering the axes gives

    K = [a-1,a] x [b-1,b],
    a >= b >= 1/2,
    a^2+b^2 = R^2.

The two adjacent-corner comparisons give `a,b>=1/2`. The diagonally
opposite corner could also have radius `R` only if `a+b=1`, which,
under those inequalities, would force `a=b=1/2`; this is incompatible
with `R>sqrt(2)`. An adjacent corner is also a circle corner exactly
when its corresponding coordinate is `1/2`. Thus the one-corner and
two-corner masks exhaust the physical possibilities. Strict convexity
of the disk excludes a non-corner point on its boundary.

In the one-physical-corner mask,

    F = k*(a,b),  k>0.

In the full two-physical-corner mask, with

    K = [d,a] x [-1/2,1/2],
    a=d+1=sqrt(R^2-1/4),

the full circle load is

    F = k*(a,eta),
    k=2*(lambda_+ + lambda_-)>0,
    eta=(lambda_+ - lambda_-)/(2*(lambda_+ + lambda_-)),
    -1/2 <= eta <= 1/2.

The second *physical* corner remains in that mask even when its
individual coefficient is zero. In particular, `eta=+/-1/2` is not
converted into the one-physical-corner case. Both masks have `F!=0`.

The radius assumptions imply

    a >= R/sqrt(2) > 1,
    1/2 <= b < 1+1/sqrt(2),

in the ordered chart, and imply `d>0` in the two-corner chart. All
coordinate changes used here are orthonormal changes about the same
origin; no containing-circle center is translated.

### 3.2 Physical circle points cannot be pair applications

For either inward unit edge `u` from a physical circle corner `Z`,
containment of `Z+u` gives `Z.u<=-1/2`. Consequently `-Z` has strictly
positive components along both inward edges. A sufficiently short
segment `Z-epsilon*Z` lies in the open square. Two actual squares
containing that same `Z` would contain the same short segment in their
open interiors. Thus no actual pair application can be any physical
circle corner, irrespective of its own circle multiplier.

### 3.3 The group support bound uses the real neighbors

At a side-interior application all outward normals of `K` have its
one side direction. At a vertex they belong to one closed outward
right-angle quadrant. Their scalar products with its unit bisector
are at least `1/sqrt(2)`. Therefore

    |G_T| >= W_T/sqrt(2) > 0.

The sum is itself a supporting vector of `K` at `T`, because it is
a positive sum of supporting inequalities at that identical point.

For every original neighbor `L_i` at `T`, the direction `n_i` is
inward for `L_i`. At a vertex of `L_i`, its two inward orthonormal
edge components are nonnegative and individually at most one. Hence
`T+n_i` belongs to the actual unit. At a relative side-interior
application the complete inward normal segment of length one lies
in the actual unit. The vertex argument includes side endpoints.
This proves the reach statement for every original support feature,
including endpoints of the normal cone and full shared means.

Each `T+n_i` is in the same containing disk, so their original
positive weighted average `T+G_T/W_T` is in that disk. Projecting
onto `g_T=G_T/|G_T|` gives

    T.g_T + |G_T|/W_T <= R,
    T.g_T <= R-1/sqrt(2) < R/sqrt(2).

The last strict inequality is equivalent to `R<1+sqrt(2)`. Thus an
actual group of support height at least `R/sqrt(2)` is impossible.
This proof does not posit any artificial unit of normal `G_T` and
does not require even one real neighbor to be physically boundary.

## 4. The one-application alternative is retained and proved

If all original applications equal `P`, the full equations give
`G_P=-F` and `det(P,F)=0`. For every physical circle corner `Z`,
the actual unit diameter gives `|Z-P|^2<=2`. Thus

    P.Z = (R^2+|P|^2-|Z-P|^2)/2
        >= (R^2+|P|^2-2)/2 > 0.

The strict step uses exactly `R>sqrt(2)`. Summing with the full
nonnegative circle coefficients of positive total gives `P.F>0`.
Since `F!=0`,

    P = ((P.F)/|F|^2)*F,

with strictly positive coefficient. Taking `q=P` proves the stated
positive radial conclusion, membership in the actual unit, and the
common incidence of every original line. Every original ray has
length zero. The source correctly retains this alternative rather
than applying an old boundary-neighbor hypothesis to exclude it.

## 5. The parallel alternative is exactly the stated radial mask

For two distinct applications, both exact groups are nonzero by
Section 3. If their vectors are parallel, their nonzero sum `-F`
makes their common axis the axis of `F`.

With one physical circle corner, a group in direction `+(a,b)`
would expose that unshareable corner. Hence both groups would have
to point in direction `-(a,b)`, which exposes the same unique
opposite corner. This contradicts the two distinct applications.

With two physical corners and `eta!=0`, the positive `F` direction
exposes one of the two unshareable outer corners; the negative
direction exposes the same unique inner corner for both groups.
Again distinct applications are impossible. This includes both
`eta=+/-1/2` cases.

Only `eta=0` remains. An East-directed group has supporting height
`a`. Here `a^2=R^2-1/4>R^2/2`, so that group is excluded by the
real-neighbor bound. Both groups are therefore West and lie on
the full inner side `x=d`.

At the upper inner endpoint every original outward normal has a
nonnegative vertical component; at the lower inner endpoint each
has a nonpositive vertical component. A zero aggregate vertical
component with strictly positive original coefficients forces
every such component to be zero. The only unit outward normal
there with zero vertical component is West. The same conclusion
is immediate at a relative side-interior application. Thus every
original normal, not only either aggregate direction, is West.

The full original corner mask then gives
`lambda_+=lambda_->0`. Writing the two actual applications as
`(d,p)` and `(d,q_0)`, the original origin moment is exactly

    W_P*p + W_Q*q_0 = 0.

Both weights are strictly positive and the heights are distinct.
Consequently one height is strictly negative and the other strictly
positive. Neither can be zero. Their original allowed height range
includes the endpoints `-1/2` and `1/2`. This proves precisely

    -1/2 <= p < 0 < q_0 <= 1/2

after relabeling. The two force lines are distinct horizontal lines;
the source correctly asserts no finite concurrence here. It asserts
no boundary status for the real neighbors.

## 6. Nonparallel groups: radial identity and full unique-corner cover

Nonparallel exact group lines have a unique intersection `q`. Because
their moments are at their original common applications,

    det(P,G_P)+det(Q,G_Q)
      =det(q,G_P+G_Q)
      =-det(q,F)=0.

This establishes a radial *line* only. The later geometric steps
are needed for positive radial direction and proper rays; neither
is inferred from this determinant identity alone.

For the one-physical-corner chart put `q=tau*(a,b)`. Exactly the
interval

    1-1/a <= tau <= 1

places `q` in the actual rectangle. Its lower endpoint is strictly
positive because `a>1`. To check the exterior cover independently,
label the four corners

    I=(a-1,b-1), U=(a-1,b), V=(a,b-1), Z=(a,b),

whose closed outward cones are respectively SW, NW, SE and NE.
A line through a corner in one of those cones can extend in
either sign. At a relative side-interior point it is horizontal
or vertical. These facts give the following entire exterior cover:

| Radial exterior region | Possible corner/side normal-line points before removing unavailable points |
|---|---|
| `tau>1` | `I` and `Z` only |
| `tau<1-1/a`, `q_y<b-1` | `I` and `Z` only |
| `tau<1-1/a`, `q_y=b-1` | `I`, `Z`, and `V` with East normal |
| `tau<1-1/a`, `b-1<q_y<b` | left-side point at height `q_y`, right-side point with East normal, `V`, and `Z` |

There is no missing region with `q_y>=b` in the last three rows,
since `tau<1` and `b>0`. The physical circle point `Z` is always
unavailable. Every East-normal point has support height `a` and
is excluded by the group support bound. The first three rows
therefore leave at most one actual application.

In the last row, two distinct applications would force one group
at `V`. Its outward unit normal is

    n=(cos(theta),-sin(theta)),
    tan(theta)=(b*tau-b+1)/(a*(1-tau)).

The fraction is increasing in `tau`, with derivative
`1/(a*(1-tau)^2)>0`, and at `tau=1-1/a` its value is `(a-b)/a`.
Thus its actual value is strictly between zero and `(a-b)/a`.
If `a=b` this entire candidate strip is impossible. Enlarging
to the closed interval from zero to `(a-b)/a` loses no endpoint.

### 6.1 Independent verification of the expanded coefficient range

Put `e=a-b>=0`. The support height is

    f(theta)=a*cos(theta)-(b-1)*sin(theta).

On the enlarged interval its numerator after division by the
positive cosine is `a-(b-1)*tan(theta)>0`. For `b<=1` this is
immediate; for `b>1` its smallest value is `N/a`, where

    N=a^2+e*(1-b)
     =(a^2-a*b+b^2)+(a-b)>0.

Therefore `f''=-f<0`, and its minimum occurs at an endpoint.
The first endpoint is `a>=R/sqrt(2)`. At the other,

    f=N/D,  D^2=a^2+e^2.

For an independent algebraic check, use

    a=b+e,
    N=b^2+(b+1)*e+e^2,
    R^2=2*b^2+2*b*e+e^2,
    D^2=b^2+2*b*e+2*e^2.

Expansion by powers of `e` gives

    2*N^2-R^2*D^2
      =e*(4*b^2-2*b^3)
       +e^2*(2+4*b-3*b^2)
       +e^3*(4-2*b),

which is the source's printed factorization. This check is a hand
polynomial expansion, not a computational geometric certificate.

Throughout `1/2<=b<B=1+1/sqrt(2)<2`, the first and third
coefficients in its bracket are positive. The middle coefficient
is a concave quadratic; on the larger closed interval `[1/2,B]`
its endpoint values are

    13/4,
    3/2-sqrt(2)>0.

The last strict inequality follows from `9/4>2`. Concavity places
every intermediate value above the smaller endpoint value. Hence
the entire expression is nonnegative for `e>=0`, including `e=0`.
As `N,D>0`, its second endpoint support height is at least
`R/sqrt(2)`. Both endpoint heights, and therefore every height
on the closed interval, contradict the strict real-neighbor bound.

This closes the last exterior region at the enlarged radius range.
It does not rely on the predecessor's smaller bound `b<3/2`.

### 6.2 Positivity and proper rays in the unique-corner mask

The interval for `tau` has been forced, so `q` belongs to the actual
unit and is a strictly positive multiple of `F`. For either group,
its original supporting inequality gives `G_T.(q-T)<=0`.
Since `q-T` lies on its group line, `T-q` is a nonnegative multiple
of `G_T/|G_T|`. Equality is allowed and is exactly a zero ray.
Both proper-ray conclusions therefore follow for the original
exact groups.

## 7. Nonparallel groups: complete two-corner cover and exterior rays

Write `q=tau*(a,eta)` in the complete two-corner chart. The first
claim is `tau>=d/a>0`. If `tau<d/a`, then `q_x<d`.

For `|q_y|<1/2`, the only non-circle candidates are the inner-face
point at height `q_y` and the horizontal East-normal outer-face
point. At `q_y=+/-1/2`, the inner candidate is the corresponding
inner endpoint. The outer point is then a physical circle point;
in all cases any East candidate is also excluded by support height.
If `q_y>1/2`, the only possible corner lines are from the upper
inner corner and the opposite lower outer circle corner. If
`q_y<-1/2`, the only possibilities are the lower inner corner and
the opposite upper outer circle corner. Vertical side lines cannot
reach `q_x<d`, and horizontal side lines supply no extra candidates
in the outside-height regions. Thus every such region leaves at
most one allowed actual application. This proves `tau>=d/a>0`.

If `d/a<=tau<=1`, then `d<=q_x<=a` and `|q_y|<=1/2`.
The concurrence is in the actual unit, and the same supporting
half-plane argument proves both nonnegative rays.

For `tau>1`, one has `q_x>a`. The full right-hand exterior cover is:

| Height of `q` | Possible non-circle points |
|---|---|
| `q_y>1/2` | only the lower inner corner; the other possible corner is the upper outer physical circle point |
| `q_y<-1/2` | only the upper inner corner; the other possible corner is the lower outer physical circle point |
| `|q_y|<=1/2` | points on the inner face, including its endpoints, and a possible East-normal outer-face point |

The first two rows cannot supply two distinct actual applications.
The East-normal possibility in the last row is again excluded by
its height. Thus every surviving exterior concurrence has exactly
the asserted location

    q_x>a,  |q_y|<=1/2,

and both actual applications lie on the inner face. For either such
application `T`, the vector `T-q` has strictly negative horizontal
component. Its actual outward group normal also has strictly
negative horizontal component: West at a side-interior point;
at an inner endpoint a zero horizontal component would require a
vertical line, which cannot pass through `q_x>a`. Parallelism of
the vectors and agreement of this component's sign prove a
strictly positive ray length for both groups. The radial multiple
is positive by `tau>=d/a>0`.

All side endpoints and closed cone endpoints are included in this
argument. In particular, equality `q_y=+/-1/2` in the exterior
strip is covered. The individual zero circle-weight cases
`eta=+/-1/2` were retained throughout. In those cases an exterior
`tau>1` would give `|q_y|=tau/2>1/2`, so the complete cover itself
excludes exterior concurrence. They remain valid nonparallel
cases with concurrence inside the actual unit. This explains the
endpoint coverage without claiming that a nonexistent exterior
endpoint-weight case must be realized.

The source does not impose equal corner weights on the general
nonparallel case. It also correctly avoids asserting `q in K`
for a surviving exterior two-corner concurrence.

## 8. Broad-domain corollaries and literal caller limits

The original closed packing interval is contained strictly in the
new open interval. Indeed

    (79/40)^2=6241/1600>2,
    1105/256<5<3+2*sqrt(2)=(1+sqrt(2))^2.

Both original closed radius endpoints are therefore retained.
No assertion has been checked or accepted at the new endpoints
`R=sqrt(2)` or `R=1+sqrt(2)`: the proof uses strict inequalities
at those respective bounds.

For a true loaded degree-two unit, two distinct nonparallel original
forces give the direct proper concurrence, with no boundary-neighbor
premise. If their original applications coincide, the entire
one-application alternative is retained. If their exact groups are
parallel at distinct applications, the radial inner-face exception
must be retained. Its original means cannot be replaced by vertices
to remove the weighted height condition.

For two forces owned by perpendicular sides of the actual unit, the
intersection of their horizontal and vertical normal lines takes
one coordinate from each actual application, so it belongs to that
unit even when an application is an endpoint. The determinant
identity gives radial alignment, and the diameter test of Section 4
gives its positive direction. The source's special corollary is
therefore valid, including coincident applications.

For higher true degree, the full unchanged set of original
applications must genuinely have cardinality at most two. A caller
cannot obtain the premise by deleting an unwanted positive force,
moving a shared mean, or merging two different points. A multi-term
group concurrence also does not become concurrence of all of its
individual original lines unless their application equals `q`.

The stated application to a genuinely loaded E2 of the three-load
four-spoke pentagon is a valid local implication: it has its two
original A and D pair terms, whether either neighbor is physically
boundary or both are clear. The new theorem alone does not select
which alternative that E2 has, eliminate the radial parallel case,
or close either original H4_D0 load family. Those caller limits are
part of this acceptance.

## 9. Verification record and adoption boundary

This was a full independent mathematical review of the frozen
source, not a review of a selected scalar step or of an earlier
narrower theorem. The actual-point reach statement, masks,
unshareability, all cone regions, boundary equalities, signs,
polynomial identity and enlarged interval were checked directly.
Every original positive term and every individual zero corner
coefficient remains in the argument.

Only source reading and file/Git provenance inspection were used.
No old checker, numerical search, angle mesh, computational
exclusion, Lean or Lake invocation, CI, workflow, commit, or remote
operation was used. The recovered saved checkout and all proof
sources were left unchanged. This new review is the only artifact
written by this reviewer for this task.

**Accepted result:** all three alternatives of frozen source
`3808b2b767a9e15c7270b50c4fbbb434ae0d69fe42c567d4da01f7d167f7fa78`
on the entire stated radius domain. No mathematical blocker or
required repair remains. Current root adoption and every later
whole-family caller remain separate from this review.
