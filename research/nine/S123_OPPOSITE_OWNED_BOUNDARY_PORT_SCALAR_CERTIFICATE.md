# Exact scalar enclosure for the opposite-root owned boundary star

Date: October 27, 2026.

**Status: complete exact rational scalar certificate, submitted for full
root and separate independent review.** This is a scalar lemma for
the original-star caller named in Section 6. It does not select a
pose, contact normal, circle mask, or side mean. All comparisons in
its finite enclosure use integers and rational numbers; no sampled
configuration or floating-point tolerance is a premise.

## 1. Closed rational box and the literal star guards

Let real A,F,p,V satisfy

    -1/60<=A<=1/60,       37/50<=F<=1,
    13/40<=p<=1,         17/4<=V<=1105/256.

Define

    L=sqrt(1+p^2),       r=p/L,       s=1/L,
    H=A*r+F*s,           z=-A*s+F*r,
    S=H+1,              W=sqrt(V-S^2),
    lambda=z*S/W-H,      eta=z+1-W.                    (1)

The actual-star guards are

    A^2+F^2<1,       1/2<H<33/35,       z>0,
    0<=lambda<=1,    0<=eta<=1.                       (2)

In particular W is positive: even on the enlarged closed H range,

    V-S^2>=17/4-(68/35)^2=2329/4900>0.

Put B=1-F, and define the rational nonnegative majorant

    vbar=B*(1-p)/[p*(1-B-(3/5)*B^2)].                 (3)

Its denominator is positive since 0<=B<=13/50. The first
conclusion of the lemma is

    vbar<p.                                           (4)

## 2. The three original return formulas and the conclusions

The far-return support is the following actual scalar:

    h_far=[S*(1-lambda)-(W-1)*eta]
              /sqrt((1-lambda)^2+eta^2).              (5)

Whenever the denominator in (5) is nonzero, the guards imply

    h_far>61/60.                                      (6)

The near and side returns have coordinates Q=(Q_1,Q_2) in
the original A-axis frame. They are exactly

    near: q_m=H,
    side: q_m=z*S/W,
    Q_1=q_m*r-(W-1)*s,
    Q_2=q_m*s+(W-1)*r.                               (7)

For either return impose its literal physical boundary-contact
guard

    |Q|>=sqrt(V-1)-1.                                (8)

For the near return we may also impose W<=1. Section 4 proves
this is already a consequence of (8), so it is not a new physical
restriction. For every unchanged direction ratio 0<=v<=vbar,
rotate Q to the actual channel frame by

    Q_n=(Q_1-v*Q_2)/sqrt(1+v^2),
    Q_f=(v*Q_1+Q_2)/sqrt(1+v^2).

Then the complete scalar conclusion is

    1/8<Q_n<3/4,       1/10<Q_f<9/10.                 (9)

The lower f bound here is deliberately weaker than 1/2. The
later strict-C-inner caller uses the actual chord condition;
both sides of 1/2 in (9) give the same strict 2/5 chord bound.

## 3. Explicit finite rational certificate

The complete arithmetic is specified by the accompanying file

    certificates/s123_opposite_owned_boundary_port_certificate.py.

It contains no import or operation for floating-point arithmetic.
Here is the full enclosure rule, including its splitting rule and
all discard conditions, so the finite assertion is independently
reproducible.

Every interval endpoint is an integer divided by

    D=2^40=1099511627776.

For a rational input q, round its lower endpoint down and its
upper endpoint up on this lattice. Addition and subtraction use
the usual endpoint rules. For multiplication take the minimum
and maximum of the four endpoint products, dividing by D with
outward rounding. For a positive interval [a,b], its reciprocal
has endpoint numerators floor(D^2/b), ceil(D^2/a). Squaring
uses zero as the lower endpoint if the interval crosses zero.
For a nonnegative interval with numerator endpoints a,b, the
square-root endpoint numerators are floor(sqrt(a*D)) and
ceil(sqrt(b*D)); integer square root and an exact square test
give those two integers. Thus every enclosure is rigorous.

Begin with the entire closed rational box in Section 1. At
each box calculate (1). Discard the box if its enclosure proves
any of

    A^2+F^2>=1,       H<=1/2,       z<=0,
    lambda<0,        eta<0,        eta>1,

or if the relevant interval becomes empty after intersection
with the literal ranges (2). Intersect the H interval with
[1/2,33/35], and the lambda and eta intervals with [0,1].
These operations retain every possible original star.

Calculate (3) and (5). A box is accepted only if its outward
enclosures prove (4),(6). If a required divisor is not yet
proved positive, subdivide instead of discarding it.

For each return (7), first check whether its enclosure already
excludes (8). It is enough for this discard to prove

    |Q|^2<(sqrt(13/4)-1)^2.

For the near return, discard that feature if W>1; otherwise
intersect its W interval with [0,1] and its H interval with
[sqrt(13/4)-1,33/35]. The latter lower bound follows from
S^2=V-W^2>=V-1. Calculate (7) with those intersections.

For every remaining feature a box is accepted only if Q_1,Q_2
have positive lower endpoints and the following four complete
interval tests succeed:

    (Q_1-vbar*Q_2)/sqrt(1+vbar^2)>1/8,
    Q_1<3/4,
    Q_2/sqrt(1+vbar^2)>1/10,
    Q_2+vbar*Q_1<9/10.                               (10)

For positive Q_1,Q_2, the first rotated coordinate decreases
with v, while the two elementary upper/lower bounds for the
second coordinate in (10) hold for all 0<=v<=vbar. Thus
(10) proves (9), rather than testing one chosen direction.

If neither a discard nor all acceptance tests succeed, bisect
the original input interval whose width, multiplied respectively
by (4,3,3,1) for (A,F,p,V), is largest. In a tie take the first
coordinate in that displayed order. Both children, with their
common midpoint retained, replace the parent. Therefore this
is an exact cover of the initial closed box, including every
weak endpoint. No interval is removed because a sample fails.

The complete resulting finite tree has

| Result | Number of nodes |
| --- | ---: |
| Accepted boxes | 2833 |
| Boxes excluded by literal guards | 37 |
| Bisected boxes | 2869 |

There are 2870 terminal boxes, exactly one more than the 2869
binary splits. The maximum depth is 18. The full node count
at depths 0 through 18 is

    1,2,4,8,16,32,56,104,166,288,348,378,528,764,
    808,678,750,642,166.

The extrema of the final rigorous endpoint enclosures, given
as integer numerators over the common denominator D, are

| Enclosed scalar | Bound numerator |
| --- | ---: |
| Lower bound for h_far | 1119395769889 |
| Lower bound for p-vbar | 123819593436 |
| Lower bound for Q_n | 137441585016 |
| Upper bound for Q_n, via Q_1 | 747744982675 |
| Lower bound for Q_f | 549357926969 |
| Upper bound for Q_f | 989553193737 |

In particular the exact strict reserves are

    h_far-61/60 >=23384224751/16492674416640>0,
    p-vbar >=30954898359/274877906944>0,
    Q_n-1/8 >=328943/137438953472>0,
    3/4-Q_n >=76888738157/1099511627776>0,
    Q_f-1/10 >=2197033820957/5497558138880>0,
    9/10-Q_f >=36356307/5497558138880>0.               (11)

All listed integers are the output of the stated outward
rational operations on the finite tree. The supplied checker
also asserts the terminal/split identity and each positive
reserve. This is an exact scalar proof by a finite cover,
not an optimization assumption or a numerical pose argument.

## 4. Why the near-return restriction is automatic

For the near return (7), orthonormality and (1) give

    |Q|^2=H^2+(W-1)^2=V-2(H+W).

The square of the right side of (8) is

    (sqrt(V-1)-1)^2=V-2sqrt(V-1).

Thus (8) implies H+W<=sqrt(V-1). Since H>0,

    (H+W)^2-(V-1)=2H(W-1)

forces W<=1. This proves the exact additional intersection
used for that feature; it keeps equality W=1.

## 5. Normal signs retained for the actual caller

In the caller the outgoing near normal is proportional to

    -lambda*m-eta*j,
    m=(r,s),       j=(-s,r),       0<eta<1,
    0<=lambda<eta.

The owned-side normal is -j. Thus both have positive first
and negative second A-axis components, and their downward
slope is at least p=r/s. By (4), every actual channel rotation
0<=v<=vbar leaves their channel components strictly

    g_n>0>g_f.

No actual mean or normal is varied by this comparison.

## 6. Scope

The original-force application is
S_LEAF_C5_THREE_LOAD_OPPOSITE_ROOT_OWNED_BOUNDARY_SIDE_EXCLUSION.md.
That caller proves every guard, the original complete return
cover, and the literal comparison 0<=t/x<=vbar before invoking
this scalar lemma. It separately invokes the sharp physical
boundary-contact radius for the unchanged B--M edge.

The certificate does not remove the actual M load, give it a
false degree, assume a new B--C contact, or alter the original
channel support. The A-owned side-mean channel t=0 remains
inside its v=0 endpoint. All nine original physical units and
every original mean/mask are retained.
