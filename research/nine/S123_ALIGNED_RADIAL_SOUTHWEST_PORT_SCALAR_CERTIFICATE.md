# Exact scalar cover for the aligned radial Southwest S123 star

Date: October 27, 2026.

**Status: complete exact rational scalar certificate, submitted for full
root and separate independent review.** Its original-force caller is
S_LEAF_C5_ALIGNED_SOUTHWEST_RADIAL_FAR_EXCLUSION.md. This is a finite
cover of unchanged scalar data. It neither selects a pose nor changes
an original normal, physical circle mask, or shared-side mean.

## 1. The complete closed input box and literal guards

Let

    0<=a<=29/100,       1/4<=K<=7,
    b=1-a,             L_a=sqrt(K^2+a^2),
    L_b=sqrt(K^2+b^2),
    epsilon=a^2/(L_a+K)=L_a-K,
    V=(2+epsilon)^2+1/4,
    N=(b^2-epsilon*K)/L_b,
    z=b*(K+epsilon)/L_b,
    S=N+1,             W=sqrt(V-S^2),
    lambda=z*S/W-N,     eta=z+1-W,
    D0=(K^2-a*b)/(L_a*L_b),
    E0=K/(L_a*L_b).

Keep the literal original-star guards

    0<=epsilon<=1/60,       17/4<=V<=1105/256,
    0<N<1,                 1/2<W<11/6,
    0<=lambda<=1,           0<=eta<=1.                 (1)

The actual B-center coordinates in the channel frame are

    B_n=(N+1/2)*D0-(W-1/2)*E0,
    B_f=(N+1/2)*E0+(W-1/2)*D0.

Impose the additional original boundary-path guard

    B_n<(9/50)*|B_f|.                                (2)

The caller proves (2) from the actual B--M--C boundary path,
and proves the entire input range before invoking this lemma.
The closed zero-a endpoint is included in the scalar cover;
the original caller has a>0. No radius identity is weakened
to an independent sampled parameter.

## 2. Original returns and the complete scalar conclusion

The far return has its actual support

    h_far=[S*(1-lambda)-(W-1)*eta]
              /sqrt((1-lambda)^2+eta^2).              (3)

For the two other returns put

    near: q_m=N,
    side: q_m=z*S/W,
    Q_n=q_m*D0-(W-1)*E0,
    Q_f=q_m*E0+(W-1)*D0.                             (4)

For each of those actual boundary contacts retain the necessary
sharp inner-radius guard

    Q_n^2+Q_f^2 >= (sqrt(V-1)-1)^2.                  (5)

The complete conclusions are

    D0>1/4,       h_far>61/60,                       (6)
    1/10<Q_n<3/4,       1/2<Q_f<43/50               (7)

for both retained returns (4). The denominator in (3) cannot
vanish under the definitions and (1): lambda=1 would imply
z=W and hence eta=1. Thus no free-direction endpoint is hidden
in the far-support formula.

## 3. The exact finite rational enclosure

The complete independently reproducible arithmetic is in

    certificates/s123_aligned_radial_southwest_port_certificate.py.

It uses only integer arithmetic, Fraction arithmetic and integer
square root. The outward interval arithmetic infrastructure is
the same elementary infrastructure as the separately specified
opposite-root certificate, but the two-variable inputs, guards,
formulas, tree and all conclusions here are independent.

Every interval endpoint is an integer divided by

    D=2^40=1099511627776.

Rational inputs are rounded down/up to this lattice. Addition
and subtraction use their endpoint rules. A product uses the
minimum and maximum of the four endpoint products with outward
division by D. The reciprocal of a positive interval with
numerator endpoints l,u is enclosed by
floor(D^2/u), ceil(D^2/l). A square uses zero as its lower
endpoint when its argument crosses zero. A square root uses
floor(sqrt(l*D)), ceil(sqrt(u*D)), with the lower radicand
replaced by zero if needed and an exact integer-square test
for the upper endpoint. Absolute value uses the complete
interval image, including intervals crossing zero.

Start with the entire closed box in Section 1. Calculate
epsilon and V, and discard a box only if their enclosures
exclude their ranges in (1). Otherwise intersect them with
those literal ranges. Calculate N and intersect it with
[0,1]; calculate W and intersect it with [1/2,11/6].
An empty intersection or a wholly negative W radicand
excludes that box. Calculate lambda and eta, discard a box
whose enclosure excludes [0,1], and otherwise intersect both
with [0,1]. These intersections preserve every actual star.

Calculate D0,E0,B_n,B_f. Discard a box if the lower endpoint
of B_n-(9/50)|B_f| is nonnegative, since its whole interval
then contradicts the strict original guard (2). Otherwise
accept the first two tests only when the full enclosures
prove (6). An unresolved divisor or test causes subdivision,
never a discard.

For each return (4), discard that feature if its squared-norm
upper enclosure is below the lower enclosure of the right
side of (5). For the near return first intersect W with
[1/2,1] and N with [sqrt(V-1)-1,1], using the lower
enclosure of the latter radical. Section 4 proves these
additional intersections from (5). An empty near-feature
intersection discards only that feature.

For every feature remaining in the box, accept only if the
four endpoint tests give all of (7). If any test remains
unresolved, bisect the original input interval whose width
multiplied respectively by (12,1) for (a,K) is largest;
break a tie by the first coordinate. Retain both children,
including their common midpoint. This is an exact binary
cover, not a collection of point tests.

The complete finite tree is

| Node classification | Count |
| --- | ---: |
| Accepted boxes | 13096 |
| Boxes excluded by literal guards | 5885 |
| Bisected boxes | 18980 |

There are 18981 terminal boxes, one more than the 18980
binary splits. Its maximum depth is 21. The numbers of
visited nodes at depths 0 through 21 are

    1,2,4,8,16,32,62,124,192,366,492,956,1338,2614,
    3822,7416,4638,7844,2756,4660,340,278.

The final outward endpoint extrema, as integer numerators
over D, are

| Scalar bound | Numerator |
| --- | ---: |
| Lower h_far | 1117856742672 |
| Lower D0 | 274960222659 |
| Lower Q_n | 109967782804 |
| Upper Q_n | 720801679289 |
| Lower Q_f | 708904628435 |
| Upper Q_f | 945578266343 |

Their exact positive reserves are

    h_far-61/60 >=18676031/1030792151040,
    D0-1/4 >=82315715/1099511627776,
    Q_n-1/10 >=20775033/1374389534720,
    3/4-Q_n >=103832041543/1099511627776,
    Q_f-1/2 >=159148814547/1099511627776,
    43/50-Q_f >=43338609/27487790694400.              (8)

Every displayed count and rational number is obtained by
the fully specified outward integer operations, not by
floating-point approximation. The checker asserts both
the terminal/split identity and all six strict reserves.

## 4. The exact near-return intersections

For the near return, orthonormality gives

    |Q|^2=N^2+(W-1)^2=V-2(N+W),
    (sqrt(V-1)-1)^2=V-2sqrt(V-1).

Thus (5) implies N+W<=sqrt(V-1). Since N>0, the identity

    (N+W)^2-(V-1)=2N(W-1)

forces W<=1. The original circle identity then gives
N+1>=sqrt(V-1). These are exactly the two extra interval
intersections used for that feature. Both equalities are
retained; no original endpoint is silently removed.

## 5. Scope

The caller checks every guard from the same actual six-body
component and keeps all three completion squares. In particular
the actual loaded M supplies the B--M--C order and the B--M
boundary-contact radius. This certificate neither shortens
that path nor replaces its two forces by an unloaded channel.
All actual side means, unique/physical circle conventions and
zero individual circle-weight endpoints remain in the caller.

This file is a complete scalar theorem at its stated guards,
not a numerical pose premise or a claim about the South direct
normal. No shared metadata, compilation, CI or remote action
is involved.
