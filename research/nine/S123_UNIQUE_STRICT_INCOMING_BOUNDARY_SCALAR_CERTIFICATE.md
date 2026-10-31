# Exact scalar separation for the unique strict-incoming boundary star

Date: October 27, 2026.

**Status: complete exact rational certificate, submitted for full root and
separate independent review.** The three parameter rows below are the
three actual original root identities used by
S_LEAF_C5_STRICT_INCOMING_UNIQUE_BOUNDARY_EXCLUSION.md. They include
the entire zero-channel-component side mean. No numerical pose, sampled
inequality or floating-point decision is used.

## 1. The three complete closed parameter boxes

Write e=epsilon, d=1+e and R2=(d+1)^2+1/4. The original radius
has 0<e<1/60. The certificate uses the larger closed interval
0<=e<=1/60 and retains its endpoints.

The actual incoming point and channel frame are

    P=(-A,F),       n=(x,-t),       f=(t,x).

There are exactly three scalar rows.

**Strict tilted channel.** On 0<=k<=31/60 put

    a=1-2e*(d-k^2)/(d+k)^2,       b=sqrt(1-a^2),
    A=a*(d-k),       F=1-d*b,
    p=b*k/(1-a*k),       x=1/sqrt(1+p^2), t=p*x.       (1)

**Tilted zero-component channel.** On the same entire k interval put

    a=(1-e)/d,       b=2sqrt(e)/d,
    A=a*(d-k),       F=1-d*b,       x=1,t=0.           (2)

This is the original side-mean domain. Formula (1) is not imposed
on it. The parameter k is not fixed to a vertex endpoint.

**Aligned South root.** On 1/2<=A<=61/60 put

    h=sqrt(e*(2A-e)),       F=1-h,
    x=1-e/A,       t=h/A.                             (3)

All square roots are nonnegative. The actual aligned identities give
x^2+t^2=1, as do (1)--(2).

## 2. Literal physical guards and the two claims

Only candidates satisfying the following actual strict guards matter:

    37/50<F<1,       1/2<A<1,
    K=(R2-A^2-F^2-1)/2,
    J=sqrt(A^2+F^2-K^2),       1/2<J<1,
    c=(A*J+F*K)/(A^2+F^2),
    s=(A*K-F*J)/(A^2+F^2),
    0<s<3/7,       A<c<=1,
    delta=J/(A+s).                                    (4)

The original geometric proof supplies every guard before invoking
this certificate. In particular c^2+s^2=1. The displayed formulas
are the actual B circle identity and actual incoming concurrence;
they do not introduce a second unit or a replacement mean.

For the near return define

    Q0=(c-A,F+s),
    Q0n=x*(c-A)-t*(F+s),
    V=t*c+x*(s-delta).                                (5)

For the B-owned return define its unchanged side mean

    Q1=(c-A-c*s*delta, F+s+c^2*delta)=(X,Y),
    Q1n=x*X-t*Y,       Q1f=t*X+x*Y,
    I=(X+c)^2+(Y+s)^2-R2,
    E=(d-Q1n)^2+(Q1f-1/2)^2-2.                       (6)

The complete scalar conclusions, in every one of (1)--(3), are

    Q0n>e  => V<0;
    Q1n>e  => max(I,E)>0.                             (7)

The second conclusion is a disjunction. It does not claim that the
same one of its two alternatives holds throughout a parameter row.
Both alternatives are literal physical contradictions in the caller.

## 3. Outward exact interval rules

The companion checker is

    certificates/s123_unique_strict_incoming_boundary_certificate.py.

Every interval is represented by two integers l,u, meaning the closed
interval [l/D,u/D], at the fixed denominator

    D=2^40=1099511627776.

Rational inputs are rounded down at their lower endpoint and up at
their upper endpoint. Addition and subtraction are exact integer
endpoint operations. Products take the minimum and maximum of all
four endpoint products and round outwards. A reciprocal is taken
only after its complete denominator interval is strictly positive.
For a nonnegative square root the lower integer is
floor(sqrt(max(0,l)*D)); the upper is the least integer whose square
is at least u*D. Integer square root and exact integer comparisons
implement both operations. Thus neither a square root nor any
arithmetic operation uses a floating-point approximation.

At each box the checker encloses (1), (2), or (3), and then (4).
It intersects only with the already proved physical bounds

    0<=a<=1, 37/50<=F<=1, 1/2<=A<=1,
    1/4<=J^2<=1, 0<=c<=1, 0<=s<=3/7.

An empty intersection discards the box. The other empty guards are
F<=37/50, A<=1/2, A>=1, J^2<=1/4, J^2>=1,
s<=0, c<=0, or A>=c, each certified for the entire box by its
outward endpoints. These are all necessary strict physical guards.

For a return whose enclosed Qn upper endpoint is at most the
enclosed e lower endpoint, the implication in (7) is vacuous
throughout that box. Otherwise the checker requires a strictly
negative upper endpoint for V, or a strictly positive lower endpoint
for at least one of I,E, respectively. A box passes only after both
complete return implications have passed. No contact or mask is
silently discarded because its interval overlaps an endpoint.

## 4. Exhaustive binary partition and exact margins

The initial boxes are exactly

    strict:  [0,1/60] x [0,31/60],
    side:    [0,1/60] x [0,31/60],
    aligned: [0,1/60] x [1/2,61/60].

An unresolved box is bisected at the exact rational midpoint of the
coordinate maximizing its width times the scale (20,1); the first
coordinate wins ties. Both closed children are retained. The checker
uses a stack with the upper child visited first. The following are
the exact complete results, recomputed from the saved checker.

| Actual row | Passed leaves | Empty leaves | Bisections | Maximum depth |
|---|---:|---:|---:|---:|
| Strict tilted channel | 918 | 65 | 982 | 14 |
| Entire tilted zero-component mean | 2695 | 128 | 2822 | 19 |
| Aligned South root | 161 | 23 | 183 | 11 |

For each row passed leaves plus empty leaves equals bisections plus
one. All leaves are therefore accounted for in the original closed
box. There is no unresolved leaf and no truncated parameter strip.

The next entries are positive integer numerators over the common
denominator D. The first column is a lower bound for -V whenever
the near-return guard can hold. The second is a lower bound for the
certified member of {I,E} whenever the owned-return guard can hold.

| Actual row | Near-return sign margin | Owned-return separation margin |
|---|---:|---:|
| Strict tilted channel | 13636713734/D | 166563583/D |
| Entire tilted zero-component mean | 3671383217/D | 18555532/D |
| Aligned South root | 3936317160/D | 44260172/D |

For completeness the visited-node counts, indexed by depth beginning
at zero, are respectively

    strict:
    1,2,4,8,14,26,44,82,136,226,298,408,324,330,62;

    side:
    1,2,4,6,12,22,38,68,112,188,278,412,532,634,
    668,758,664,672,370,204;

    aligned:
    1,2,4,8,12,20,30,50,58,80,62,40.

Every comparison is between exact integers or rational numbers.
The rational boxes are used only to prove the two scalar implications
(7); no physical pose, selected normal, application mean, circle mask,
or circle weight is changed by this comparison.

