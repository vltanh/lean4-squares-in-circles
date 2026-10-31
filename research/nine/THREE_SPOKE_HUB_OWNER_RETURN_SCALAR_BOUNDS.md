# Exact coupled scalar bounds for the three-spoke hub-owner return

Date: October 28, 2026. Author: rooted_blocks.

**Status: complete exact scalar theorem, frozen for full independent
and root review.** The proof eliminates the original side-mean
parameter monotonically and then uses a complete, finite outward
rational interval cover in two variables. It uses no sampled pose,
floating-point sign, unproved extremum or upper bound on the original
k. The physical caller and its contact/mask cover are separate.

## 1. Whole scalar domain and conclusion

Let the actual scalar parameters satisfy

    a>b>0, a^2+b^2=1,
    (a-b)/(a+b)<p<min(b/a,(1-b)/a),
    H=b+a*p, t=1-H,
    x=1-(b/a)*(1+p)>0,
    y0=a-t,
    v=t/(1-p*H),
    E=sqrt(1+x^2), L=sqrt(1+v^2),
    g=(x+v)/(E*L), h=(1-x*v)/(E*L).                (1)

For any unchanged parameter 0<lambda<=1 put

    A0=(1+b+x*y0)/E,
    B0=(x*(1+b)-y0)/E,
    xi=B0+lambda*h,
    d=1-xi,
    k=1-A0+lambda*g.                              (2)

Here d is the scalar complement 1-xi; it is not the radial-leaf
distance used in some other sources. Assume only

                             k>0.                 (3)

In particular no k<1, k<=1, or xi bound is needed for this theorem.
The original lambda=1 endpoint is included. The physical k=1
zero-proper-distance endpoint is retained in the hypotheses and
will be excluded by the conclusion.

**Theorem.** Throughout the full domain (1)--(3),

    d>1/3,    0<k<1/8,    h>3/5,    g>d.          (4)

The result keeps all the coupling in (1). For example v, x and
y0 are not independently varied or replaced by numerical bounds.

## 2. Exact elimination of lambda

The hypotheses give 0<p<b/a<1 and 0<H<1. Therefore

    0<t<1,
    1-p*H>1-H=t>0,
    0<v<1,
    0<x<1.

Consequently g>0, h>0, and the exact identity

                         g^2+h^2=1               (5)

follows by expanding (x+v)^2+(1-xv)^2.

Define the two endpoint comparisons

    d1=1-B0-h,
    k1=1-A0+g,
    F=g^2-g+B0*g+h*(A0-1).                        (6)

Since lambda<=1,

    d>=d1,  k<=k1.

The actual k>0 therefore forces k1>0. Also direct substitution of
(2) into (6) gives the exact coupled identity

                       g*(g-d)=F+h*k.             (7)

It is enough to prove the following four inequalities on the
two-variable domain (1), with only the necessary extra guard k1>0:

    d1>1/3, k1<1/8, h>3/5, F>0.                  (8)

Indeed the first three imply the corresponding claims in (4).
Then h,k,g>0 and (7) give g>d. No division by k, lambda, xi,
A0-1 or a potentially zero proper length is used. No lower bound
on lambda is manufactured by an independent relaxation.

## 3. One compact rational rectangle contains the entire actual domain

Put z=b/(1+a). Then

    a=(1-z^2)/(1+z^2),
    b=2z/(1+z^2).

The condition a>b>0 implies

    0<z<sqrt(2)-1<5/12,

where the last comparison has exact squared reserve 1/144.

For the lower bound let r=b/a=2z/(1-z^2), increasing in z.
The hypotheses require

    (1-r)/(1+r)<p<r.

If z<=19/100, then r<=3800/9639. The function
(1-r)/(1+r)-r is strictly decreasing for r>0, and at this endpoint
it is

    (1-3800/9639)/(1+3800/9639)-3800/9639
                   =5213921/129538521>0.

This is incompatible with the required interval for p. Thus every
actual parameter pair belongs to

                    (19/100,5/12) x (0,1).        (9)

The interval cover below uses a closed outward enlargement of
this rectangle. It includes its edges and some nonphysical points.
Nonphysical points are removed only by necessary strict guards
whose entire enclosing interval is nonpositive; otherwise the
four inequalities are proved on the whole retained box.

## 4. Complete exact interval certificate

The full checker is

    certificates/three_spoke_hub_owner_return_scalar_bounds.py
    d073ebfa7d1c27f8c4272a9d3b5c56e20f8de1a1ae310a8d7d790ff5c91acf99

It has no external mathematical dependency and uses only Python
integer arithmetic, integer square roots, and finite binary
subdivision. This section specifies its complete enclosure and
acceptance rules so that the cover can be independently rebuilt.

### 4.1. Exact outward operations

Set M=2^48=281474976710656. An interval [l,u] in the checker
means the closed real interval [l/M,u/M], with integer l,u.
Rational constants are enclosed by floor(M*n/d), ceil(M*n/d).

Addition and subtraction use the exact endpoint formulas.
Multiplication takes the minimum and maximum of all four integer
endpoint products and divides by M with floor and ceiling.
Division is used only when the denominator lower endpoint is
strictly positive; it encloses all four endpoint quotients using
integer floor and ceiling. Squaring has lower endpoint zero if
the interval crosses zero, and otherwise the smaller endpoint
square. Upper endpoints use the larger square. For a nonnegative
interval the square-root endpoints are

    floor(sqrt(l*M)), ceil(sqrt(u*M)),

computed exactly by integer isqrt and an integer square comparison.
These operations include negative numerators and zero endpoints.
They are all rigorous interval inclusions.

The single root box, in scaled integer coordinates (zlo,zhi,plo,phi),
is exactly

    (53480245575024, 117281240296107,
     0, 281474976710656).                          (10)

It is the outward rounding of the closed rectangle in (9).

### 4.2. Necessary guards and safe denominators

On a box the checker first computes a,b,p0=(a-b)/(a+b), H,t,x
from their exact formulas. It can mark a box impossible only
when the upper endpoint of one of the following necessary
strictly positive quantities is nonpositive:

    a-b,
    p-p0,
    b/a-p,
    t=1-H,
    x,
    1-p*H.                                       (11)

The last guard follows from the original domain as proved in
Section 2. The first rational denominators a, a+b and 1+z^2
are strictly positive throughout the root box; the checker
requires their computed lower bounds to be positive at every
use. If the interval for 1-pH still reaches zero, the box is
subdivided instead of dividing through it or deciding a sign.

For boxes surviving (11), intersecting the computed t and x
intervals with [0,infinity) is valid because their actual values
are strictly positive. Their zero endpoints are retained in
the enlarged enclosure. The checker then computes the original
v,y0,E,L,A0,B0,g,h with outward operations.

Finally it may mark a box impossible if the entire computed k1
interval is nonpositive. This is valid because (3) and lambda<=1
imply the strict k1>0 guard. No upper bound on k is introduced.

### 4.3. Three identical formulas tighten one enclosure

For F in (6) use the following three algebraically identical
expressions:

    F1=g^2-g+B0*g+h*(A0-1),
    F2=(1+b-v*y0)/L-h-g+g^2,
    F3=(1+b-v*y0)/L-h-g+1-h^2.                    (12)

The equality F1=F2 follows by the exact identity

    A0*h+B0*g=(1+b-v*y0)/L.

It is obtained by expanding both numerators over E^2*L and
cancelling the common factor 1+x^2. Equality F2=F3 is (5).
The intersection of their three outward interval enclosures
therefore still contains the actual F. It is not a selection
of independent values of g,h or of a physical parameter.

The four acceptance margins on a retained box are

    d1-1/3,
    1/8-k1,
    h-3/5,
    F.                                           (13)

A box is accepted only if all four computed lower endpoints are
strictly positive. This proves (8) at every actual point of
that whole box. No center or sample value is ever tested.

### 4.4. Complete subdivision and terminal counts

Any box which is neither proved impossible nor accepted is
bisected. Compare its two side lengths after normalizing by
the two root-box widths. Split the larger normalized side,
choosing z in a tie. The midpoint is the integer floor of
the two endpoint integers' average. Both children contain
that common endpoint, so their union is the full parent box.
The lower child is processed first. The checker cannot accept
an unresolved box at a depth limit; it raises an error instead.

The complete run terminates with the following exact counts:

| Terminal decision | Number of whole boxes |
| --- | ---: |
| All four margins strictly positive | 219 |
| p-p0 has nonpositive upper endpoint | 115 |
| k1 has nonpositive upper endpoint | 109 |
| b/a-p has nonpositive upper endpoint | 27 |
| t has nonpositive upper endpoint | 3 |
| x has nonpositive upper endpoint | 2 |
| Total terminal boxes | 475 |

There are 474 splits, 949 total visits and maximum depth 20.
The root is therefore fully covered: terminal_count=split_count+1
and visit_count=2*split_count+1, and every terminal has one of
the rigorous decisions above. No unresolved box or omitted
boundary remains.

Among the 219 positive boxes, the minimum certified lower
endpoints of the four margins (13) are, respectively,

    5702628015/M,
    39611230475/M,
    41648853359044/M,
    195083550495/M.                               (14)

All are strictly positive. These are conservative exact interval
reserves, not claimed extrema of the original functions.

The deterministic terminal path/decision/margin digest is

    2fa607a00554e12f173e2b44108fbf20c0b102a224262239bb96487f8f779d62.

The checker can emit the complete 475-leaf cover, including
each integer box and its decision, using --leaf-output. The
author's complete readback leaf file is

    /tmp/rooted_blocks_H3_hub_owner_scalar_leaves.json
    1d6b388ad701b0a625f14c94a4b3daf7afa8d49f31f99954d414dc9b64604357.

That file is retained in the recovery checkpoint. The full
proof does not depend on a precomputed leaf file: the frozen
checker regenerates the entire finite cover and verifies each
leaf from (1), (6), (10)--(13) using the exact operations above.

By interval inclusion at each operation and induction over
the exhaustive binary subdivisions, every actual parameter
pair satisfying (1) and k1>0 lies in a terminal positive box.
Equations (8) are consequently proved over their full domain.

## 5. Whole original parameter conclusion

Restore the actual lambda, without selecting a new mean. The
relations d>=d1 and k<=k1 and the certificate give

    d>1/3, 0<k<1/8, h>3/5.

The exact identity (7), with h>0,k>0 and certified F>0,
gives g*(g-d)>0. Since g>0, it follows that g>d. This proves
the complete theorem (4), including lambda=1. Any original
k=1 is excluded by the proved upper bound rather than by
an added hypothesis. The original physical condition 0<xi<1
was never needed; it may remain in a caller without being
used to restrict the certificate's domain.

## 6. Pure algebraic radius consequence for the physical caller

For any 0<R<25/12 and the scalars in (4), define

    E_R=(g-d)^2+(1+h)^2
         +2R*((g-d)*d-(1+h)*k)/sqrt(d^2+k^2).

Because g-d,d,k are positive,

    E_R>(1+h)*(1+h-2R*k/d).

The proved k/d<3/8 gives 2R*k/d<25/16. Since 1+h>8/5,

    E_R>(8/5)*(8/5-25/16)=3/50>0.                (15)

This is a scalar consequence only. The physical source must
still identify its real B point, actual unique or two-corner C
mask, proper directions and the corresponding radius formula.
The present theorem introduces no new physical contact or force,
does not shorten a star, and does not assert a whole graph or
load-family exclusion by itself.

All proof arithmetic is exact and finite. No Lean compilation,
CI, workflow, remote mutation, shared metadata change, numerical
pose premise or post-extraction normal/mean change is used.
