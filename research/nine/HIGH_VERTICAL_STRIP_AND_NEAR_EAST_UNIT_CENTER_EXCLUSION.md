# A high vertical strip and a nearby East support cannot contain two disjoint units

Date: October 28, 2026.

**Status: complete force-free hand proof, submitted for full independent
and root review.** All coordinates refer to the original circle origin.
No force, load, degree, contact mean or circle-mask assumption is used.

Let actual unit squares be contained in the closed disk of radius R, with

    R²=(2+epsilon)²+1/4,  0<=epsilon<1/60.

Put d=1+epsilon. The sharp contained-unit center bound gives

    |center|<=d+1/2<91/60.                         (1)

## 1. The complete high vertical-strip center bound

Suppose an actual unit D lies in x>=1-epsilon. Then

    89/60<center(D)_x<91/60,
    |center(D)_y|<3/25.                            (2)

Here is a full proof, including every orientation. In an aligned frame
the x interval is [H,H+1] with H>=1-epsilon. The two outer corners give

    |center(D)_y|<=sqrt(1/4+8epsilon)-1/2<3/25.     (3)

The last strict comparison follows from

    (31/50)²-23/60=2/1875>0.

For an oblique frame, reflect y if necessary and write the actual
minimum-x vertex as (H,q), with inward axes

    f=(a,b), j=(b,-a),  0<a<=b, a²+b²=1.

Write w=a+b and Delta=b-a. The center bound (1) and H>=1-epsilon
give w<=1+4epsilon<16/15. Since a+b is increasing for a<=b,

    a<1/14, b>199/200, Delta>139/150.               (4)

For the first comparison, (1+sqrt(195))/14>16/15 follows from
195-(209/15)²=194/225>0. The middle comparison follows by
squaring b>sqrt(195)/14. For the last,

    Delta²=2-w²>194/225,
    194/225-(139/150)²=79/22500>0.

Put Y=center(D)_y=q+Delta/2. The actual opposite and lower-right
corners imply

    Y<=sqrt(R²-(H+w)²)-Delta/2,
    Y>=w/2-sqrt(R²-(H+b)²).                        (5)

Replacing H by 1-epsilon weakens both bounds. In the upper expression
let X=1-epsilon+w and S=sqrt(R²-X²). Where its radicand is nonnegative,
its derivative with respect to a is

    [-X*Delta/S+w/2]/b<0.                          (6)

Indeed X>119/60, Delta>139/150, S<31/50 and w<16/15, so the
negative term strictly dominates. If S=0, the asserted comparison
follows by continuity; a negative radicand already forbids containment.
At a=0 the upper expression is sqrt(1/4+8epsilon)-1/2.

For the lower expression put X0=1-epsilon+b and
S0=sqrt(R²-X0²). Here S0>=1/2 and X0<=2. Its derivative is

    [Delta/2-X0*a/S0]/b
      >[139/300-2/7]/b>0.                         (7)

Thus its minimum is its a=0 value 1/2-sqrt(1/4+8epsilon).
Equations (3), (5)--(7) prove the vertical part of (2). The horizontal
part follows from the directional halfwidth being at least 1/2 and
(1). This proof uses actual corners only and includes both physical
circle-corner masks, whether or not any corner is loaded.

## 2. The full nearby-normal exclusion

Let a second contained unit T lie in

    n dot x>=1-epsilon,
    |n|=1, n_x>0, 0<=n_y<=7/20.                    (8)

Then D and T cannot have disjoint open interiors.

Write Z=center(T), A0=89/60 and M=91/60. Its n projection is
strictly greater than A0 and |Z|<M. Its transverse projection
therefore has absolute value less than

    sqrt(M²-A0²)=sqrt(1/10)<8/25.

Also n_x>=sqrt(351)/20>187/200; the last squared reserve is
131/40000. Consequently

    Z_x>A0*(187/200)-(8/25)*(7/20)=15299/12000.     (9)

For its upper vertical coordinate, at any fixed n the expression

    u*n_y+sqrt(M²-u²)*n_x

is strictly decreasing for u>=A0 in its real domain. Its derivative
is n_y-u*n_x/sqrt(M²-u²), which is negative using the preceding
bounds. Thus

    -8/25<Z_y<A0*(7/20)+8/25=1007/1200.            (10)

Combining (2), (9), (10) and the common center-norm bound gives

    |Z_x-center(D)_x|<2901/12000,
    |Z_y-center(D)_y|<1151/1200.

Their squared distance is therefore strictly below

    (2901/12000)²+(1151/1200)²
       =1-3104099/144000000<1.                    (11)

Both units contain the open disk of radius 1/2 about their actual
centers. Equation (11) makes those two disks intersect, contradicting
interior disjointness. The conclusion includes n_y=0 and every closed
support-side endpoint in (8).

## 3. Exact imported scope

The sole imported input is the force-free contained-unit center bound
in END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md, Section 1 only, current
SHA-256 6f3459eaf4ca425ee2001ddb27e1ba7a1b5eb0003548498f48c610776554d3bb.
Its loaded-triangle equations in later sections are not used.

This is a physical two-unit exclusion, not a replacement of either
unit by a force or a point. No normal selection, numerical certificate,
movement, completion argument, shared metadata, remote mutation,
compilation or CI is involved.
