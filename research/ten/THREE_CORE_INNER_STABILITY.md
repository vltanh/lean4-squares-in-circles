# A small-circle stability bound for three cores with no outer trace

This is a proved conditional reduction, not a proof of the ten-square bound.
It adapts the elementary arc computation in
[Chapter 6, Three squares](https://github.com/vltanh/lean4-squares-in-circles/blob/4bea747b3efa13c869b956cb28435efaf21526fa/docs/proof/06-three.md)
to a slightly larger disk. The source is pinned to the base commit of this
research branch; the identities needed here are reproduced below.

Put

    r = sqrt(1 + 1/sqrt(2)),   s = 3/8.

**Zero-protrusion hypothesis:** all three core squares are wholly contained
in the closed disk D_r, including their boundaries. Having only their centers
in the open unit disk does not imply this hypothesis.

Every unit square contained in the closed disk D_r about the origin contains
an open arc of the circle C_s of angular length at least 5*pi/8. Consequently,
three interior-disjoint unit squares contained in D_r leave at most pi/8 of
C_s outside these three arcs. The angular distance between any two arc
midpoints is between 5*pi/8 and 3*pi/4.

## Local coordinates

Rotate and reflect with one square, so its center has coordinates a>=b>=0.
Containment is

    (a+1/2)^2 + (b+1/2)^2 <= r^2.                 (1)

Since b>=0 and r^2-1/4=(1+sqrt(2))^2/4, (1) gives a<=1/sqrt(2).
Let Delta=r^2-425/256. Expanding at (1/2,5/16) gives

    (a+1/2)^2+(b+1/2)^2-425/256
      = (16*a+13*b-193/16)/8
        +(a-1/2)^2+(b-5/16)^2.

Thus 16*a+13*b<=193/16+8*Delta.

## The origin is not in the square's interior

Here a>=1/2. Set

    u=(a-1/2)/s,   v=(1/2-b)/s,
    m=4*(sqrt(2)-1)/3.

Then 0<=u<=m, and the tangent inequality becomes

    v >= c+(16/13)*u,   c=1/2-(64/39)*Delta > 2/5.          (2)

For the last strict bound, sqrt(2)>7/5 gives
Delta<97/1792<39/640.
In particular v>0 and hence b<1/2.

The square contains the open C_s arc of length

    L = A + min(A,V),   A=acos(u),   V=asin(min(v,1)).

This follows directly by intersecting C_s with the near and lower square
sides: a-1/2=s*u<s, both far sides lie beyond C_s, and the permitted chart
angles run from -min(A,V) to A.

The exact inequality m<cos(5*pi/16) gives A>5*pi/16.
For completeness, after squaring positive sides it reduces to

    128*sqrt(2)-174 > 9*sqrt(2-sqrt(2)),
    62882 > 44463*sqrt(2),

and the last inequality follows from
62882^2-2*44463^2=229186>0. The first left side is positive since
sqrt(2)>7/5>174/128.

If V>=A, then L=2*A>5*pi/8. Otherwise, write

    x=pi/8+asin(u).

Since u<cos(5*pi/16)=sin(3*pi/16), x<5*pi/16<pi/2. Moreover,

    sin(x) = sin(pi/8)*sqrt(1-u^2)+cos(pi/8)*u
           <= sin(pi/8)+u < 2/5+u <= v.

Here sin(pi/8)<2/5 follows from sqrt(2)>34/25. If v>=1, then V=pi/2>x;
otherwise sine is increasing on the relevant interval and V>=x. Hence

    A+V >= pi/2-asin(u)+pi/8+asin(u) = 5*pi/8.

Thus every exterior square supplies an arc of the required length.

## The origin is in the square's interior

Now a<1/2. Put P=(1/2-a)/s and T=(1/2-b)/s. Both are positive.
The square contains the open arc of length

    L=pi/2+asin(min(P,1))+asin(min(T,1)).

If either P or T is at least 1, then L>=pi>5*pi/8. Otherwise asin(x)>=x,
and Cauchy--Schwarz in (1) gives

    a+b+1 <= sqrt(2)*r = sqrt(2+sqrt(2)),
    L >= pi/2+(8/3)*(2-sqrt(2+sqrt(2))) > 5*pi/8.

The final strict comparison can be checked using pi<22/7 and sqrt(2)<10/7:

    sqrt(2+sqrt(2)) < sqrt(24/7) < 415/224,
    (8/3)*(2-415/224) = 11/28 > pi/8.

The middle comparison squares to 7*415^2>24*224^2, with difference 1351.

## Three-square consequence

The three supplied open arcs lie in disjoint square interiors, hence are
disjoint. Each has length at least 5*pi/8, so their total length is at least
15*pi/8 and the uncovered angular measure is at most pi/8.
For two arc midpoints, the shorter circular distance is at least the sum
of their half-widths, hence at least 5*pi/8. The third arc and the two
half-widths on the longer route give the upper bound

    2*pi - 5*pi/8 - 5*pi/16 - 5*pi/16 = 3*pi/4.

## An outer equality type is excluded

The D-type equality square in
[CENTER_RADIUS_REDUCTION.md](CENTER_RADIUS_REDUCTION.md) has center norm 1
and, in its own frame, center coordinates (1/sqrt(2),1/sqrt(2)). Its near
side offsets are both (sqrt(2)-1)/2. Therefore its intersection with C_s
is an open arc of angular length

    pi/2 - 2*asin(m),   m=4*(sqrt(2)-1)/3.

The inequality m<cos(5*pi/16)=sin(3*pi/16), proved above, gives

    pi/2 - 2*asin(m) > pi/2 - 3*pi/8 = pi/8.

Thus such a square cannot coexist with the three zero-protrusion cores:
their three arcs already occupy at least 15*pi/8 on C_s. This conclusion
uses disjointness on the small circle and does not require an eight-square
ring or the side-line compatibility argument.

## Scope

In a hypothetical subcritical ten-packing with exactly three centers in the
open unit disk, seven outer-center squares occupy at least 7*pi/4 on C_r.
The inner squares may still protrude through the remaining pi/4. The lemma
above covers the subcase in which all three inner squares are wholly inside
D_r. It does not justify treating that subcase as the whole problem.
