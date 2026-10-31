# The exact radius-dependent diagonal bound for a nine-eighths inner arc

Date: October 27, 2026.

**Status: complete force-free hand lemma, submitted for full root and
separate independent review.** This supplies a sharper radius-dependent
length, with its actual equality, for the already accepted connected
inner-arc theorem. It does not assert a completion or original graph
closure by itself.

Put

    sqrt(17)/2<=R<=sqrt(1105)/16,       rho=9/8,
    z=(R/sqrt(2)-1)/rho,
    delta(R)=pi/2-2arcsin(z).

Let E be an actual contained unit square. Either of the following
physical hypotheses suffices:

1. dist(O,E)>1/8; or
2. after signs and order of its actual own axes are chosen so that
   E=[a-1,a] times[b-1,b], a>=b>=1/2, one has a>rho.

Then the open interior of E meets the radius-rho circle in exactly
one connected open arc, containing its actual radial-center point,
and that arc has length **at least delta(R)**. This is a weak bound:
the diagonal far-corner square in Section5 attains equality.

All orientations, physical circle masks and side endpoints are
included. No force, graph degree, or selected normal is needed.

## 1. Exact scalar bounds

Throughout,

    2/5<z<94/225<1/2,
    pi/6<delta(R)<pi/4.

Indeed R/sqrt(2)>=sqrt(17/8)>29/20, with squared reserve9/400,
so z>2/5. The upper radius gives R/sqrt(2)<147/100, hence
z<94/225. Finally sin(pi/8)<2/5, by
2-sqrt(2)<16/25. The asserted angle interval follows by the
strict monotonicity of arcsine.

Write s=sin(delta), c=cos(delta). Then

    s=1-2z^2,       c=2z sqrt(1-z^2),
    13/20<s<17/25,
    rho^2 c^2>1701/2500.                              (1)

For the lower bound on s,

    1-2(94/225)^2-13/20=187/202500>0.

For the last inequality, the function u(1-u) increases on
0<u<1/2, so z^2>4/25 gives c^2>336/625.

Choose only signs and order of the actual orthonormal own axes,
retaining the original disk origin, and write

    E=[A,a] times[B,b], A=a-1, B=b-1,
    a>=b>=1/2,       q=a^2+b^2<=R^2.

Thus A<61/60 and B<1/2. This follows from
sqrt(R^2-1/4)<121/60 and R/sqrt(2)<147/100.

## 2. The complete domain a>rho

Here A>1/8, B>=-1/2, and q>97/64. We prove the exact inequality

    A^2+B^2+2sAB<=rho^2 c^2.                          (2)

For fixed q set w=a+b. Its left side expands as

    (1-s)q+s w^2-2(1+s)w+2(1+s).

This is convex in w. Enlarge to the complete fixed-q interval
a>=b>=1/2. Its endpoint frames are b=1/2 and a=b.

At b=1/2 put A0=sqrt(q-1/4)-1. Then
1/8<A0<61/60. By (1), the endpoint expression is less than

    A0^2+1/4-(13/20)A0
      <=max(59/320,1121/1800)=1121/1800
       <1701/2500<rho^2 c^2.

The exact comparison reserve is2593/45000.

At a=b=v, one has 3/4<v<=R/sqrt(2). Since
R/sqrt(2)-1>9/20>1/4,

    |v-1|<=R/sqrt(2)-1=rho*z.

Consequently this endpoint satisfies

    2(1+s)(v-1)^2
       <=2(1+s)rho^2 z^2
        =4rho^2 z^2(1-z^2)=rho^2 c^2.

Convexity proves (2) throughout the actual domain. No endpoint
frame is asserted to be an actual second square or a replacement
pose; these are scalar comparisons at the unchanged q.

Define

    alpha=arccos(A/rho), beta=arcsin(B/rho),
    eta=arcsin(min(b/rho,1)).

The complete closed-circle intersection is exactly

    [max(-alpha,beta), min(alpha,eta)].                 (3)

The actual first coordinate is positive; the possible positive and
negative transverse sides are both included in (3). The formal
eta=pi/2 endpoint when b>=rho cannot add an isolated point, since
alpha<pi/2 already excludes that direction.

Inequality (2) is equivalent to

    (A+sB)^2<=c^2(rho^2-B^2).

It implies A<=c sqrt(rho^2-B^2)-sB=rho cos(beta+delta),
regardless of the sign of A+sB. Since |beta|<=arcsin(4/9)<pi/6
and pi/6<delta<pi/4, beta+delta lies in(0,pi/2). Thus

    alpha-beta>=delta.                                (4)

The other three upper-minus-lower differences in (3) are strictly
larger than delta. In fact

    A/rho<122/135<23/25<cos(pi/8)<cos(delta/2),
    eta>=arcsin(4/9)>pi/8>delta/2.

Here cos(pi/8)>23/25 follows by squaring and using sqrt(2)>7/5.
Therefore 2alpha>delta and alpha+eta>delta.

The remaining unit-strip difference satisfies

    eta-beta>=2arcsin(4/9)>pi/4>delta       if b<=rho;
    eta-beta>pi/3>delta                    if b>rho.

The first minimum occurs at the centered strip b=1/2: the
derivative of arcsin(b/rho)-arcsin((b-1)/rho) is nonnegative
for b>=1/2, and continuity includes b=rho. All strip endpoints
are retained.

Thus (3) is one nonempty closed interval of length at least delta.
Its open-interior intersection is exactly the corresponding open
interval, with that same angular length. This proves the statement
on a>rho without needing any central-clearance premise.

## 3. The entire remaining domain a<=rho

Only hypothesis1 remains relevant here. Its strict distance gives

    0<B<=A<=1/8,       A^2+B^2>1/64,
    a>13/12,       b>1.

Indeed if B<=0 the nearest-point norm is at most A<=1/8;
otherwise A>=B and A>1/(8sqrt(2))>1/12.

The complete first-quadrant circle interval is

    [max(beta,theta), min(alpha,eta)],
    alpha=arccos(A/rho), beta=arcsin(B/rho),
    theta=arccos(a/rho), eta=arcsin(b/rho).             (5)

The original outer-face proof in
NINE_EIGHTHS_INNER_ARC_OUTSIDE_ONE_EIGHTH.md supplies all four
endpoint differences. For clarity their full estimates are:

* alpha-beta>=pi/2-2arcsin(1/9)>delta, since z>2/5>1/9;
* alpha-theta and eta-beta are at least arcsin(8/9)>delta,
  since sin(delta)<17/25<8/9;
* eta-theta belongs to[-pi/2,pi/2], and

      sin(eta-theta)
       =[ab-sqrt((rho^2-a^2)(rho^2-b^2))]/rho^2
       >(13/12-31/192)/(81/64)=59/81>17/25>sin(delta).

For the last strict radical comparison,

    (rho^2-a^2)(rho^2-b^2)
       <(53/576)(17/64)=901/36864<(31/192)^2.

The sine comparison is legitimate on the entire displayed difference
interval. It gives eta-theta>delta. This covers a=rho and b=rho
as well: the corresponding formal axis endpoint is superseded by
the other strict inner-face inequality in (5).

Every interval difference is strict in this whole outer-face domain.
The actual open arc is therefore connected and longer than delta.

## 4. The radial center point and exact counting export

Under hypothesis1 the unit incircle gives |c_E|>5/8. Under
hypothesis2 its first own center coordinate is a-1/2>5/8,
so the same strict bound holds without a distance assumption.
Actual farthest-corner containment gives

    |c_E|^2+|c_E|+1/2<=1105/256,
    |c_E|<91/60<rho+1/2.

The strict upper bound has the exact reserve31/57600 at91/60.
Thus |rho-|c_E||<1/2 and the radial point rho*c_E/|c_E|
is in the actual open incircle, hence in the complete arc just proved.

Distinct actual squares have disjoint open arcs. If a caller proves
that k such complete arcs must lie in one actual free interval of
length strictly less than k*delta(R), that interval cannot hold
all k squares. The gap inequality must be strict because the
single-square length bound is weak. Actual occupied endpoints and
the complete free-gap routing remain the caller's obligation.

## 5. Sharp single-square equality and retained limits

The actual square

    E_*=[R/sqrt(2)-1,R/sqrt(2)]^2

is contained in the original radius-R disk and has a unique far
diagonal circle corner. Its distance from O is R-sqrt(2)>1/8.
Its complete radius-rho arc has exactly the two inner-side endpoints,
and length

    pi/2-2arcsin((R/sqrt(2)-1)/rho)=delta(R).

Thus replacing "at least" by "strictly greater" in the full
statement would be false. This equality frame is retained.

The theorem does not cover an arbitrary near-origin unit with
dist(O,E)<=1/8 and a<=rho. It does not prove such an additional
unit absent from a proposed core or route any extra across a physical
cycle. These remain explicit physical obligations in any completion
application.

No sampled orientation, numerical pose, force or mean change,
compilation, CI, remote mutation or shared metadata edit is used.
