# Four units within 1/60 of the origin leave total capacity at most eight

Date: October 27, 2026.

**Status: accepted complete uniform hand physical capacity theorem
after full-source root and separate independent reviews in
REVIEW_FOUR_NEAR_ORIGIN_UNITS_CAPACITY_ROOT_2026_10_27.md and
REVIEW_FOUR_NEAR_ORIGIN_UNITS_CAPACITY_ROOTED_BLOCKS_2026_10_27.md.** No contact
graph, stress, load, normal selection or common square orientation
is assumed. No shared ledger or original fine count is changed.

**Theorem.** Let pairwise interior-disjoint unit squares lie in a
disk centered at O with

    R^2<=1105/256.

If four distinct actual squares meet the closed disk D_(1/60)
about O, there are at most eight squares in total.

In particular the original nine-square radius window cannot have
four such actual units. This includes points on original square
sides or vertices and points on the small disk boundary.

The argument uses centers only. Four near-origin centers must
surround O in almost quarter-turn order. Every other center lies
in one of four remaining narrow angular intervals, and each of
those intervals has physical center capacity one. The rational
constants below give a strict reserve for every radius and angle
endpoint; they do not describe a sampled pose.

## 1. The exact universal center bounds

For a unit square with center z and orthonormal own side axes
u,v, its farthest corner has squared norm

    |z|^2+1/2+|z.u|+|z.v|
      >=|z|^2+|z|+1/2.

Disk containment therefore gives

    |z|<=sqrt(R^2-1/4)-1/2<M:=91/60.                  (1)

The last comparison follows by squaring:

    (121/60)^2-1041/256=31/57600>0.

Any two distinct actual centers have distance at least one,
since their open radius-1/2 inscribed disks are disjoint.

Choose four of the actual squares meeting D_(1/60), and call
their centers z_1,...,z_4. The distance from any square point
to its center is at most 1/sqrt(2). Consequently

    |z_i|<=1/sqrt(2)+1/60<m:=3619/5000<3/4.           (2)

For the strict rational comparison,

    m-1/60=10607/15000,
    (10607/15000)^2-1/2=8449/225000000>0.

None of these four centers is O: it would be at distance less
than m<1 from any of the other three. Their directions are
distinct for the same reason, since two on the same ray would
have distance less than m.

## 2. The four near centers surround O and have a positive inner radius

Set

    c=57/1250,       alpha=arccos(c),
    s=6577/10000,    beta=2pi-3alpha.

For two positive radii a,b and their minor center angle omega,
distance at least one gives

    cos(omega)<=f(a,b):=(a^2+b^2-1)/(2ab).             (3)

On 0<a,b<=m the function f increases strictly in either
variable: its derivative in a has the sign of a^2-b^2+1,
which is positive since b<m<1. Thus (2)--(3) give

    cos(omega)<f(m,m)=597161/13097161<c.              (4)

The last rational comparison has positive cross-product
difference

    57(13097161)-1250(597161)=86927.

Hence every pair of near-center directions has minor angle
strictly greater than alpha. Order the four directions
cyclically and denote their consecutive angular gaps by
g_1,...,g_4. Each gap is greater than alpha: if it is at
most pi this is (4), and a larger gap is greater than
alpha automatically. Since alpha>pi/3, no gap can be at
least pi; the other three would already sum to more than
pi. Therefore each is a minor gap and

    alpha<g_i<2pi-3alpha=beta.                       (5)

In particular the four directions surround O. We also have

    |z_i|>s   for every i.                            (6)

To prove (6), suppose one radius is at most s. Its angle
to either cyclic neighbor has, by monotonicity of f,

    cos(omega)<f(s,m)=-4354427/95208652<-c.

The second comparison is exact because

    1250(4354427)-57(95208652)=16140586>0.

Both adjacent gaps would then exceed arccos(-c)=pi-alpha.
The other two exceed alpha by (5). Their total would be
strictly greater than 2pi, a contradiction. This proves
the inner-radius bound without assuming equal radii or a
common orientation of the four original squares.

We will also use the simple bound

    pi/2<beta<3pi/4.                                 (7)

The lower bound follows from alpha<pi/2. For the upper,
c<1/4<cos(5pi/12), so alpha>5pi/12. The exact latter
comparison is (sqrt(6)-sqrt(2))/4>1/4, equivalently
sqrt(6)>1+sqrt(2), which follows by squaring twice.

## 3. Every other actual center has radius strictly greater than one

Let z be the center of any other original square. If z=O,
its distance to a near center is less than one, impossible.
Otherwise (5)--(7) supply a near-center direction within
angle less than beta/2<3pi/8 of the direction of z. Call
its radius a and this angle omega. Then

    0<a<m<3/4<2cos(3pi/8)<2cos(omega).               (8)

For the middle exact comparison, 2cos(3pi/8)=sqrt(2-sqrt(2))
is greater than 3/4 because sqrt(2)<23/16.

If |z|=t<=1, the squared distance to this near center is

    t^2+a^2-2ta cos(omega).

For fixed a,omega this is a convex quadratic in t. At
t=0 it equals a^2<1; at t=1 it is strictly less than one
by a<2cos(omega). It is consequently less than one for
every 0<=t<=1, contradicting the actual center separation.
Every other center therefore satisfies

    1<|z|<M.                                        (9)

This conclusion concerns every extra original square,
independently of its load, contacts or orientation.

## 4. Four angular intervals contain all other centers

Define

    k=f(M,s)=222794623/256503000,
    gamma=arccos(k),
    theta=beta-2gamma=2pi-3alpha-2gamma.              (10)

For a remaining center of radius t in (1,M) and a near
center of radius a in (s,m), (3) gives

    cos(omega)<=f(t,a)<f(M,a)<f(M,s)=k.              (11)

The first strict comparison uses the positive derivative
in t. For the second, the derivative of f(M,a) in a has
the sign of a^2-M^2+1, which is negative throughout
(s,m), since m<3/4 and M>3/2. Thus every other center
direction is more than gamma from each near-center direction.

In the cyclic gap g_i between successive near-center
directions, (11) removes a gamma interval from each end.
All remaining directions in that gap lie in one open
interval of length

    g_i-2gamma<beta-2gamma=theta.                    (12)

An interval with nonpositive length has no center at all.
There are at most four such intervals, one in each original
gap. Every other center is assigned to its unique gap.

For clarity theta lies strictly between zero and pi. We
have k>1737/2000>sqrt(3)/2, so 0<gamma<pi/6, while
beta>pi/2 by (7). Thus theta>pi/6. Also theta<beta<3pi/4.
These comparisons justify use of the ordinary minor angle
and the decreasing cosine on the entire interval in (12).

## 5. Exact angular reserve

We prove the rational bound

    cos(theta)>b:=1957/2500.                         (13)

All estimates in this section are elementary rational
comparisons or squaring of positive quantities. Since
cos(alpha)=c and cos(gamma)=k, the angle addition formula
gives exactly

    cos(theta)
      =(4c^3-3c)(2k^2-1)
        +(1-4c^2)sqrt(1-c^2) 2k sqrt(1-k^2).          (14)

Here 0<c<1/2 and sqrt(3)/2<k<1. The two factors of the
first product have signs negative and positive. The
following strict rational bounds apply:

    4c^3-3c > -171/1250,
    0<2k^2-1<509/1000,
    1-4c^2>2479/2500,
    sqrt(1-c^2)>9989/10000,
    2k sqrt(1-k^2)>4303/5000.                        (15)

For the only slightly longer final check, the explicit k
in (10) satisfies

    sqrt(3)/2<1737/2000<k<4343/5000=:u.

The function 2x sqrt(1-x^2) is decreasing for
1/sqrt(2)<x<1. The final inequality in (15) follows from
the positive exact square difference

    4u^2(1-u^2)-(4303/5000)^2
      =55615750799/156250000000000>0.

The preceding square-root comparison in (15) has exact
reserve

    1-c^2-(9989/10000)^2=11943/100000000>0.

Also 1-4c^2-2479/2500=129/1562500>0, and
2u^2-1=12723298/25000000<509/1000. Thus every bound
in (15) is strict on the full declared interval.

Substituting them into (14), with the displayed product
signs retained, yields

    cos(theta)
      > -(171/1250)(509/1000)
          +(2479/2500)(9989/10000)(4303/5000)
       =97850131493/125000000000
       >1957/2500.

The last comparison has positive numerator reserve 131493
on denominator 125000000000. This proves (13); no angle
grid, floating-point comparison or approximate trigonometric
value is a premise.

## 6. Each remaining interval has center capacity one

Suppose two remaining actual centers lie in one of the
intervals from (12). Their minor angular difference is
less than theta, so its cosine is greater than b by (13).
Their radii t_1,t_2 lie in (1,M) by (9). Their squared
distance is consequently strictly less than

    F(t_1,t_2)=t_1^2+t_2^2-2b t_1t_2.                (16)

This function is convex separately in t_1 and t_2. Its
maximum on the entire rectangle [1,M]^2 is attained at
one of the four corners. Every corner is strictly less
than one:

    F(1,1)=2(1-b)=543/1250<1;

    F(1,M)=F(M,1)<1,
      because b-M/2=367/15000>0;

    F(M,M)=2M^2(1-b)=4496583/4500000<1.              (17)

Equations (16)--(17) contradict the actual center distance
of at least one. This checks unequal radii as well as equal
radii; the other centers were never placed on a common
circle.

Each of the four available angular intervals therefore
contains at most one other center. There are at most four
other original squares. Together with the four chosen
near-origin units, the total is at most eight, as claimed.

## 7. Exact physical scope

The theorem uses only unit side length, disjoint open
interiors, the common enclosing disk and four actual points
of norm at most 1/60. All other squares may have unrelated
orientations and arbitrary circle contacts. The strict
reserves retain the closed small-disk boundary, original
side and vertex points, and every possible circle boundary
case. It applies in particular whenever four original
units meet D_epsilon with 0<=epsilon<1/60.

No force, positive degree, physical circle mask, individual
zero multiplier, original contact normal or mean is changed
or needed. No numerical pose, new scalar certificate, Lean
compilation, CI, remote action or shared-ledger mutation is
used. Any coarse-cell caller must still supply four distinct
original units satisfying the stated physical hypothesis.
