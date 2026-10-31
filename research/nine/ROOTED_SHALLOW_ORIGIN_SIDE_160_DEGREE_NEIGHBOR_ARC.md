# A shallow origin side puts every boundary neighbor in an arc shorter than 160 degrees

Date: October 27, 2026.

**Status: complete fresh geometric proof, pending full root and separate
independent review.** This is an honestly new reconstruction of the
previously accepted shallow-side arc statement after the executor rollback.
It does not claim to restore the bytes or historical pin of
ROOTED_SHALLOW_ORIGIN_SIDE_FOUR_BOUNDARY_NEIGHBORS.md. No original
graph/load gate, coarse cell, shared ledger or remote is changed.

Keep all nine actual interior-disjoint unit squares in the disk centered
at O with

    sqrt(17)/2 <= R <= sqrt(1105)/16.

A physical boundary square means an actual unit touching the containing
circle, irrespective of whether its circle multiplier is positive.

**Theorem.** Suppose an actual unit H contains O closed and has an own
side whose distance from O is at most 1/60. Then the center directions of
all distinct physical boundary squares touching H lie in one ordinary
angular interval of length strictly less than

    8 pi/9 = 160 degrees.

Consequently H has at most four distinct physical boundary neighbors.
No contact normal, force equation, degree, positive edge or circle weight
is needed in this theorem.

The proof below allows the own side and O to coincide, and allows O at
any side or vertex of H. All neighbor orientations and all contact
features remain unrestricted.

## 1. A rational rounded rectangle contains all neighbor directions

Rotate and reflect the whole packing so that

    H=[-a,1-a] times [-b,1-b],
    0<=a<=1/60, 0<=b<=1.

Put

    rho=27/20, r=29/40, K=[0,1] times [-b,1-b].             (1)

If C is the center of a physical boundary neighbor E of H, an actual
contact point p belongs to H and E. Hence

    dist(C,H)<=1/sqrt(2),
    dist(C,K)<=a+1/sqrt(2)<29/40=r.                       (2)

The strict last comparison follows from 1/sqrt(2)<17/24 and
1/60+17/24=29/40.

Every physical boundary center satisfies

    |C|>=R-1/sqrt(2)>=sqrt(17)/2-1/sqrt(2)>27/20=rho.     (3)

For the last strict comparison, both sides in
771/400>27 sqrt(2)/20 are positive and the difference of their
squares is 11241/160000>0. Squaring back proves
sqrt(17)/2>27/20+1/sqrt(2).

The convex set K contains O. Radially contract C to

    C'=rho C/|C|.

Equation (2), convexity, and O in K imply dist(C',K)<r. For example,
write C=k+w with k in K and |w|<r; then
C'=t k+t w with 0<t<1, tk in K and |tw|<r.
Thus every actual neighbor direction occurs on the circle of radius
rho inside the open r-neighborhood of K.

This radial contraction is only a direction estimate. No actual square,
contact, selected normal or force is moved.

## 2. The exact complete angular endpoint bound

For 0<=B<=1 define

    F(B)=asin((B+r)/rho),                       if 0<=B<=5/8,
    F(B)=pi/2+acos((rho^2+B^2-r^2)/(2 rho B)),   if 5/8<=B<=1.   (4)

The two expressions agree at B=5/8 because rho-r=5/8.
Their inverse trigonometric functions take their usual values in
[0,pi/2]. In the second expression the argument belongs to (0,1].

We claim every point of the circle |P|=rho with dist(P,K)<r has an
ordinary argument theta satisfying

    -F(b)<theta<F(1-b).                                  (5)

The negative x-axis itself is impossible because its distance to K is
rho>r, so these ordinary arguments have no wrap ambiguity.

It suffices to prove the upper bound; reflect y for the lower one.
Write B=1-b and restrict to the upper semicircle.

If B<=5/8 and P_x<=0, its nearest point of K is (0,t) for some
0<=t<=B. Therefore its distance to K is at least rho-B>=r, impossible.
If P_x>0, the upper height of the r-neighborhood is B+r, so
rho sin(theta)<B+r. On this right upper quadrant that gives
theta<F(B), including B=5/8.

Now suppose B>=5/8. Points on the right upper quadrant already have
theta<=pi/2<=F(B), with equality impossible when B=5/8.
For P_x<0, if P_y<=B, then

    dist(P,K)^2=P_x^2>=rho^2-B^2
                  >=rho^2-1>r^2,

since rho^2-r^2=83/64>1. Thus P_y>B. Its nearest point is exactly
the upper-left K corner (0,B), and

    rho^2+B^2-2 rho B sin(theta)<r^2.

For pi/2<theta<pi, this is precisely theta<F(B). This proves (5)
for every point and all endpoint cases.

The function F is increasing on [0,1]. This is immediate on its first
branch. On its second branch the arccos argument has derivative

    (B^2-(rho^2-r^2))/(2 rho B^2)<0,

because B^2<=1<83/64. The two branches agree at their common endpoint.

It remains to prove the uniform strict estimate

    F(b)+F(1-b)<8 pi/9.                                  (6)

## 3. The central range of b

Reflect the vertical frame if necessary so that 0<=b<=1/2.
If 3/8<=b<=1/2, both b and 1-b are at most 5/8. Monotonicity gives

    F(b)<=F(1/2)=asin(49/54)<7 pi/18,
    F(1-b)<=pi/2.

The strict comparison uses 49/54<15/16<cos(pi/9)=sin(7 pi/18).
For completeness, 4x^3-3x is increasing for x>1/2; its value at
15/16 is 495/1024<1/2, whereas its value at cos(pi/9) is 1/2.
Therefore (6) holds throughout this closed range.

## 4. The complete remaining interval and one exact quartic

Let 0<=b<=3/8 and put t=1-b, so 5/8<=t<=1. Set

    x=(69-40t)/54,
    y=(t^2+83/64)/((27/10)t).                            (7)

Then x=(b+r)/rho and y is the second-branch arccos argument, so

    F(b)+F(1-b)=asin(x)+pi/2+acos(y).                    (8)

Both x,y are positive and at most one. Also
x<=22/27<15/16<cos(pi/9), so asin(x)<7 pi/18.

We use the exact angle bounds

    sin(pi/9)<11/32,
    cos(pi/9)<47/50.                                    (9)

The first follows because 3z-4z^3 increases on [0,1/2], its value at
11/32 is 7117/8192, and

    7117^2=50651689>50331648=(3/4)8192^2.

The second follows from the increasing 4z^3-3z on z>1/2 and

    [4(47/50)^3-3(47/50)]-1/2=73/31250>0.

We now prove

    y-(47/50)x > (11/32)sqrt(1-x^2).                    (10)

The left side is

    A(t)/(21600t),
    A(t)=23040t^2-25944t+10375.

On [5/8,1], A is increasing because A'(5/8)=2856>0, and
A(5/8)=3160>0. Thus the left side of (10) is strictly positive.

A direct identity gives

    [y-(47/50)x]^2-(121/1024)(1-x^2)
       =P(t)/(1866240000t^2),                            (11)

where the entire numerator is

    P(t)=2244366400t^4-5199448080t^3+4744212669t^2
                         -2153352000t+430562500.

Here is a complete positive certificate on the entire required interval,
with no sampling or root approximation. Write z=t-3/4, so
-1/8<=z<=1/4. Exact expansion gives

    P(t)=12520381/16 -(47466663/2)z
         +620191089z^2+1533651120z^3+2244366400z^4.        (12)

For -1/8<=z<=0, the linear term is nonnegative and

    620191089+1533651120z>=428484699>0.

Consequently every term after the strictly positive constant, grouped
as the quadratic/cubic pair, is nonnegative.

For 0<=z<=1/4, the cubic and quartic terms are nonnegative. The remaining
quadratic has positive leading coefficient and is strictly positive
on the whole real line, since

    4(12520381/16)(620191089)-(47466663/2)^2
        =1377986157682335>0.                            (13)

This proves P(t)>0 everywhere on [5/8,1]. Equation (11), and the
already checked positive left side, prove (10).

Using (9),(10), with alpha=asin(x), gives

    y > cos(pi/9)sin(alpha)+sin(pi/9)cos(alpha)
      = cos(7 pi/18-alpha).

The angle 7 pi/18-alpha lies in (0,pi/2). Monotonicity of arccos gives

    acos(y)<7 pi/18-alpha.

Substituting in (8) proves (6) throughout the remaining closed interval.
Together with Section 3 this covers every b in [0,1].

## 5. All actual neighbors and the exact counting consequence

By (3)--(6), every actual physical boundary neighbor center has direction
in the same ordinary interval

    (-F(b),F(1-b)),

whose length is strictly less than 160 degrees. This is an actual common
interval for all the neighbors at once, not a separate pairwise estimate.

CENTERED_INNER_ARC.md proves that any two physical boundary centers in
the declared radius window have minor angular separation strictly greater
than 2 pi/9=40 degrees. The full lemma is geometric and allows every
one- or two-corner mask and every zero circle multiplier.

If H had at least five physical boundary neighbors, order any five of
their center directions in the interval just obtained. Each of the four
successive gaps is smaller than pi, and is therefore the corresponding
minor angle, strictly greater than 40 degrees. Their total span would
exceed 160 degrees, a contradiction. Hence there are at most four.

## 6. A useful actual-near-unit trigger

Suppose instead that H contains O openly and a distinct actual unit X
meets the closed disk of radius epsilon, where 0<=epsilon<1/60.
Then some actual own side of H has distance at most epsilon from O.

Indeed, if all four side distances exceeded epsilon, that whole closed
disk would lie in int H. A point of X in it would then be interior to H,
and points of int X arbitrarily near that point would overlap int H.
This is impossible for two distinct physical units. This argument retains
tangencies of X with the closed small disk.

Therefore, at high radius, an origin-containing H with a distinct actual
near unit X satisfies the whole common-arc and at-most-four conclusion.
X need not be a leaf root, unloaded body, or positive neighbor. The usual
genuine S-root caller supplies both the near point and d>1, hence the
required high radius, without changing its original equation.

No further graph closure is asserted here. In particular a later caller
using the circular order of several private components must justify that
actual order and every component's boundary status separately.

