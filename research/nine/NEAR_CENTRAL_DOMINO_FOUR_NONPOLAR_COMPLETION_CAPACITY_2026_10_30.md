# A near-central two-square rectangle permits at most four nonpolar completing units

Date: October 30, 2026 UTC.

**Status: complete proposed physical hand theorem, awaiting a separate
independent review. No original case or ledger flag is changed.**

This theorem couples the actual two central units to all completing
squares by their real separating axes. It uses neither stress nor a
common frame for the completing units. The numerical labels below are
short exact bounds, not sampled poses.

## 1. Statement, including the exact record central pair

Put Q=1105/256 and r=5/4. Let actual unit squares have pairwise
disjoint open interiors and be contained in the disk centered at O
of squared radius at most Q. Suppose two of the actual units share
a complete side, and in one common orthonormal coordinate system
their physical union is

    C = [s-1,s+1] x [h-1/2,h+1/2],
    |s|<=1/12, |h|<=1/12.                                    (1)

The origin has not been translated. Set

    delta = 1/2-|h|,          5/12<=delta<=1/2.                (2)

For every other actual square E let c_E be its original center and
u_E,v_E its own orthonormal side axes. Call it nonpolar here if

    max(|c_E.u_E|, |c_E.v_E|) <= 1-|h| = 1/2+delta.          (3)

**Theorem.** At most four of the other actual units satisfy (3).
Every such unit is wholly above or wholly below C, and each of those
two half-planes contains at most two such units.

Consequently any nine-unit packing with (1) has at least three of its
other seven units with an own center coordinate strictly larger than
1-|h| in absolute value. No circle-touching premise is used.

The exact record core has central centers (-1/2,1/16),(1/2,1/16),
so s=0,h=1/16 belongs to (1). The theorem does not assert that every
packing has the pair (1), or that the remaining polar units cannot
fit. The latter require additional physical constraints.

## 2. Exact SAT routing, including equality on a central side

E's open interior misses the interior of C. Indeed any open overlap
with C contains points away from the two central units' common side,
and hence intersects one central unit's open interior.

The separating-axis theorem for two rectangles supplies a separating
normal parallel to a side axis of C or of E. Orient it n from C to E.
Write H_C(n) for C's full support value, and H_E(n) for E's support
halfwidth. The unchanged actual separator is

    c_E.n-H_E(n) >= H_C(n).                                (4)

C contains the disk D_delta. More precisely,

    H_C(n)=s*n_x+h*n_y+|n_x|+(1/2)|n_y|
      >=(1-|s|)|n_x|+delta*|n_y| >= delta.                  (5)

Since 1-|s|>=11/12>delta and |n_x|+|n_y|>=1, equality in the
last bound can occur only for n_x=0. Thus if n is an E-owned side
axis, (3) and H_E(n)=1/2 give

    c_E.n-H_E(n) <= delta <= H_C(n).

Equation (4) forces equality and n_x=0. Such a separator is also a
vertical C-axis separator. No weak endpoint has been discarded.

For a horizontal C-axis separator, (4) and H_E(n)>=1/2 give

    |(c_E)_x| >= 3/2-|s| >= 17/12 > sqrt(2).               (6)

But (3) gives |c_E|<=sqrt(2)*(1-|h|)<=sqrt(2), impossible.
The final exact comparison in (6) is (17/12)^2-2=1/144>0.
Every possible actual separating axis therefore puts E wholly in

    y>=h+1/2       or       y<=h-1/2.                     (7)

In particular dist(O,E)>=delta. These closed half-plane statements
include actual side contacts with C. Their open-square parts lie in
the corresponding strict half-planes.

## 3. A full single-square arc bound with the central-pair coordinate cap

Take any E satisfying (3),(7). Change only its own coordinate signs
and order so its center coordinates are x>=y>=0, and write

    a=x+1/2, b=y+1/2, A=a-1, B=b-1,
    E=[A,a] x [B,b],
    a>=b>=1/2, a^2+b^2<=Q, A,B<=delta.                    (8)

These are coordinates relative to the same O. Set

    v=sqrt(Q/2), w=v-1,
    alpha0=pi/2-2*asin(w/r),
    alpha_delta=pi/2-2*asin(delta/r),
    sigma=2*asin(2/5),
    L_delta=min(max(alpha0,alpha_delta),sigma).             (9)

We prove that the entire actual open-interior intersection with the
circle of radius r is one open arc of length at least L_delta.

First a>r. Otherwise A,B<=1/4, so the actual nearest point to O
has norm at most sqrt(2)/4<5/12<=delta, contrary to (7).
Thus A>1/4, while |B|<=1/2 and A<=delta<=1/2 imply
A^2+B^2<=1/2<r^2. Put

    beta=asin(B/r), gamma=asin(min(b/r,1)).

The exact open arc is

    (beta, min(acos(A/r),gamma)).                         (10)

The outer x face lies beyond the circle, the inner x face selects
the right half-plane, and A^2+B^2<r^2 ensures the lower y endpoint
is above the negative inner-x endpoint. This accounts for the entire
intersection. In particular no extra component or tangent point is
silently joined to it.

The bounds A,B<=delta give

    acos(A/r)-beta >= alpha_delta.                        (11)

For the other possible endpoint, the function
asin(b/r)-asin((b-1)/r) is nondecreasing for 1/2<=b<=r:
its derivative comparison uses b>=|b-1| and the increasing derivative
of asin as a function of the absolute argument. Hence

    gamma-beta >= sigma.                                 (12)

When b>r, gamma=pi/2 and beta<pi/6 give an even larger value;
b=r is included by continuity. All bounds use actual coordinates.

It remains to prove the Q-dependent bound

    acos(A/r)-beta >= alpha0.                             (13)

## 4. One fixed-radius convexity argument proves (13)

The useful exact comparisons are

    9/20 < w < 19/40,
    w/r < 19/50 < sin(pi/8),
    pi/4 < alpha0 < pi/3,
    k:=sin(alpha0)=1-2*w^2/r^2 > 7/10.                    (14)

The bounds for w follow by squaring 29/20<v<59/40; the respective
positive squared reserves are 713/12800 and 223/12800.
For 19/50<sin(pi/8), use sqrt(2)<99/70<889/625 in the exact
half-angle formula. For alpha0<pi/3, use w/r>9/25 and
sin(pi/12)<1/3<9/25; the elementary radical half-angle formula
proves sin(pi/12)<1/3. The last inequality follows from
1-2*(19/50)^2=889/1250>7/10.

Define F=A^2+B^2+2*k*A*B. At fixed q=a^2+b^2, t=a+b gives

    F=(1-k)*q+k*t^2-2*(1+k)*t+2*(1+k).                   (15)

It is convex in t. The complete possible t interval with a>=b>=1/2
has endpoints b=1/2 and a=b. Enlarge to this interval, even if an
endpoint fails (3) or (7), to bound the actual F from above.

At b=1/2 put A0=sqrt(q-1/4)-1. The original a>r implies
A0>1/4, and q<=Q gives A0<41/40. Since k>7/10,

    F=A0^2+1/4-k*A0
      <A0^2+1/4-(7/10)*A0 <= 933/1600.                 (16)

The last convex quadratic has endpoint values 11/80 and 933/1600
on [1/4,41/40]. At a=b=z=sqrt(q/2), the original q>r^2+1/4
gives 3/4<z<=v. Since w>9/20>1/4, convexity of (z-1)^2 gives

    F=2*(1+k)*(z-1)^2 <= 2*(1+k)*w^2.                 (17)

The latter upper bound exceeds
`(17/5)*(9/20)^2=1377/2000>933/1600`; the final reserve is
843/8000. Consequently (15)--(17) yield, on the full actual domain,

    F <= 2*(1+k)*w^2 = r^2*cos(alpha0)^2.              (18)

The identity on the right follows from k=1-2*w^2/r^2 and (9).
Equivalently,

    (A+B*sin(alpha0))^2
      <= cos(alpha0)^2*(r^2-B^2).

Taking the nonnegative square root yields

    A <= cos(alpha0)*sqrt(r^2-B^2)-B*sin(alpha0)
      =r*cos(beta+alpha0).

There is no premise on the sign of A+B*sin(alpha0): its absolute
value is bounded, which implies the displayed upper bound regardless.
By |B|<=1/2, beta lies in (-pi/6,pi/6), and (14) gives
0<beta+alpha0<pi/2. The decreasing cosine on this interval proves
(13). Equations (10)--(13) prove the claimed L_delta arc bound.

## 5. Three such arcs exceed either available half-plane cap

On the radius-r circle either half-plane in (7) cuts an open cap of
angular measure at most

    K_delta=pi-2*asin(delta/r).                         (19)

We prove 3*L_delta>K_delta throughout 5/12<=delta<=1/2.
Both entries of the minimum in (9) satisfy this strict inequality.

For M_delta=max(alpha0,alpha_delta), distinguish delta<=w and
delta>=w. In the first case,

    3*M_delta-K_delta
      =pi/2-4*asin(delta/r)
      >=pi/2-4*asin(w/r)>0,                            (20)

by (14). In the second case M_delta=alpha0 and K_delta<=K_w,
so the same strict lower bound in (20) applies.

For sigma put t=asin(2/5), so 0<3*t<pi/2 and

    cos(3*t)=9*sqrt(21)/125 < 1/3 <= delta/r.           (21)

The strict comparison follows by squaring positive quantities:

    1/9-(9*sqrt(21)/125)^2 = 316/140625 > 0.

The increasing sine on (0,pi/2) now gives
asin(delta/r)>pi/2-3*t. Therefore

    3*sigma-K_delta
      =6*t+2*asin(delta/r)-pi>0.                       (22)

Equations (20),(22) imply 3*L_delta>K_delta. Three different actual
units in either half-plane would have disjoint open circle arcs of
total measure at least 3*L_delta, inside a cap of measure at most
K_delta. This is impossible. There are at most two above and two
below, proving the theorem.

## 6. Exact obstruction removed, and remaining scope

In the all-radii relaxation witness of the companion document, two
physical A units would force C=[-1,1] x [-1/2,1/2]. Each B profile has
both own center coordinates sqrt(17/8)-1/2<1. Thus all five B units
would satisfy (3), contradicting this theorem. The S profiles are
not used or deleted; they may remain as arbitrary other actual units.

This is a pair-dependent obstruction that the entire family of
independent radial occupations misses. Its positive theorem applies
to arbitrary orientations, radial positions, contacts and physical
circle masks of the completing units satisfying (3), not only the
three particular radial profiles.

The theorem does not extract (1) from every original large block and
does not bound the number or arrangement of the complementary polar
units. Those are explicit remaining obligations before it can close
an original coarse row. All nine physical units can remain throughout;
no force, torque, mean or normal selection is changed. The proof is
self-contained apart from the elementary rectangle separating-axis
theorem, and uses no numerical pose search, computation certificate,
Lean compilation, CI, original metadata mutation or remote write.
