# The exact minimum quarter-clear square arc on the radius-five-quarters circle

Date: October 28, 2026 UTC. Author: mixed_capacity_review continuation.

**Status: complete proposed force-free hand theorem, submitted for full
root and separate independent review.** Root proposed the diagonal
extremizer and asked for the complete quantitative bound, including every
strip, outer-face and tangent endpoint. The author derived the sharp
angle-dependent quadratic, the complete other-case comparisons and the
adjacent-equality obstruction below. A root adoption is therefore an
integration/author check; an independent reviewer is still required.

The entire argument concerns actual contained units and their actual
circle intersections. It changes no normal, force, degree, application,
mean, mask, pose, graph, completion allocation, or original gate.

## 1. Exact sharp statement

Set

    Q=1105/256, rho=5/4, v=sqrt(Q/2), D=v-1,
    alpha_*=asin(D/rho),
    Lambda=pi/2-2*alpha_*.

Every inverse sine and cosine below uses its usual principal branch.
The exact constants satisfy

    15/32<D<47/100,
    pi/4<Lambda<2*asin(2/5)<pi/2.                    (1)

Let E be any actual closed unit square, of arbitrary frame, contained in
the closed disk D_sqrt(Q).

**Theorem A, sharp angular measure.** If dist(O,E)>=1/4, the angular
measure of

    int(E) intersect {|z|=rho}

is at least Lambda. Equality holds if and only if E is a rigid rotation
about the original origin of

    [D,v] times[D,v].                                (2)

Every equality square has clearance strictly greater than 1/4 and a
single open circle arc of length Lambda. Reflections produce the same
rotated family.

**Theorem B, connected arc under strict clearance.** If
dist(O,E)>1/4, the actual intersection is one connected open arc of
length at least Lambda. It contains the actual radial center point
rho*c/|c| in its open interior.

**Theorem C, a uniform interval capacity consequence.** Suppose N>=2
actual interior-disjoint units all have distance strictly greater than
1/4 and their entire actual radius-rho arcs are routed into one lifted
angular interval of length L<=2*pi. Then

    L>N*Lambda.                                     (3)

In particular a correctly routed free interval of length at most
2*Lambda has capacity at most one such whole unit. The exact two-unit
threshold is

    2*Lambda=pi-4*asin((sqrt(1105/512)-1)/(5/4)),
                                                             (4)

which is strictly greater than pi/2. The whole-unit clearance and
complete occupied-crosscut routing remain caller hypotheses; this
force-free theorem does not supply them from a graph or a center gap.

## 2. Exact constants and a strict gap above the strip minimum

The bounds D>15/32 and D<47/100 follow from

    Q/2-(47/32)^2=1/1024>0,
    (147/100)^2-Q/2>0.

Also 7/5<sqrt(2)<99/70 and sqrt(21)<23/5, by positive squared
comparisons.

Since D/rho<47/125, whereas

    sin(pi/8)^2=(2-sqrt(2))/4>41/280,
    41/280-(47/125)^2=4421/875000>0,

we have alpha_*<pi/8 and Lambda>pi/4.

For the opposite strict comparison in (1), note that

    sin(pi/4-asin(2/5))
      =(sqrt(21)-2)/(5*sqrt(2))
      <13/35<3/8<D/rho.

Here pi/4-asin(2/5) lies strictly between zero and pi/2, and
3/8-13/35=1/280>0. Monotonicity of sine on that interval gives

    alpha_*>pi/4-asin(2/5),
    Lambda<2*asin(2/5).

Finally 2/5<1/sqrt(2), so the latter strip angle is less than pi/2.
All radical comparisons have positive sides before squaring.

## 3. The complete own-frame domain

Choose signs and order of E's own two orthonormal axes so its actual
center coordinates satisfy x>=y>=0. This is a separate rigid coordinate
description for this actual square, with the same origin. Write

    a=x+1/2, b=y+1/2, A=a-1, B=b-1,
    E=[A,a] times[B,b],
    a>=b>=1/2, q=a^2+b^2<=Q.                        (5)

The farthest corner gives the last inequality exactly. The nearest
point to O has coordinates (max(A,0),max(B,0)).

The cases a>rho, a<=rho with B>0, and a<=rho with B<=0
exhaust all of (5). The last case will be possible only at the weak
clearance endpoint. No boundary contact, positive load, selected normal,
or positive degree is used.

## 4. Complete inner-face case: the sharp angle-dependent quadratic

Assume a>rho. Then

    A>1/4, A<41/40, -1/2<=B<=D<1/2,
    A^2+B^2<2081/1600<rho^2.                        (6)

For the upper A bound, a^2<=Q-1/4=1041/256 and
sqrt(1041)/16<81/40. For B use b<=v; equality B=D is retained
at the final diagonal equality square.

Put s=sin(Lambda)>1/sqrt(2)>7/10 and define

    F_s=A^2+B^2+2s*A*B.

At fixed q, write t=a+b. Direct expansion gives

    F_s=(1-s)*q+s*t^2-2(1+s)*t+2(1+s).              (7)

This is strictly convex in t. Over the entire fixed-q interval
a>=b>=1/2, its maximum is attained at either b=1/2 or a=b.
Enlarging to that interval is legitimate even if an endpoint fails the
current a>rho or clearance premise.

At b=1/2 let A_0=sqrt(q-1/4)-1. The original a>rho implies

    1/4<A_0<41/40.

Therefore

    F_s=A_0^2+1/4-s*A_0
       <A_0^2+1/4-(7/10)*A_0
       <=933/1600.                                 (8)

The comparison quadratic is convex. Its endpoint values on
[1/4,41/40] are 11/80 and 933/1600.

At a=b=w=sqrt(q/2), the original q>rho^2+1/4 gives
3/4<w<=v. The larger endpoint value of (w-1)^2 on [3/4,v]
is D^2, since D>15/32>1/4. Hence

    F_s=2(1+s)*(w-1)^2<=2(1+s)*D^2.                 (9)

The other endpoint (8) is strictly smaller than the right side of (9):
indeed

    2(1+s)*D^2 > (17/5)*(15/32)^2
                  =765/1024>933/1600,

with final reserve 4197/25600. Consequently every actual inner-face
square satisfies

    F_s<=2(1+s)*D^2=rho^2*cos(Lambda)^2.             (10)

For the identity, alpha_*=asin(D/rho) and
s=cos(2alpha_*)=1-2D^2/rho^2.

The strict convexity in (7), the strict bound at b=1/2, and the endpoint
comparison in (9) also prove the complete equality statement in (10):

    equality in (10)  iff  a=b=v.                   (11)

For the last step, the equation (w-1)^2=D^2 has solutions w=v or
w=2-v; the second is below 3/4 because v>47/32>5/4. The two
fixed-q endpoints are distinct in the actual q>rho^2+1/4 domain.

### 4.1. The actual complete arc and both candidate lengths

Set

    alpha=acos(A/rho), beta=asin(B/rho),
    gamma=asin(min(b/rho,1)).

Because E lies in the strict positive x half-plane, a>rho, and
A^2+B^2<rho^2, the entire actual closed circle intersection is

    [beta,min(alpha,gamma)],                        (12)

and its open-interior intersection is the corresponding open interval.
Indeed the circle's x coordinate is below a everywhere in this
half-plane, the inner x condition is -alpha<=theta<=alpha,
and A^2+B^2<rho^2 gives beta>-alpha. The y conditions give
beta<=theta<=gamma. The length comparisons below prove nonemptiness.

Equation (10) is equivalent to

    (A+s*B)^2<=cos(Lambda)^2*(rho^2-B^2).

It follows, irrespective of the sign of A+sB, that

    A<=cos(Lambda)*sqrt(rho^2-B^2)-sin(Lambda)*B
      =rho*cos(beta+Lambda).

The angle beta+Lambda is strictly between zero and pi: its lower
bound uses beta>=-asin(2/5)>-pi/4 and Lambda>pi/4, while
B<=D gives beta+Lambda<=alpha_*+Lambda=pi/2-alpha_*.
Thus cosine is decreasing on the relevant range, and

    alpha-beta>=Lambda.                            (13)

Equality in (13) forces equality in (10), so by (11) it forces a=b=v.

If b<=rho, the other possible length is

    gamma-beta=asin(b/rho)-asin((b-1)/rho)
               >=2*asin(1/(2rho))
               =2*asin(2/5)>Lambda.                (14)

For completeness, the difference is nondecreasing for b>=1/2
on [1/2,rho): its derivative has this sign because
b>=|b-1|. Continuity includes b=rho. If b>rho, then
gamma=pi/2 and beta<=alpha_*, so instead

    gamma-beta>=pi/2-alpha_*>Lambda.                (15)

Therefore the actual whole arc in (12) has length at least Lambda,
and equality is possible only at a=b=v. No clearance assumption was
needed inside this a>rho case.

Conversely, for a=b=v, one has v>rho and the exact open interval is
(alpha_*,pi/2-alpha_*), of length Lambda. Its clearance is
sqrt(2)*D>(7/5)*(15/32)=21/32>1/4. This verifies the actual
equality geometry, not just equality in an algebraic bound.

## 5. Complete outer-face case with B>0

Suppose a<=rho and B>0. Put h=rho-1=1/4. The weak clearance
premise is exactly

    0<B<=A<=h,
    k^2=A^2+B^2>=h^2.                               (16)

The full actual closed intersection in the positive quadrant is

    [max(acos(a/rho),asin(B/rho)),
     min(acos(A/rho),asin(b/rho))].                  (17)

There are four candidate upper-minus-lower differences. Both
opposite-face differences are at least the strip angle
2*asin(2/5)>Lambda by the same full monotonicity argument as (14).
The inner-inner difference is at least

    pi/2-2*asin(h/rho)
      =pi/2-2*asin(1/5)>Lambda,                     (18)

because D/rho>3/8>1/5.

The remaining outer-outer difference is

    L(A,B)=asin((1+A)/rho)+asin((1+B)/rho)-pi/2.

Fix k^2 and vary from A=B=k/sqrt(2) to the actual A>=B,
with B=sqrt(k^2-A^2). This entire path stays in 0<A,B<=h:
its largest A is the actual endpoint and its largest B is its starting
value k/sqrt(2)<=A_actual<=h. At every differentiable interior
point, compare the two positive derivative terms and square. The sign
of dL/dA is the sign of

    (A-B)*[(A+B-h)^2+(k^2-h^2)*(A+B+1)],             (19)

which is nonnegative by (16). The factorization follows directly
from rho^2=1+2h+h^2. Equivalently the second factor expands to

    (A+B)^2+(k^2-2h-h^2)*(A+B)+k^2.

Continuity includes A=h or B=h, where an individual derivative may be
infinite. Thus

    L(A,B)>=2*asin((1+k/sqrt(2))/rho)-pi/2
          >=2*asin((4+1/sqrt(2))/5)-pi/2.            (20)

This lower bound is strictly larger than the strip angle. Both arguments
belong to [0,1], and

    (4+1/sqrt(2))/5
      >sin(pi/4+asin(2/5))
      =(sqrt(21)+2)/(5*sqrt(2)).

After multiplying by positive 5sqrt(2), the inequality is
4sqrt(2)-1>sqrt(21). Both sides are positive, and the squared
comparison reduces to 12>8sqrt(2), which follows from
sqrt(2)<3/2. Consequently

    L(A,B)>2*asin(2/5)>Lambda.                       (21)

All four candidate differences in (17) are strictly greater than
Lambda. They also prove that (17) is a nonempty single interval and
the entire intersection. The open-interior version is a single open
arc, including the weak clearance endpoint k=h. No equality square
occurs in this outer-face case.

## 6. The entire weak tangent residue

Suppose a<=rho and B<=0. The clearance premise and nearest-point
formula give

    1/4<=dist(O,E)=max(A,0)<=1/4.

Therefore this entire remaining case is exactly

    a=rho, A=1/4,
    -1/2<=B<=0, b=B+1 in[1/2,1].                    (22)

It is absent under strict clearance. Write beta=asin(B/rho) and
gamma=asin(b/rho). The inner x face does not cut the interval between
these angles, because

    A^2+b^2<=1/16+1<rho^2,

and b>=|B|. The outer x face x=rho is tangent at angle zero.
The actual open-interior circle intersection is therefore

    (beta,gamma), with the point 0 removed if present. (23)

For B<0 the removed point splits the intersection into two arcs.
For B=0 it is already an endpoint. No connectedness is claimed at
this weak-clearance residue. Removing one point changes no angular
measure; by (14) its total measure is at least

    2*asin(2/5)>Lambda.                             (24)

This retains every tangent endpoint and treats actual open interiors
rather than incorrectly including a tangent boundary point.

Sections 4--6 exhaust the whole square domain and prove Theorem A,
including its unique equality family. Under strict clearance the only
disconnected case (22) is absent, proving the connectedness assertion
of Theorem B.

## 7. The actual radial center point

For strict clearance, the nearest-point support has distance
dist(O,E)>1/4. A unit square's projection halfwidth in any direction
is at least 1/2, so its actual center satisfies

    |c|>3/4.

The farthest actual corner also gives

    |c|^2+|c|+1/2<=Q.

Indeed the two own-center projections have absolute-value sum at least
|c|. At 91/60 the excess over Q is 31/57600>0, hence

    |c|<91/60<7/4.

Thus ||c|-rho|<1/2. The actual radial point rho*c/|c| lies in
the open incircle of E, and consequently in the connected open arc
already proved. This makes no claim that the entire arc is centered at c.

## 8. Adjacent equality squares overlap, giving the strict interval consequence

First consider two equality squares whose actual open arcs are adjacent,
with no angular gap. Every equality square is determined by the midpoint
of its radial arc: (2) has arc midpoint pi/4, and reflection produces
the same rotated family. After one common rotation, the first square is

    S=[D,v] times[D,v],

and its clockwise neighbor is exactly Rot(-Lambda)S.

Put T=sqrt(rho^2-D^2) and P=(T,D). Its angle is alpha_*,
which is the lower endpoint of the first actual arc. Since

    D<T<rho<v,

P is in the relative interior of S's bottom side. Rotating P back
by Lambda gives angle alpha_*+Lambda=pi/2-alpha_* and hence
coordinates (D,T), in the relative interior of the other square's left
side. The first inequality D<T follows from alpha_*<pi/4; the
others follow from D>0 and v>47/32>rho.

The two actual sides are not parallel because 0<Lambda<pi/2.
For an explicit common inward direction choose

    w=(1+sin(Lambda),cos(Lambda)).

Its second coordinate is positive, so it enters the first unit above
its bottom side. After rotation by Lambda, its first coordinate is
cos(Lambda)>0, so it enters the second unit across its left side.
All other side margins at P are strict. Therefore P+epsilon*w
belongs to both actual open interiors for all sufficiently small
positive epsilon. Adjacent equality arcs are incompatible with
interior nonoverlap.

Now retain N>=2 actual interior-disjoint units with strict quarter
clearance and their complete routing into one interval of length L.
Their connected open arcs are disjoint and each has length at least
Lambda. Thus L>=N*Lambda. If equality held, every one of these
units would be an equality square and every successive gap in their
ordered lifted arcs would be zero. An adjacent pair would then be
the impossible pair just proved. Hence L>N*Lambda, proving (3).

This equality argument is geometric and uniform for every N>=2. It
does not presume that the radius-rho arcs fill a larger pocket or that
a body center determines its whole allocation.

## 9. Relation to existing whole-domain kernels and exact review boundary

The previous continuous arc family proves length greater than pi/4
at rho=5/4 and strict quarter clearance. The present result determines
the exact larger minimum Lambda and its full equality family. It also
includes the weak-clearance measure statement and its possible tangent
point removal. Existing source bytes and historical review pins remain
unchanged.

The two relevant complete predecessor sources are:

| Complete source | SHA256 | Exact relation |
| --- | --- | --- |
| UNIFORM_INNER_CIRCLE_ARC_FAMILY_AND_SMALL_CENTRAL_DISK_EXCLUSION.md | c8c9dc223e11dbcd7be9063818d546a3d3c0bc77b66cdac181b9ea97d51bae69 | Complete original own-frame cover, endpoint distinction and exact-critical equality method; the changed sharp bound and all its case comparisons are proved here |
| GENERAL_SIDE_CHANNEL_CAP_INNER_ARC.md | f76d76ef2feccc80098fb6d10d6316af4e393d3ae34d4953846dd27b80c137cb | Its radius-5/4 quarter-clear kernel is strengthened quantitatively; each original channel caller still must establish its actual whole-extra allocation |

The mathematical proof here is complete in its stated unit-square
domain. No continuous orientation, own-frame sign, strip endpoint,
outer-face endpoint, tangent side, or equality shape has been omitted.
Physical masks, degrees and stress choices are irrelevant to this
force-free theorem and are not restricted when a literal caller uses it.

The theorem alone closes no original fine or coarse row. A capacity
caller must prove that every whole relevant extra has strict quarter
clearance and that its entire actual inner-circle arc lies in the one
bounded free interval being compared. The exact original nine-unit
allocation remains separate.

No angle mesh, numerical optimization, sampled pose, finite exclusion
certificate, coefficient packet, changed original normal or application,
deleted body or force, Lean/Lake build, CI/workflow, remote write, commit,
or original-ledger mutation is part of this proof.

