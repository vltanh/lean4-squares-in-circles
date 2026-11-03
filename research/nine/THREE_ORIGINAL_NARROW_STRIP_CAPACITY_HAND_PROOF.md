# A shared three-original capacity theorem in a narrow center strip

November 3, 2026. Hand proof with seven printed positive rational
coefficients. The three physical unit squares may have independent frames.
No disk-containment assumption, marked comparison, Lean, Lake, or CI is
needed for this local theorem. Applying it to a fixed original cell still
requires a proved height order and a proved width bound on that entire cell.

## 1. The original-coordinate theorem

Let L, M, U be three distinct physical unit squares with pairwise disjoint
open interiors. Suppose their unchanged centers satisfy

    y_L <= y_M <= y_U,
    max(x_L,x_M,x_U)-min(x_L,x_M,x_U) <= W,
    0 <= W <= 7/10.

Write

    V = y_U-y_L,       Delta = x_U-x_L,
    f(W) = min(2, 208/75-(29/15)W).

Then

    V + (5/14) Delta^2 >= f(W).                       (1)

The same result holds after interchanging the coordinate axes or reflecting
an axis. Original orientations remain independent. The theorem concerns
center width, not the width of a union of squares.

In particular, if a complete original parent proves Delta in [l,u], its
necessary linear consequence is

    V + (5/14)((l+u)Delta-lu) >= f(W).                (2)

Indeed (Delta-l)(Delta-u)<=0 gives
Delta^2<=(l+u)Delta-lu; its coefficient is positive. Both signs of Delta,
all contact boundaries and equality in the ordered-center guards are
retained. A conservative alternative is V>=f(W)-(5/14)max(l^2,u^2).

For W<=2/5 the right side in (1) is 2. For 2/5<=W<=7/10 it is
208/75-(29/15)W. W is a certified upper bound, so no additional split at
an unknown actual width is required.

## 2. One physical square and two endpoint disks

Every physical unit square contains the open disk of radius 1/2 about
its own center. If an endpoint square is disjoint in its interior from
M, that endpoint disk is also disjoint from the interior of M. Its center
therefore lies outside the interior of

    K = M + B_(1/2),

where + denotes Minkowski addition and B_(1/2) is the closed radius-1/2
disk. This is an implication from the unchanged physical squares; the
endpoint squares are not replaced in the original caller.

First consider a coordinate frame in which the endpoint centers have
the same x-coordinate, their distance is D, the middle center projects
between them, and its distance from their line is d<=7/10. Translate M's
center to the origin and, if needed, reflect x so the endpoint line is
x=d. Since K contains the unit disk, its slice at x=d contains the
origin of that vertical line between its two boundary heights. The lower
endpoint center must be below the lower slice boundary and the upper
endpoint center above the upper slice boundary. Thus D is at least the
vertical length of that slice of K.

We will prove the following universal lower bound on that slice length:

    length(K intersect {x=d}) >= f(d),  0<=d<=7/10.    (3)

No orientation has been assigned to M.

## 3. Vertical symmetrization and the rotated-square slice

For a convex set A, let S(A) replace every nonempty vertical slice by the
centered vertical interval of the same length. We need only the elementary
inclusion

    S(M+B_(1/2)) contains S(M)+B_(1/2).              (4)

For any split x=x_1+x_2, the sum of M's interval slice at x_1 and the
disk's centered interval slice at x_2 is an interval in the Minkowski
sum slice at x. Its length is the sum of the two slice lengths. Centering
these intervals therefore preserves that lower bound. Taking their union
over x_1,x_2 proves (4), because the centered intervals are nested. This
argument does not assume that the original M slices have the same center.

A quarter-turn-equivalent representation and reflection allow the middle
frame to have side components alpha>=beta>=0 with alpha^2+beta^2=1. Put

    t=beta/alpha in [0,1],   r=sqrt(1+t^2),
    alpha=1/r,              beta=t/r,
    k=(alpha-beta)/2,       h=(alpha+beta)/2,
    A=1/(2alpha)=r/2.

The upper half-length of the vertical slice of P=S(M) is

    A                                      for |x|<=k,
    (h-|x|)/(2alpha beta)                   for k<=|x|<=h,

with the second expression omitted when beta=0. This follows by writing
the equations of the two original side lines on each interval. In
particular P is symmetric in both axes and contains the points (k,A)
and (-k,A). It also contains the radius-1/2 disk, since M does and
centering its slices preserves that inclusion.

We claim

    (2/5,1) belongs to P+B_(1/2)                    (5)

for every middle frame. Sections 4-5 give an exact proof.

## 4. The critical point for small slopes and the endpoint values

For 0<=t<=1/6, k is decreasing and

    k >= k(1/6)=5/(2sqrt(37)) > 2/5.

The last positive comparison follows from 625>592. Since A>=1/2,
the point (2/5,A) belongs to P and its vertical distance from (2/5,1)
is at most 1/2. This proves (5) on that entire interval, including t=0.

For t in [1/6,1], use the original slice endpoint (k,A). Its squared
distance from the proposed point is

    F(t) = (2/5-(1-t)/(2r))^2 + (1-r/2)^2.           (6)

We prove F is convex on [1/6,1], so its maximum is at an endpoint.
At t=1/6,

    2/5 <= k < 21/50,      A > 101/200,

whence

    F(1/6) < (1/50)^2+(99/200)^2
            =9817/40000 < 1/4.                     (7)

The exact comparisons follow by squaring positive quantities:
625>592, 62500<65268, and 37-(303/50)^2=691/2500>0.
At t=1,

    F(1)=83/50-sqrt(2)<1/4,                          (8)

because sqrt(2)>141/100, verified by 20000>19881. Convexity and (7)-(8)
then put the full [1/6,1] slope interval strictly inside the required
distance bound, proving (5).

## 5. Seven positive rational coefficients prove convexity

Differentiating (6) directly, with r=sqrt(1+t^2), gives

    F''(t) = (2/5)(1-3t-2t^2)/r^5
              +t(3-t^2)/r^6 +1/2-1/r^3.

Equivalently,

    10r^6 F''(t)
      =5(1+t^2)^3+30t-10t^3
         -r(6+12t+18t^2).

Since r<=1+t^2/2 and the last polynomial coefficient is positive,

    10r^6 F''(t) >= p(t),
    p(t)=-1+18t-6t^2-16t^3+6t^4+5t^6.              (9)

The square-root upper bound follows by squaring; its reserve is t^4/4.
Write t=(1+5s)/6, so 0<=s<=1. The exact Bernstein representation is

    p((1+5s)/6)=sum_(i=0)^6 b_i binom(6,i)s^i(1-s)^(6-i),

with the following printed coefficients:

| i | b_i |
|---:|---:|
| 0 | 82301/46656 |
| 1 | 29681/7776 |
| 2 | 253/48 |
| 3 | 139/24 |
| 4 | 191/36 |
| 5 | 13/3 |
| 6 | 6 |

Every b_i is positive. The seven basis weights are nonnegative and sum
to one, so p(t)>0 on [1/6,1]. Equation (9) proves F''>0 there. The
coefficient identity can be checked by multiplying denominators and
expanding; no sampled angular values are used.

## 6. From the critical point to the complete slice bound

The set P+B_(1/2) is convex and symmetric in both axes. Equation (5)
and its x-reflection give (d,1) in this set for 0<=d<=2/5. It also
contains the unit disk, because P contains B_(1/2). In particular it
contains

    (7/10,71/100),

whose squared norm is 9941/10000<1. The line segment joining this point
to (2/5,1) gives, for 2/5<=d<=7/10, the point

    (d, 104/75-(29/30)d).

Reflecting in y shows that the corresponding vertical slice has length
at least twice the displayed height. Applying (4) proves (3), hence the
equal-endpoint result

    D >= f(d).                                      (10)

It includes the full interval, both joins, physical contact and aligned
middle frames.

## 7. Return to the original coordinates and prove every rotation guard

Return to the three original centers of Section 1. Let

    v_1=y_M-y_L,  v_2=y_U-y_M,  V=v_1+v_2,
    D=|c_U-c_L|=sqrt(V^2+Delta^2).

The three original incircles of radius 1/2 give original center
distances at least one. Since each horizontal gap is at most W<=7/10,

    v_1,v_2 >= sqrt(1-W^2) > 7/10,
    V>7/5.                                         (11)

Thus all ordered heights are actually strict. The projection of M onto
the endpoint line lies strictly between the endpoints: indeed

    (c_M-c_L) dot (c_U-c_L)
      >= -W^2+v_1(v_1+v_2)
      >= 2-3W^2 >= 53/100 >0,

and the analogous expression measured from U has the same lower bound.
These are exactly the two projection guards needed in Section 2.

Let d be M's perpendicular distance from that line. At the original
height y_M, the endpoint segment has a point whose x-coordinate lies
between x_L and x_U. All three x-coordinates lie in a strip of width W,
so M is at horizontal distance at most W from that point of the line.
Consequently

    d<=W<=7/10.                                    (12)

Rotate the entire three-original configuration so the endpoint line is
vertical. This common rotation preserves all physical squares and
nonoverlap. The proved projection order and (12) allow (10). Since f is
nonincreasing,

    D >= f(d) >= f(W).                              (13)

Finally

    D-V = Delta^2/(D+V)
        <= Delta^2/(2V)
        <= (5/14)Delta^2,

by (11). Combining this with (13) proves (1), and Section 1 already
derived its exact linear consequence (2). No new cone comparison,
separator owner, common square orientation, or omitted original is
introduced in this argument.

## 8. Use in the fixed original frontier

For an application, retain the original three square labels and prove
their transverse spread bound W, longitudinal order and endpoint
difference interval [l,u] on the entire unchanged original parent. Then
(2) is a valid rational linear necessary row. Its use can be repeated
for different triples or with the axes interchanged.

A numerical pose that violates (1) is only a diagnostic; it does not
prove those guards on an entire cell. The theorem closes no fixed mask
or original cell by itself. A parent receives credit only after all
required guards and a complete exact contradiction for that parent
have been supplied.
