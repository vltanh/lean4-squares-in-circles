# The zero-angle owned-return S123 five-cycle has no inner unit

Date: October 27, 2026.

**Status: complete physical area theorem and conditional canonical
slider consequence, submitted for full independent and root review.**
The theorem retains every actual contact mean and the entire unloaded
side-transmitter position. It applies to every frame and physical
circle mask of the actual middle square. It closes the central-hole
obligation in this exact zero-angle chart, not its exterior completion.

## 1. Complete physical hypotheses

Retain the same actual five-cycle A--B--M--C--U--A. Work in actual
orthonormal coordinates and put

    d=1+epsilon,       0<epsilon<1/60,
    R^2=(d+1)^2+1/4,
    0<V<13/50,       F=1-V,
    W=sqrt(R^2-(F+1)^2),       1/2<W<1,
    u=1-W.

Its actual squares and applications have the following complete form:

    A=[epsilon-1,epsilon] times[-V,F],
    B=[-W,u] times[F,F+1],
    C=[d,d+1] times[-1/2,1/2],
    U=[epsilon,d] times[z,z+1],

    E=p_AU=(epsilon,-T),       D=p_UC=(d,-T),
    S=p_AB=(-J,F),             Q=p_BM=(u,Y),
    P=p_CM=(X,1/2),

    0<=T<=V,       J>0,
    F<=Y<F+1,       d<=X<=d+1.

All displayed points belong to both actual endpoint squares.
In particular the true U interval contains -T; it is not centered
or replaced by a segment. M has actual minimum East support u,
containing Q. The actual C-to-M unit normal h satisfies

    h_x<=0,       h_y>0.

No M circle-mask or force-ratio premise is needed for the area
argument. A shared C--M side keeps its actual X, and a shared
B--M side keeps its actual Y.

These are the literal t=0 hypotheses in the surviving tilted-root,
B-owned-incoming, owned-East-return S123 chart. They follow from
S_LEAF_C5_THREE_LOAD_RADIAL_ROOT_HALFPLANES.md and
S_LEAF_C5_THREE_LOAD_OWNED_DIRECT_SIDE_UPPER_RETURN_EXCLUSION.md.
The additional true-root identity V=2sqrt(epsilon) is not needed
here. The genuine leaf and all three original completion squares
remain actual other units.

**Theorem 1.1.** No further whole unit square lies on the bounded
side of this actual five-cycle.

## 2. Winding and the occupied pieces

Use the physical center/contact loop and its actual five applications.
They are distinct: E,D have height -T<=0, S,Q have heights at least
F>1/2, and P has height1/2. The two low points differ by one;
S and Q differ horizontally because -J<0<u. No opposite pair
can coincide either.

The actual center/contact loop is therefore a Jordan curve.
Its open center-to-contact strands lie in the respective disjoint
square interiors. The complete contact-polygon homotopy in
CONTACT_RING_HOLE_AREA.md Section1 applies. The limiting polygon

    E--S--Q--P--D--E

has winding zero or one after positive orientation. We use its
clockwise signed-area magnitude in the displayed coordinate
calculation below. The bottom edge D--E has every other contact
strictly above it, fixing this orientation.

Every extra unit on the bounded side contributes its full open
unit area to the free hole. That free area is at most the contact
polygon area minus any disjoint occupied pieces on its inward side.
This is the literal winding subtraction from the same source,
not an assumption that a straight contact polygon is strictly convex.

Three such pieces are the actual triangles

    E, (epsilon,F), S         inside A,
    S, (u,F), Q               inside B,
    P, (d,1/2), D             inside C.

Degenerate triangles have area zero and are retained. In each
case the displayed auxiliary corner lies to the right of the
clockwise contact chord, hence on its inward side. The whole
triangle is in its actual square. Its open interior meets no
other contact-polygon edge, so its winding is one whenever
its area is positive. The three pieces have disjoint interiors
because their actual squares do.

Subtracting exactly these three pieces inserts those auxiliary
corners into the area formula. A direct determinant expansion gives

    A_after_ABC
      = T+(u-epsilon)F+(d-u)/2
          +(X-u)(Y-1/2)/2.                         (1)

For clarity, the resulting clockwise boundary is

    E, (epsilon,F), (u,F), Q, P, (d,1/2), D, E.

Formula (1) uses only d-epsilon=1 and is valid even if some
inserted segments retrace or u<epsilon. The winding subtraction
is made before any use of that algebraic expression.

## 3. The complete M frame and its actual side means

We bound the final term of (1) after subtracting an actual
occupied piece of M.

### 3.1. M also owns East

Then M is axis aligned with minimum x coordinate u.
Since h_y>0, its minimum-h point P lies on its bottom side
or a bottom corner. Consequently the bottom height is exactly
1/2. Its actual triangle with vertices

    Q, (u,1/2), P

has area (X-u)(Y-1/2)/2 and is on the inward side of Q--P.
It lies in M, with its full genuine bottom-side mean X retained.
Subtracting it cancels the last term of (1).

This includes all cases where Q or P is an endpoint of an
owned-side mean, and every physical M circle mask.

### 3.2. M does not own East

The actual Q is its unique minimum-x vertex. Write its actual
inward unit axes as

    v=(c,s),       w=(s,-c),
    c,s>0,       c^2+s^2=1,
    M=Q+[0,1]v+[0,1]w.

Because h_x<=0<h_y,

    h.w=h_x*s-h_y*c<0.

Therefore the actual minimum-h application has the exact form

    P=Q+w+lambda*v,       0<=lambda<=1.            (2)

When h.v>0 the original lambda is0; when h.v<0 it is1;
when h.v=0 it is its full original shared-side mean.
No endpoint or mean is replaced. Since P_y=1/2, (2) gives

    X-u=s+lambda*c,
    Y-1/2=c-lambda*s.

The actual triangle Q, Q+w, P lies on the inward side of
Q--P and has area lambda/2. It is an occupied piece of M
disjoint from the pieces in Section2. Thus the remaining
last term of (1) is exactly

    [(s+lambda*c)(c-lambda*s)-lambda]/2
      = cs(1-lambda^2)/2-lambda*s^2
      <=cs/2<=1/4.                                (3)

All inequalities include lambda=0 and lambda=1. Nothing about
the location of a proper concurrence, or about the number or
weights of M's physical circle corners, was used.

Together the two complete M frame cases prove the uniform
free-hole bound

    area(hole)
      <=T+(u-epsilon)F+(d-u)/2+1/4
      <=5/4-(F-1/2)(W+epsilon),                    (4)

where the last line uses only T<=V=1-F and u=1-W.

## 4. The exact scalar bound is strictly below one

We prove

    (F-1/2)W>1/4.                                 (5)

Fix the actual R. Since W<1 and F<1, the actual F lies
strictly inside

    [sqrt(R^2-1)-1, 1].

The left endpoint exceeds1/2 because R^2>17/4.
Define on this interval

    f(y)=(y-1/2)sqrt(R^2-(y+1)^2).

All square roots are positive. Direct differentiation gives

    f''(y)
      =-(3y+3/2)/sqrt(R^2-(y+1)^2)
       -(y-1/2)(y+1)^2/[R^2-(y+1)^2]^(3/2)
      <0.

Therefore f is strictly concave and is bounded below by
the smaller of its two endpoint values. At the left endpoint,

    f=sqrt(R^2-1)-3/2
      >sqrt(13)/2-3/2>1/4,

where the last squared comparison is13>49/4.
At the right endpoint,

    f=(1/2)sqrt(R^2-4)>1/4.

Both comparisons use the original strict high radius,
R^2>17/4. This proves (5). Since epsilon>0 and F>1/2,
(4) is strictly less than one.

A hypothetical inner unit would contribute its full area one,
a contradiction. Theorem1.1 is proved for the entire physical
chart and every actual U position.

## 5. Exact canonical upward-slider consequence

This section uses only the already available secondary choice
from FOUR_CYCLE_SECONDARY_CONTACT_REDUCTION.md Section1:
among global radius minimizers choose one minimizing the sum
of squared center norms, before finite normal selection and
stress extraction. No stronger minimization is imposed.

Let b=z+1 be the actual top of U. Its actual side mean implies
b>=-T. At such a canonical packing,

    b>=1/2,       or U has an actual physical contact with M. (6)

Suppose instead b<1/2 and U is closed-disjoint from M.
Translate only U upward by a sufficiently small positive amount,
less than1/2-b and the actual positive distance to M.

A and C remain separated from its open interior by the unchanged
vertical lines x=epsilon and x=d. B is above height F>1/2.
Every newly occupied interior point lies in

    (epsilon,d) times (b,b+small),
    -T<y<1/2.

The contact polygon in Section2 has winding one throughout
the rectangle (epsilon,d) times(-T,1/2): its bottom is D--E,
its left and right closing portions are outside this open
rectangle, and its upper chain has height at least1/2.
A new point outside the five actual core bodies therefore
lies in the actual bounded hole by the contact-polygon
homotopy. Section4 excludes any other whole unit from that
hole. Connected extra-square interiors cannot enter it from
outside the occupied core loop. Thus every original extra
unit and the genuine leaf remain disjoint from the translated U.

The transverse center of U is b-1/2<0. Moving it toward zero
strictly decreases its maximum corner radius and its squared
center norm. Its fixed horizontal interval is unchanged.
This contradicts the canonical secondary minimum, proving (6).

The possible U--M contact is physical only; it is not assigned
a positive multiplier or used to shorten any actual force equation.

If M also owns East, Section3.1 gives M's bottom height1/2.
Its horizontal interval [u,u+1] overlaps the interior of
[epsilon,d], because u<1/2<d and u+1>1>epsilon.
Actual nonoverlap therefore forces b<=1/2. Moreover U cannot
touch M when b<1/2. Combining with (6) gives the exact
canonical conclusion

    U=[epsilon,d] times[-1/2,1/2]                  (7)

for this whole M-owned subcase. Its original channel mean
-T remains on the same two actual sides.

For a strict-M frame, (6) is the only conclusion asserted here.
A physical contact with M or a top greater than1/2 must be
retained unless separately ruled out.

## 6. Scope

The central-hole exclusion is physical and uses no minimizer
premise. The slider consequence is conditional on the existing
canonical radius minimizer and applies to the unchanged original
nine-unit packing, with all side means retained.

No clearance of an exterior extra from D_(1/8) follows solely
from this theorem. In particular, when V<1/8 the lower-left
region below A remains a separate physical completion issue.
The theorem does not center an arbitrary transmitter, delete
a middle load, replace a selected normal, or close the whole
S123 original fine family.

