# A triangle with nonzero cycle moment enters every full external-resultant ray

Date: October 27, 2026.

**Status: accepted complete hand strengthening after full-source root
and separate independent reviews in
REVIEW_NONZERO_TRIANGLE_RAY_AND_S_HUB_INTERIOR_ROOT_2026_10_27.md and
REVIEW_TRIANGLE_NONZERO_MOMENT_EXTERNAL_RAY_HEXAGON_2026_10_27.md.**
The nonzero-moment premise is essential; no stronger
claim is made for a zero-moment triangle. This source supplies a
general local theorem and its two-block origin-interior consequence,
not an original coarse-cell closure.

## 1. The full actual triangle and the additional moment premise

Let K,U,V be three original interior-disjoint unit squares, with
all three positive physical triangle edges, in the original circle
of radius

    79/40<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1<61/60.

Retain each body's complete external force system, all its original
applications and positive magnitudes, every physical circle mask
and zero atom, and every arbitrary completion square. Assume the
complete external system at each body has zero origin moment.
The actual directed cycle moments are therefore equal. Assume their
common value is nonzero.

At K put

    M=mu_1 n_1+mu_2 n_2,       mu_1,mu_2>0,
    F_K=-M,

where n_i are its two original outward triangle normals and F_K
is its full external resultant. The actual triangle theorem makes
M nonzero.

**Theorem.** The closed K contains a point of the strictly positive
full external-resultant ray:

    K intersect {t F_K:t>0} is nonempty.                 (1)

The earlier TRIANGLE_EXTERNAL_RAY_INTERSECTS_BODY.md proves this
with t>=0, without the present nonzero-moment premise. Thus if (1)
fails, that theorem gives O in K. We assume this failure below.

## 2. The nonparallel case reaches the same far-side cap at height one

If K's triangle normals are nonparallel, the actual nonzero-moment
concurrence theorem gives

    q=-tau M,       tau>0,
    P_i=q+a_i n_i,  a_i>=0,                             (2)

for its original applications P_i. Since the positive ray is
assumed disjoint from K, q is outside K and a_i>0.

Write K in its own two orthonormal side axes about the unchanged
circle origin. Because O belongs to K but no positive multiple
of -M does, at least one side interval has zero as an endpoint,
and the corresponding component of -M points strictly outside
that interval. Reflect that axis if necessary. We obtain

    K=[0,1] x [b,b+1],     b<=0<=b+1,
    M_x>0,                q_x<0.                       (3)

This elementary tangent-cone step includes origin vertices: if
every active coordinate pointed inward or tangentially, sufficiently
small positive multiples of -M would belong to the rectangle.

Equations (2)--(3) make every (n_i)_x positive. Each actual P_i
is consequently on the far side x=1. Its vertical coordinate y_i
is the upper endpoint when (n_i)_y>0, the lower endpoint when
(n_i)_y<0, and the actual side-mean height when it is zero.

The full pair origin moment is zero. Therefore

    M_y=sum_i mu_i y_i(n_i)_x,
    k=M_y/M_x

is a positive weighted mean of y_1,y_2. For the actual proper
line (2),

    (n_i)_y/(n_i)_x
      =(y_i+tau M_y)/(1+tau M_x)
      =y_i/(1+tau M_x)+tau M_x k/(1+tau M_x).           (4)

For a positive vertical normal y_i is the largest possible port
height and k<=y_i; for a negative vertical normal k>=y_i.
Multiplying the resulting slope inequality by the correctly signed
vertical normal component gives, also for the zero component,

    y_i(n_i)_y >= (n_i)_y^2/(n_i)_x,
    h_i=P_i.n_i >=1/(n_i)_x.                            (5)

Every actual contained unit neighbor requires h_i<=d, by the
sharp center/halfwidth bound. Thus

    (n_i)_x>=1/d>60/61,
    |(n_i)_y|<11/61,
    h_i>=1.                                             (6)

These are exactly the estimates of
ROOTED_NONPOSITIVE_RAY_PROPER_PORT_CAP_EXCLUSION.md with its far
side height A allowed to equal one. The next strict center estimate
does not require h_i>1.

Let c_i be the original neighbor center and M_*=91/60. Its actual
support gives c_i.n_i>=h_i+1/2>=3/2, while the sharp contained-unit
bound gives |c_i|<M_*. Consequently its transverse component has
magnitude less than sqrt(181)/60<27/120. By (6),

    (c_i)_x>(3/2)(60/61)-(11/61)(27/120)
            =3501/2440=:L.                              (7)

Both original centers lie in the same open rectangle

    L<x<M_*,       |y|<sqrt(M_*^2-L^2).

Its squared diameter is

    (M_*-L)^2+4(M_*^2-L^2)
      =52124381/53582400<1.                             (8)

The two radius-1/2 open incircles would overlap. This contradicts
the original interior-disjoint neighbors and excludes the
nonparallel case.

## 3. The parallel case has two neighbors beyond a full unit width

The purely physical triangle theorem makes both parallel outward
normals the same unit vector m. Nonzero common cycle moment makes
their original applications distinct: if both were p, the two
oriented moments at K would be positive magnitudes times opposite
values det(p,m), forcing that determinant and the common moment
to be zero. Hence their common exposed face is an actual K side
with axis m.

Put h=h_K(m). The full external zero moment says that the positive
weighted mean of the two actual applications is exactly h m in K.
In the m,Jm frame, K's first interval is [h-1,h] and its transverse
interval contains zero. Since O belongs to K, h<=1. Since the ray
{-t m:t>0} has no point in K, h-1>=0. Thus

    h=1.                                                (9)

Both original neighboring centers have m-coordinate at least3/2
and norm strictly less than91/60. They lie in the same rectangle
whose squared diameter is at most

    (1/60)^2+4*(181/3600)=29/144<1.

This again contradicts their disjoint unit incircles. The parallel
case is impossible too, proving (1).

## 4. A nonzero-moment external resultant cannot run along an origin side

This auxiliary statement is purely a physical triangle fact; no
radius estimate is needed. Suppose O is in the relative interior
of an actual K side, and the full external resultant F_K is
parallel to that side. In own axes put the side on y=0 and K
on 0<=y<=1. The triangle pair's vertical components sum to zero.

If both pair normals are horizontal, their physical signs agree.
The full origin moment makes their positive weighted mean have
height zero. Both actual means have nonnegative heights, so both
have height zero and each individual cycle moment vanishes. This
contradicts the nonzero common value.

Otherwise the two vertical components have opposite signs. The
actual nonparallel concurrence is q=tau F_K, tau>0, so q_y=0.
The downward normal's application has height zero. Properness
therefore forces its length to be zero: that actual application
is q itself. If its normal is the owned downward K axis, the
owned-normal nonobtuse lemma forbids the other normal's strictly
positive vertical component.

The remaining downward port is a strict bottom vertex. The upward
port is on the top side. If it is the opposite top vertex, the
unit-triangle opposite-vertices obstruction applies. If it is on
the same vertical line as the bottom vertex, its proper normal
line is vertical, giving the owned upward axis whose scalar
product with the actual downward normal is negative, again
forbidden by the owned-normal lemma. A top-side interior port
would have that same vertical axis and hence that same line;
there is no additional case. This excludes every alternative.

Thus, under nonzero common cycle moment,

    O in a K side interior implies F_K is not parallel
    to that side.                                       (10)

All actual shared-side endpoints and zero proper lengths have
been included in this argument.

## 5. Two nonzero-moment triangle blocks at one clear hub contain O openly

Suppose two actual triangle blocks meet only at K, which has no
other positive force and is physically circle-clear. Keep all
actual attachments in the two branches, whose private moment
sums supply zero full external origin moment at each triangle
vertex. Assume each actual triangle has nonzero common cycle
moment. The original K equation makes its full external
resultants for the two triangles opposite nonzero vectors.

By (1), the closed K contains a nonzero point on each of their
opposite rays. Their connecting segment contains O in its relative
interior. Thus O belongs to K and cannot be a K vertex. If O were
in a side interior, the two ray points would both lie on that
supporting side, making either full external resultant parallel
to it. This contradicts (10). Therefore

    O belongs to the open interior of K.                (11)

The two triangle moments need not have the same sign or magnitude.
The proof uses each triangle's unchanged complete external system
and does not replace a decorated branch by a new physical leaf.
No original body degree, force, selected normal, mean or corner
weight changes. No zero-moment version of (1) or (11) is asserted.
