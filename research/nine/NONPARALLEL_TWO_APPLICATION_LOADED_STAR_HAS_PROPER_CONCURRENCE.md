# Two distinct nonparallel application groups give proper concurrence without a boundary neighbor

Date: October 28, 2026 UTC. Author: pentagon continuation.

**Status: complete proposed uniform hand theorem, frozen for separate
independent and root review.** Every original force, actual neighboring
unit, application mean and physical circle mask is retained. No original
graph/load family is declared excluded.

The physical boundary-neighbor hypothesis in
LOADED_TWO_APPLICATION_FULL_STAR_PROPER_CONCURRENCE.md is needed for
that source's preliminary one-application and parallel exits. It is
unnecessary for its nonparallel rectangle argument. The complete
stronger statement and proof are given here. The proof also works on
the larger open radius interval displayed below.

## 1. Exact full-star statement

Let K and all of its actual positive pair neighbors be closed unit
squares with pairwise disjoint open interiors in the same actual disk
D_R centered at O, where

    sqrt(2)<R<1+sqrt(2).                                  (1)

K has positive total circle load and arbitrary positive pair degree.
In coordinates with the unchanged O=0, retain the entire original
equations

    F+sum_i mu_i*n_i=0,
    sum_i mu_i*det(P_i,n_i)=0,
    F=2*sum_j lambda_j*Z_j,
    mu_i>0, lambda_j>=0, sum_j lambda_j>0, |Z_j|=R.        (2)

Each n_i is the original outward unit support normal of K at its
unchanged physical application P_i. The same point is the original
minimum-n_i support of the real neighboring square. Every original
shared-side mean remains its actual point, including either endpoint.

Assume that the set of original positive pair applications consists
of exactly two distinct actual points P,Q. Define their exact sums

    G_P=sum_(P_i=P) mu_i*n_i,
    G_Q=sum_(P_i=Q) mu_i*n_i.                            (3)

Assume that these two aggregate vectors are nonparallel. In particular
this is a literal condition on the complete original sums, not a
replacement of either group by a new physical neighbor.

**Theorem.** The two actual lines P+R*G_P and Q+R*G_Q meet at a point q
such that

    q=t*F, t>0,
    P-q=ell_P*G_P/|G_P|,
    Q-q=ell_Q*G_Q/|G_Q|,
    ell_P,ell_Q>=0.                                    (4)

If K has one physical circle corner, q belongs to K. For two physical
circle corners q can be exterior, and only (4) is asserted.

No positive pair neighbor is required to touch the circle. The theorem
does not exclude a coincident-application or parallel-group case; those
cases simply do not satisfy its two explicit entry hypotheses.

The original interval 79/40<=R<=sqrt(1105)/16 lies strictly in (1).
Indeed 79/40>sqrt(2), while sqrt(1105)/16<21/10<1+sqrt(2).

## 2. Actual neighbor reach bounds every full common-point group

Let I be a nonempty original group at an actual point T of K, and put

    W=sum_(i in I) mu_i,
    G=sum_(i in I) mu_i*n_i.

At a side-interior point of K all n_i are the same side axis. At a
vertex all belong to its closed outward quadrant. Dot with that
quadrant's unit bisector, or with the side axis in the side-interior
case. Positivity of every original coefficient gives

    |G|>=W/sqrt(2)>0,
    G.(X-T)<=0 for every X in K.                         (5)

Thus G is nonzero and supports the actual K at the unchanged T.

For each original real neighboring unit L_i, the point

    T+n_i belongs to L_i.                               (6)

To check this at a vertex of L_i, write n_i in its two actual inward
orthonormal axes. Both components are in [0,1], so the unit step
lies in the same physical square. At a relative side-interior
support, n_i is its inward side axis and the whole unit normal
segment is in the square. A side endpoint is included by the vertex
argument. This uses the real neighbor, not an auxiliary support body.

Every point (6) is in D_R. By convexity of the disk their positive
weighted average T+G/W is also in it. Projection onto n=G/|G| gives

    T.n+|G|/W<=R,
    T.n<=R-1/sqrt(2).                                  (7)

The radius condition in (1) gives the strict comparison

    R/sqrt(2)>R-1/sqrt(2).                              (8)

Consequently an actual group normal with support height at least
R/sqrt(2) is impossible. This proves the full support-height input
for either group, including arbitrarily many nonparallel original
normals at the same point.

Since the applications within a group literally coincide, its torque
is exactly det(T,G). Thus (2) gives the unchanged identities

    F+G_P+G_Q=0,
    det(P,G_P)+det(Q,G_Q)=0.                            (9)

No actual side mean is moved to obtain them.

## 3. Complete physical circle masks and concurrence

Choose actual orthonormal own coordinates and signs so a physical
farthest corner of K is Z=(a,b), with a>=b. Keep O=0. Containment
of the adjacent corners and physical contact with the circle give

    K=[a-1,a] times [b-1,b],
    a>=b>=1/2, a^2+b^2=R^2.                           (10)

The radius interval (1) implies

    a>=R/sqrt(2)>1,
    1/2<=b<=R/sqrt(2)<1+1/sqrt(2)<2.                  (11)

Another corner has the same norm exactly when an own coordinate of
Z equals 1/2. Since a>1, there is one physical circle corner when
b>1/2 and exactly two when b=1/2. The latter complete pose is

    K=[d,a] times [-1/2,1/2],
    a=sqrt(R^2-1/4), d=a-1>0.                          (12)

Both physical corners are retained even when one individual circle
coefficient is zero.

A physical circle point cannot belong to two of the actual units.
Indeed, a point Z on the containing circle must be a vertex of each
contained unit containing it. If v is either inward unit side vector
there, containment of Z+v gives Z.v<=-1/2. Hence -Z has strictly
positive components in both inward axes. For sufficiently small
epsilon>0 the same point Z-epsilon*Z lies in the open interior of
each such unit, contradicting disjoint open interiors. In particular
no actual positive pair application is a physical circle corner.

In the one-circle-corner case F is a positive multiple of (a,b). In
the two-circle-corner case its full unchanged mask has the form

    F=k*(a,eta), k>0, |eta|<=1/2.                       (13)

Thus F is nonzero in every case. Nonparallelness of G_P,G_Q gives
their unique line intersection q. Using (9) and the actual two
lines through q gives

    0=det(q,G_P+G_Q)=-det(q,F).                         (14)

Therefore q= tau*(a,b) in (10) for one physical circle corner, or
q=tau*(a,eta) in (12)--(13). The sign of tau is not assumed.

## 4. One physical circle corner: every exterior alternative is excluded

Use (10), with b>1/2. The closed interval

    1-1/a<=tau<=1                                      (15)

puts q inside K: its first coordinate is in [a-1,a], and its second
coordinate is at least b-b/a>=b-1 and at most b. It also gives
tau>0, by a>1. We exclude all other values of tau.

If tau>1, q is strictly above and right of K. The only vertices
whose supporting normal lines pass through q are the opposite
inner corner and the outer physical circle corner. No side-interior
normal line can pass through q. The outer circle corner is not an
actual application, so two distinct application points are impossible.

Now suppose tau<1-1/a, so q_x<a-1 and q_y<b. If q_y<b-1, the same
complete normal-cone check permits only the inner and outer opposite
corners. If q_y=b-1, it additionally permits the lower-right corner
with horizontal East normal. That normal has support height a>=
R/sqrt(2), forbidden by (7)--(8). Thus these cases cannot give the
two distinct original points.

It remains to consider

    q_x<a-1, b-1<q_y<b.                               (16)

The non-circle supporting normal lines through q can occur only at
the actual left-side point (a-1,q_y), a right-side point with East
normal, or the lower-right vertex p=(a,b-1). The right-side East
normal again has forbidden height a. Hence two distinct applications
require the vertex p to carry one of the complete groups.

Its outward unit group normal must have the form

    n=(cos eta_0,-sin eta_0),
    0<=tan eta_0=(b*tau-b+1)/(a*(1-tau))<(a-b)/a.       (17)

The weak enlarged interval 0<=tan eta_0<=(a-b)/a is sufficient for
the following continuous support comparison:

    p.n=a*cos eta_0-(b-1)*sin eta_0>=R/sqrt(2).          (18)

Here is its full algebra. Put e=a-b>=0. On the displayed closed
angular interval the expression in (18) is positive. Its numerator
after division by cos eta_0 is at least

    a-(b-1)*e/a

when b>=1, and is at least a when b<=1. The former lower bound is
positive because a^2-e*(b-1)=a^2-a*b+b^2+e>0. Therefore the second
derivative of the expression is its strictly negative opposite, so
it is concave. Its minimum is attained at an endpoint.

At eta_0=0 its value is a>=R/sqrt(2). At the other endpoint set

    N=a^2+e*(1-b), D^2=a^2+e^2.

The value is N/D and N>0 by the preceding comparison. Expansion
using R^2=a^2+b^2 gives

    2*N^2-R^2*D^2
      =e*[2*b^2*(2-b)
            +e*(2+4*b-3*b^2)+e^2*(4-2*b)]>=0.          (19)

The first and last bracketed coefficients are positive for
1/2<=b<2. For the middle coefficient use the sharper bound in (11),
namely b<1+1/sqrt(2). The concave quadratic 2+4*b-3*b^2 has endpoint
values 13/4 and 3/2-sqrt(2)>0 on the enlarged closed interval
[1/2,1+1/sqrt(2)], so it is positive throughout that interval.
Squaring positive quantities in (19) proves the second endpoint
bound, including e=0. Concavity proves (18) on the entire closed
domain. No angular samples or omitted weak endpoints are involved.

But (18) contradicts (7)--(8) for the actual full group at p.
This excludes (16). Consequently (15) holds, q belongs to K, and
q=t*F with t>0.

For T=P or Q, the point q lies on the actual group normal line and
in the support half-plane of K at T. By (5), T-q is a nonnegative
multiple of G_T/|G_T|. This proves both ray statements in (4) for
the entire one-physical-circle-corner domain.

## 5. Two physical circle corners: every exterior concurrence and zero weight

Use (12)--(13), with q=tau*(a,eta). First we prove

    tau>=d/a>0.                                       (20)

If tau<d/a, then q_x<d. For |q_y|<1/2 the only possible supporting
normal lines are at the inner-face point (d,q_y), an outer physical
circle corner, or an outer-face point with East normal. The circle
corners are not applications, and the East normal has height
a>=R/sqrt(2), forbidden by (7)--(8). Thus only one actual point is
available. At q_y=+/-1/2 the inner-face point becomes its endpoint
and the same conclusion holds. For q_y>1/2 or q_y<-1/2 the normal
cones leave only one respective inner corner and an outer circle
corner. These cases also cannot give the two distinct original
application points. This proves (20), without assuming a sign for
eta or a positive coefficient at each physical corner.

For d/a<=tau<=1, q belongs to K: d<=q_x<=a and |q_y|<=1/2. The
support half-plane argument from Section 4 therefore gives (4).

Suppose tau>1. If |q_y|>1/2, the normal-cone check leaves only one
non-circle inner corner: the lower one for q_y>1/2 and the upper
one for q_y<-1/2. The other candidate is an unshareable outer circle
corner. This cannot give two distinct applications.

Every remaining exterior concurrence consequently satisfies

    q_x>a, |q_y|<=1/2.                                (21)

All non-circle contacts whose support normal lines can pass through
q are on the actual inner face x=d, including both endpoints, except
for an outer-face East normal, again excluded by (7)--(8). For each
actual group application T on the inner face, T-q points strictly
left and belongs to that point's outward West, northwest or southwest
support cone. It is parallel to its actual G_T, with the same sign.
Hence

    T-q=ell_T*G_T/|G_T|, ell_T>0.                       (22)

The full endpoint cases q_y=+/-1/2 are included. Equation (20)
also gives q=t*F with t>0. This proves (4) for the complete exterior
two-corner domain, without asserting that q belongs to the square.

Sections 4--5 exhaust all physical circle masks and finish the theorem.

## 6. Exact E2 interface and preservation boundary

For a genuinely degree-two loaded body E, the two groups are its two
original pair forces. Thus (4) applies whenever its two unchanged
applications are literally distinct and its original normals are
nonparallel, regardless of whether either neighbor physically touches
the circle. A caller must establish both conditions before invoking
the theorem. No claim of properness in the omitted parallel case is
made here.

More generally, (4) applies at arbitrary true degree when all original
applications literally belong to the displayed two-point set and
the exact full sums in (3) are nonparallel. Original nonparallel
normals at either common point remain unchanged, and every real
neighbor remains in the proof through (6)--(7).

The result is a uniform export, not a complete H4_D0.L124 exclusion.
That family retains its original six-body equations and all three
additional units. This theorem supplies a stronger legitimate E2
input only on a caller's established distinct/nonparallel interface.

## 7. Exact operative sources

| Source | SHA-256 | Exact use |
| --- | --- | --- |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Original full force, moment, support and circle-atom conventions |
| LOADED_TWO_APPLICATION_FULL_STAR_PROPER_CONCURRENCE.md | 942ed38a7452f35e95839cc79ea15ed97091114495e9a3ab9c232ae8255a0ea0 | The group reach and nonparallel rectangle arguments, completely rederived here without its preliminary boundary-neighbor exits |

The larger radius range (1) is proved directly: (8) uses its strict
upper bound; (11), (15), (20) use its strict lower bound; and (19)
uses b<1+1/sqrt(2), already supplied by (1). No other radius-dependent
lemma is imported. No normal is reselected after stress, no new
neighbor is assigned to a group, and no application or mean is moved.
No metadata, graph/load flag, computational certificate, Lean source,
build, CI, commit or remote state is changed.
