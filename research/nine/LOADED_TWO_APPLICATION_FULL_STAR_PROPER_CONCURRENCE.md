# Every full loaded star with at most two actual applications and a boundary neighbor has proper concurrence

Date: October 28, 2026 UTC. Author: pentagon_uniform continuation.

**Status: new complete proposed arbitrary-degree theorem, frozen for
separate independent and root review.** This is a theorem about all
original forces of one actual loaded square. Nonparallel forces at a
common application are allowed and remain in the original system.
No original graph/load family is declared closed.

## 1. Full physical statement

Let K be an actual unit square in the unchanged disk D_R about O,
where

    79/40<=R<=sqrt(1105)/16.                              (1)

K has strictly positive total circle load and an arbitrary positive
number of actual positive pair forces. Keep every original force,
normal, application or full shared-side mean, physical circle corner,
individual zero coefficient and other actual unit. Suppose all original
positive pair applications belong to a set of at most two actual
points P,Q of K. Assume at least one actual positive pair neighbor
of K physically touches the containing circle; that neighbor's own
total circle coefficient need not be positive.

Write each original outward force as mu_i*n_i, with mu_i>0 and unit
n_i, and write the full nonzero circle resultant as F. The entire
original equations, in coordinates with O=0, are

    F+sum_i mu_i*n_i=0,
    sum_i mu_i*det(P_i,n_i)=0,
    F=2*sum_j lambda_j*Z_j,
    lambda_j>=0, sum_j lambda_j>0, |Z_j|=R.             (2)

Every original P_i is P or Q and remains its actual physical point
or full side mean.

**Theorem.** There are exactly two distinct application points, each
with a nonempty group of original forces. Define only their exact
algebraic sums

    G_P=sum_(P_i=P) mu_i*n_i,
    G_Q=sum_(P_i=Q) mu_i*n_i.                            (3)

Both sums are nonzero. Their two actual lines P+R*G_P and Q+R*G_Q
are nonparallel and meet at a point q satisfying

    q=t*F, t>0,
    P-q=ell_P*G_P/|G_P|,
    Q-q=ell_Q*G_Q/|G_Q|,
    ell_P,ell_Q>=0.                                    (4)

If K has one physical circle corner, q belongs to K. With two physical
circle corners q can be outside K, and only the full ray statements
(4) are asserted. Neither (3) nor (4) reclassifies K's true degree,
assigns it a new physical neighbor, or changes an original normal.

## 2. A complete support bound for every original common-point group

We prove the geometric bound needed for the sums (3), rather than
assuming that either sum is the normal of a nonexistent neighboring
unit.

Let I be a nonempty set of actual positive pair forces all applied
at the same physical point T of K. Let

    W=sum_(i in I) mu_i,
    G=sum_(i in I) mu_i*n_i.

All n_i are actual outward supporting normals of K at T. If T is in
the relative interior of a side, they are that same side axis. If T
is a vertex, they belong to its closed outward quadrant. Let w be
the unit bisector of that quadrant. In the vertex case
n_i.w>=1/sqrt(2) for every i; in the side case choose the side axis
as w. Consequently

    |G|>=G.w>=W/sqrt(2)>0.                             (5)

The positive sum itself supports the unchanged square at the same
actual point:

    G.(X-T)<=0 for every X in K.                        (6)

Each original neighboring unit L_i contains the actual point

    T+n_i.                                              (7)

Indeed T is a minimum-n_i support of L_i. At a vertex of L_i,
resolve n_i in its inward orthonormal axes: both components belong
to [0,1], so T+n_i belongs to the unit. At a side-interior point,
n_i is the inward side axis and its complete unit normal segment
from T belongs to L_i. Side endpoints are included in the vertex
calculation. This proof retains the whole actual neighbor pose.

Every point (7) belongs to D_R. Since this disk is convex, their
positive weighted average also belongs to it:

    T+G/W in D_R.

Taking its projection on n=G/|G| and using (5) gives

    T.n+|G|/W<=R,
    T.n<=R-1/sqrt(2).                                  (8)

Equation (8) is the proved support-height bound for a possibly
nonparallel common-point group. It is weaker than the original
single-neighbor width-one bound, but it is sufficient here.

For later rectangle exclusions note the strict comparison

    R/sqrt(2)>R-1/sqrt(2),                              (9)

because R<1+sqrt(2) in (1). Thus any group normal with actual support
height at least R/sqrt(2) is impossible by (8).

All normal and moment identities of (3) are exact linear sums of
(2). In particular the group torque is det(T,G), because the
original applications in that group really coincide. No two
different side means are moved to create this premise.

## 3. The one-application and complete parallel exits

If there is only one actual application, the arbitrary-degree theorem
LOADED_COINCIDENT_PORT_STAR_NO_BOUNDARY_NEIGHBOR.md applies to the
entire original loaded star. It excludes the actual boundary neighbor
at that point. Its radius premise R>3/2 holds in (1). Therefore P,Q
are distinct and both groups in (3) are nonempty.

For completeness the physical circle masks of K have the following
complete rectangle description. Choose outward side coordinates at
a physical farthest corner Z=(a,b) and order them so that

    K=[a-1,a] times [b-1,b],
    a>=b>=1/2, a^2+b^2=R^2.                            (10)

The lower coordinate bounds follow by comparing Z with its two
adjacent corners. Another corner has the same norm exactly when
one coordinate equals 1/2. Since both cannot equal 1/2 in (1),
there is either one physical circle corner, or the full two-corner
pose

    K=[d,d+1] times [-1/2,1/2],
    a=d+1=sqrt(R^2-1/4), d>9/10.                       (11)

A physical circle point cannot be shared by two actual units.
At such a point Z, each of the two inward unit axes v of any
contained square satisfies Z.v<=-1/2 by containment of Z+v.
Thus -Z is strictly inside that square's inward quadrant, and a
short segment Z-epsilon*Z lies in its open interior. Two actual
units containing Z would have overlapping open interiors.

Suppose now G_P,G_Q are parallel. Their nonzero full sum is -F
by (2), so their common axis is the axis of F.

With one physical circle corner, F is a positive multiple of Z.
A group directed along +Z would support K at the unshareable
physical circle corner. Thus both groups must point along -Z;
each then has the unique opposite inner vertex as application,
contradicting P!=Q.

With two physical circle corners, normalize the complete resultant
direction as

    F=k*(a,eta), k>0, |eta|<=1/2.                       (12)

If eta is nonzero, a group directed along +(a,eta) has an outer
physical circle corner as its support, again impossible. Both
groups along -(a,eta) have the same inner corner as application,
again contradicting distinctness.

If eta=0, an East group has support height a>=R/sqrt(2), excluded
by (8)--(9). Thus both groups must be West and their applications
belong to the actual inner face x=d. Every original normal in
each such group is also West. At a side-interior point this is
immediate. At either inner vertex all permitted normal y components
have one sign, so positivity of every coefficient and the aggregate's
zero y component force every one of them to have zero y component.
Its outward x sign is West.

In particular the actual boundary neighbor in the theorem has its
unchanged minimum-West contact at some point (d,h), |h|<=1/2.
The full physical radial-inner-face theorem, C7_FORCE_POLYGON.md,
Lemma 2.1, excludes a boundary unit at that contact. That lemma
covers every neighbor frame, side application and both endpoints;
its hypothesis d>9/10 holds by (11). This contradiction completes
the entire parallel case.

Consequently the group lines are nonparallel. Let q be their unique
intersection. Full torque about q, or equivalently (2) and the
exact common-point sums, gives

    det(q,F)=0.                                         (13)

No original force has been deleted to obtain this concurrence.

## 4. One physical circle corner: the concurrence lies inside the actual unit

Use (10). Equation (13) gives q=tau*(a,b). Since a>=b and a>1,
the range

    1-1/a<=tau<=1                                      (14)

puts q inside K: its x coordinate is in [a-1,a], while
b*tau>=b-b/a>=b-1. It also gives tau>0. We exclude all other
values using only the real square's normal cones, distinct P,Q,
the unshareable circle point, and the proved group bound (8).

If tau>1, q is strictly above and to the right of K. Among its
vertices only the outer circle corner and the opposite inner corner
can have supporting normal lines through q; no side-interior normal
line can do so. The circle corner cannot be an application, leaving
only one actual point for both groups, contrary to P!=Q.

Suppose tau<1-1/a, so q_x<a-1. If q_y<b-1, the same rectangle
normal-cone check again leaves only the opposite inner and outer
circle vertices. If q_y=b-1, the lower-right vertex (a,b-1) is
an additional possibility, with horizontal East normal; its height
a>=R/sqrt(2) is excluded by (8)--(9). Thus these alternatives
cannot give two distinct applications.

The remaining range is

    q_x<a-1, b-1<q_y<b.                                (15)

The only non-circle supporting normal lines through q are the
left-side point (a-1,q_y), a right-side point with East normal,
and the lower-right vertex p=(a,b-1). The right-side point has
the same forbidden height a. Two distinct applications would
therefore require p to be one of them.

Its supporting normal is of the form

    n=(cos eta,-sin eta),
    0<=tan eta=(b*tau-b+1)/(a*(1-tau))<(a-b)/a.         (16)

On the closed enlarged interval in (16), its support value obeys

    p.n=a*cos eta-(b-1)*sin eta>=R/sqrt(2).             (17)

Here is the full algebraic comparison. The expression is positive
and concave on that interval, so its minimum is attained at an
endpoint. At zero it is a>=R/sqrt(2). At the other endpoint put
e=a-b>=0,

    N=a^2+e*(1-b), D^2=a^2+e^2.

That endpoint value is N/D, with N>0. Expansion gives

    2*N^2-R^2*D^2
      =e*[2*b^2*(2-b)+e*(2+4*b-3*b^2)+e^2*(4-2*b)]
      >=0.                                             (18)

Every coefficient in brackets is positive on 1/2<=b<3/2;
the latter bound follows from b<=R/sqrt(2)<3/2 in (1).
This proves (17), including e=0. It is the complete continuous
rectangle comparison; no angular samples are used.

Whether p carries one original force or many nonparallel ones,
(17) contradicts the common-point group bound (8)--(9).
Therefore (15) is impossible as well. This proves (14), so

    q in K, q=t*F with t>0.                             (19)

For either actual group point T=P or Q, q lies on its normal
line and inside the supporting half-plane of the same K. Thus
T-q is a nonnegative multiple of G_T/|G_T|. This proves both
ray statements of (4) throughout the one-circle-corner case.

## 5. Two physical circle corners: all coefficients and exterior concurrences

Use (11)--(12) and write q=tau*(a,eta). We first prove

    tau>=d/a>0.                                        (20)

If tau<d/a, then q_x<d. When |q_y|<1/2, the rectangle normal-line
classification permits only the inner-face point (d,q_y), outer
circle corners, and the horizontal East normal at an outer-face
point. The circle corners cannot be shared and the East height
a is excluded by (8)--(9). Hence only one actual application
remains. At q_y=+/-1/2 the inner-face point is its endpoint and
the same conclusion holds. If q_y>1/2 or q_y<-1/2, the same
normal-cone check leaves only one corresponding inner corner
and an outer circle corner. These alternatives again cannot
give the distinct P,Q. This proves (20).

For d/a<=tau<=1, the point q belongs to K, since its x coordinate
is between d and a and |q_y|<=1/2. The same supporting-half-plane
argument as in Section 4 proves (4).

Suppose tau>1, so q_x>a. If |q_y|>1/2, the normal-cone check
leaves just one non-circle inner corner: the lower inner corner
when q_y>1/2, or the upper one when q_y<-1/2. The other candidate
is an unshareable outer circle corner. This cannot provide two
distinct application points.

Thus every remaining exterior concurrence has

    q_x>a, |q_y|<=1/2.                                 (21)

All its possible non-circle contacts are on the inner face x=d,
including either endpoint, except for an outer-face horizontal
normal, which is again excluded by its height a. For each actual
inner-face point T, the vector T-q points strictly left. It lies
on that point's group normal line. Its sign agrees with the
outward West, northwest or southwest support cone of K there.
Consequently

    T-q=ell_T*G_T/|G_T|, ell_T>0,

for T=P,Q. This includes q_y=+/-1/2 and every original endpoint
coefficient. Equation (20) also gives q=t*F with t>0. Thus (4)
holds throughout the whole two-circle-corner mask, even when q
lies outside the actual unit. No equality of the two original
circle coefficients has been imposed.

Together Sections 3--5 prove the entire theorem.

## 6. Exact broad scope and the legitimate H4 coincidence interface

The theorem applies to arbitrary true positive degree and arbitrary
numbers of original forces at each of the two points. It permits
nonparallel normals in either group. It requires actual coincident
applications; a shared contact with a different original mean is
not moved or absorbed into a group at an endpoint. It also requires
an actual boundary neighbor and the positive full circle load.

In the H4_D0 configuration, if the full loaded C3 has its original
CD and CH applications at the same actual C vertex P, and its
third original force is the actual CB contact with boundary B,
the theorem applies to all three original C forces. It either
excludes the single-application case P_CB=P or gives a proper
concurrence for the exact two sums

    G_P=f_CD+f_CH, G_Q=f_CB.

Every original force, coefficient and application is still present.
This is not an invocation of a true-degree-two theorem at C.
If HC is a positive-length shared side with its original mean
different from P, the stated two-application premise has not been
proved and this corollary does not apply automatically.

No H4 feature or full original family is excluded by this generic
concurrence statement alone. A caller must still prove its actual
geometry, occupied order and the contradiction it needs.

## 7. Exact operative inputs and verification boundary

| Source | Current SHA-256 | Exact use |
| --- | --- | --- |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Full original force, moment, physical support and circle-atom conventions |
| LOADED_COINCIDENT_PORT_STAR_NO_BOUNDARY_NEIGHBOR.md | 18ad8dbde48a1c0ef6828ef199a321c54218e5ba3c39c4047025783ffb63bb83 | Complete arbitrary-degree one-application exit with an actual physical boundary neighbor |
| C7_FORCE_POLYGON.md | d50d8ca48ea19156175e651bfa74be30ef3e58065ec14d8d1834670a41559089 | Full physical radial-inner-face Lemma 2.1 in the parallel exit; Sections 4--5 provide the normal-line classification and algebra rederived here with the newly proved group bound |

The new ingredient (5)--(8) is proved from the real neighboring
units, and supplies precisely the support control missing from
an unsupported two-force substitution. The normal-line proof,
parallel exits, physical circle masks and outside-q cases are
all included above. No additional unit is created for either
algebraic sum and no original true degree is changed.

No pose search, sampled angle, numerical exclusion, selected-normal
modification, moved mean, Lean build, CI, workflow, metadata change,
commit or remote action is used. These exact bytes require complete
separate independent review and root rederivation before adoption.
