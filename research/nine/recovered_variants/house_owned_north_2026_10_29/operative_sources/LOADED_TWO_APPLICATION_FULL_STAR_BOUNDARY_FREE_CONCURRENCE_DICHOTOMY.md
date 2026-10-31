# A loaded full star with at most two actual applications has proper concurrence or an exact radial parallel exception

Date: October 28, 2026 UTC.

Authors: h4_parallel continuation, with root's actual-point radial test
and extension to the sharp support-comparison radius window.

**Status: complete proposed arbitrary-degree hand theorem, frozen for
separate full independent and root review.** There is no boundary-neighbor
premise. Every original positive force, physical support, shared mean and
circle-corner coefficient remains. The exact exception is an actual
two-corner radial inner face with two distinct application heights, both
original force groups West, and equal positive circle weights.

This is a self-contained boundary-free extraction of the normal-line
argument in the recovered two-application source. The one-application
and parallel alternatives are proved here directly; neither is silently
discarded by importing an earlier theorem with a boundary-neighbor
premise. No original graph/load family is declared closed by this source.

## 1. Complete actual statement and original equations

Let K and all its actual positive pair neighbors be contained closed unit
squares with pairwise disjoint open interiors in the same unchanged disk
D_R about O. Assume

    sqrt(2)<R<1+sqrt(2).                                  (1)

K is genuinely loaded: its original nonnegative physical circle-corner
weights have positive total. Its true positive degree is any positive
finite number. Keep every original force, normal, physical contact set,
actual application or full shared-side mean, and all other actual units.

Use coordinates about the unchanged O=0. For each original positive pair
term write mu_i*n_i at P_i, where mu_i>0, n_i is the actual outward unit
support normal from K toward its actual neighbor L_i, and P_i belongs to
the full actual intersection K intersect L_i. At a shared contact P_i is
the original mean, with its entire physical allowed interval retained.

The full equations are

    F+sum_i mu_i*n_i=0,
    sum_i mu_i*det(P_i,n_i)=0,
    F=2*sum_j lambda_j*Z_j,
    lambda_j>=0, sum_j lambda_j>0, |Z_j|=R, Z_j in K.    (2)

Each Z_j is an actual physical circle corner. A zero individual corner
weight is allowed, including at a physically present second corner.

Assume that the unchanged set of original applications has at most two
distinct actual values. For any one such value T define only its exact
algebraic group sum and its original total magnitude:

    G_T=sum_(P_i=T) mu_i*n_i,
    W_T=sum_(P_i=T) mu_i>0.                              (3)

**Theorem.** Precisely the following exhaustive alternatives apply.

1. **One actual application P.** The point q=P belongs to the actual K
   and q=t*F for t>0. Every original force line passes through q. Its
   zero ray P-q=0 is retained; this alternative is not declared
   geometrically impossible without an additional premise.

2. **Two distinct actual applications P,Q and nonparallel group sums.**
   Both G_P and G_Q are nonzero. Their actual lines P+R*G_P and
   Q+R*G_Q have a unique intersection q, and

       q=t*F, t>0,
       P-q=ell_P*G_P/|G_P|,
       Q-q=ell_Q*G_Q/|G_Q|,
       ell_P,ell_Q>=0.                                  (4)

   If K has one physical circle corner, q belongs to K. With two
   physical circle corners q may lie outside K; every such exterior
   case is included in (4).

3. **Two distinct actual applications P,Q and parallel group sums.**
   After an orthonormal choice of axes about the same O, the actual
   unit and physical circle corners are exactly

       K=[d,a] x [-1/2,1/2],
       a=d+1=sqrt(R^2-1/4)>1,
       Z_+=(a,1/2), Z_-=(a,-1/2).                        (5)

   Their original circle weights satisfy lambda_+=lambda_->0.
   Every original pair normal is West=(-1,0), and

       P=(d,p), Q=(d,q_0),
       -1/2<=p<0<q_0<=1/2,
       W_P*p+W_Q*q_0=0,                                (6)

   after interchanging the names P,Q if needed. In particular the
   two distinct original force lines are genuinely parallel and
   distinct; no finite concurrence is asserted in this exception.

The group sums (3) do not replace the true degree or introduce a new
physical neighbor. Equation (4) concerns those exact sums. When a group
contains several nonparallel original normals, this theorem does not
assert that all their separate lines pass through q unless q is their
actual common application. For a genuine loaded degree-two unit, each
distinct-application group has one original term, so (4) is directly
the usual proper concurrence of its two original pair forces.

## 2. Complete physical circle masks and unshareable circle points

Let Z be any farthest corner of the actual K from O. Choose its two
outward side coordinates and order them to write

    Z=(a,b), K=[a-1,a] x [b-1,b],
    a>=b>=1/2, a^2+b^2=R^2.                            (7)

The inequalities a,b>=1/2 follow from comparing Z with its two actual
adjacent corners: R^2>=|(a-1,b)|^2 and
R^2>=|(a,b-1)|^2. Another adjacent corner has the same norm precisely
when the corresponding coordinate is 1/2. Both coordinates cannot be
1/2 because R>sqrt(2). Thus the full physical mask has either one
corner, or exactly the two corners in (5). A non-corner point of a
unit cannot be on the disk boundary: a nontrivial convex combination
of distinct points of the strictly convex disk lies in its interior.

No physical circle point can belong to two actual contained squares.
Indeed such a point Z must be a vertex of each. For either actual
inward unit edge u there, containment of Z+u gives

    Z.u<=-1/2.

Consequently -Z is strictly inside that unit's inward quadrant.
For sufficiently small epsilon>0 the point Z-epsilon*Z is in its
open interior. The same segment for two units containing Z would
contradict their disjoint open interiors. In particular no actual
pair application, and hence no group application, is a physical
circle corner of K.

For one physical corner, its original positive full circle load gives

    F=k*(a,b), k>0.                                    (8)

For the full two-corner mask, with both original corner coefficients
retained, write

    F=k*(a,eta), k=2*(lambda_++lambda_-)>0,
    eta=(lambda_+-lambda_-)/(2*(lambda_++lambda_-)),
    -1/2<=eta<=1/2.                                    (9)

Thus F is always nonzero. The endpoints eta=+/-1/2 correspond to
one zero coefficient in a genuinely two-corner physical mask and
are not moved into the one-physical-corner case.

The radius range (1) also gives the exact bounds

    a>=R/sqrt(2)>1,
    1/2<=b<=R/sqrt(2)<B:=1+1/sqrt(2)<2.                 (10)

The first bound refers to the ordered farthest-corner coordinates
(7). In the two-corner chart (5), a=sqrt(R^2-1/4)>1 and d>0.

## 3. A real-neighbor support bound for every original group

Let T be one actual application value and retain all its original
terms in (3). They are outward supporting normals of the same K
at the same actual T. If T is in the relative interior of a side,
all are that side axis. If T is a vertex, all lie in its closed
outward quadrant. Dotting with that quadrant's unit bisector, or
with the side axis in the first case, yields

    |G_T|>=W_T/sqrt(2)>0.                              (11)

The sum itself still supports the unchanged actual square at T:

    G_T.(X-T)<=0 for every X in K.                      (12)

For each original neighbor L_i in this group, the actual point

    T+n_i

belongs to L_i. To verify this for every original support feature,
first let T be a vertex of L_i. Its two inward orthonormal unit
edges have nonnegative components of the inward direction n_i.
Those components are each in [0,1], so their sum n_i gives a point
of the actual unit. If T is in a side interior, n_i is its inward
side axis and the complete normal segment of length one belongs
to that unit. Side endpoints are already included in the vertex
argument. Thus this fact includes all actual shared means and
normal-cone endpoints.

Convexity of the unchanged containing disk now gives the actual
weighted average

    T+G_T/W_T in D_R.

Taking its projection onto g_T=G_T/|G_T| and using (11) proves

    T.g_T+|G_T|/W_T<=R,
    T.g_T<=R-1/sqrt(2).                                (13)

This is a bound proved from the real original neighboring units.
It is not an unsupported width assertion for a hypothetical unit
with normal G_T. The exact strict comparison used below is

    R-1/sqrt(2)<R/sqrt(2),                             (14)

which is equivalent to R<1+sqrt(2). Therefore an actual group
whose supporting height is at least R/sqrt(2) is impossible.

The original full force and torque equations regroup exactly as

    F+sum_T G_T=0,
    sum_T det(T,G_T)=0.                                (15)

No different applications are identified to obtain (15), and no
original force or original torque term is discarded.

## 4. The entire one-application alternative

Suppose every original application equals the actual P in K.
Equation (15) gives G_P=-F and det(P,F)=0.

For each actual physical circle corner Z with any coefficient,
both P and Z belong to the same actual unit, so |Z-P|^2<=2.
The exact identity

    Z.P=(R^2+|P|^2-|Z-P|^2)/2
       >=(R^2+|P|^2-2)/2>0                             (16)

uses only R>sqrt(2). With the full nonnegative circle weights of
positive total it yields P.F>0. Since F is nonzero and det(P,F)=0,

    P=t*F, t=(P.F)/|F|^2>0.

Take q=P. It lies in the actual K and on every original line.
All group or original rays from q to the common application have
length zero. This proves alternative 1 without a boundary neighbor
and without attempting to exclude a configuration that the stated
premises do not exclude.

## 5. The complete parallel alternative at two distinct applications

Now let P,Q be two distinct actual application values. By (11),
both original group sums are nonzero. If they are parallel, their
nonzero sum -F makes their common axis the axis of F.

In the one-physical-corner mask (7)--(8), a group directed along
+(a,b) would support K at the unshareable physical corner (a,b).
Thus both groups would have to point along -(a,b), which uniquely
supports the opposite corner (a-1,b-1). That would give P=Q,
contrary to the two actual application values.

In the full two-corner mask (5)--(9), suppose eta!=0. A group
directed along +(a,eta) strictly supports the outer upper or lower
physical circle corner and is impossible. Both groups would then
point along -(a,eta), each with the same unique inner corner as its
application. This again contradicts P!=Q. This proof includes
eta=+/-1/2 and thus a zero individual circle coefficient.

It remains that eta=0. A group directed East has supporting height
a. Since a^2=R^2-1/4>=R^2/2 for R>sqrt(2), its height is at least
R/sqrt(2), contradicting (13)--(14). Consequently both groups point
West and both actual applications lie on the full inner face x=d.

Every original pair normal in either group is itself West. This is
immediate at a side-interior application. At the upper inner vertex,
all original outward normal y components are nonnegative; at the
lower inner vertex they are nonpositive. The aggregate y component
is zero and every original pair coefficient is positive, so every
one of those components is zero. The unit outward normal at either
inner vertex with zero y component is West. No endpoint force or
zero circle coefficient is suppressed in this argument.

Thus G_P=-W_P*(1,0), G_Q=-W_Q*(1,0). Equation (9) with eta=0
gives lambda_+=lambda_->0. Writing P=(d,p), Q=(d,q_0), the full
original torque (15) is exactly

    W_P*p+W_Q*q_0=0.                                   (17)

Their heights are distinct, and both W_P,W_Q are positive. Hence
one height is strictly negative and the other strictly positive.
Interchanging P,Q if necessary gives all of (5)--(6), including
either actual endpoint p=-1/2 or q_0=1/2. This proves the complete
parallel exception. There is no boundary-status conclusion for
its real neighbors in the theorem as stated.

## 6. Nonparallel groups and the exact radial line

Suppose instead that the two nonzero actual group sums are not
parallel. Their two original group lines have a unique intersection
q. Because each original group moment is exactly its actual common
application moment, (15) gives

    0=det(P,G_P)+det(Q,G_Q)
     =det(q,G_P+G_Q)=-det(q,F).

Thus q is on the full original circle-resultant line. No positivity
or ray direction has yet been inferred from this algebraic fact.
The next two sections establish both using the complete physical
masks, the actual normal cones and the real-neighbor bound (13).

## 7. One physical circle corner: every possible exterior q is excluded

Use the ordered actual rectangle (7), with F as in (8), and write

    q=tau*(a,b).

The interval

    1-1/a<=tau<=1                                      (18)

puts q in K: its first coordinate is in [a-1,a] and its second
is in [b-b/a,b], a subset of [b-1,b] because b<=a. Its lower
endpoint is positive because a>1. We prove that no other tau
can support two distinct actual group applications.

The outward corner cones of the actual rectangle are the four
corresponding closed coordinate quadrants. A side-interior normal
line is horizontal or vertical. These statements, including the
closed cone endpoints, determine the following exhaustive cover.

If tau>1, q is strictly above and to the right of K. The only
corner normal lines through q come from the opposite inner corner
(a-1,b-1) and the outer physical corner (a,b). No horizontal or
vertical side-interior line can pass through that q. The physical
circle corner cannot be an application, so at most one actual
application remains, contrary to P!=Q.

Suppose tau<1-1/a, so q_x<a-1. If q_y<b-1, q is strictly
below and to the left; the same cone check leaves only those
same two opposite corners, again giving at most one permitted
application. If q_y=b-1, the lower-right corner (a,b-1) is
an additional candidate only with horizontal East normal. Its
height a>=R/sqrt(2) is forbidden by (13)--(14). Thus equality
at that lower line also leaves at most one permitted point.

The only remaining exterior range is

    q_x<a-1, b-1<q_y<b.                                (19)

The strict upper inequality follows also from tau<1 and b>0.
In this strip, the complete non-circle normal-line candidates are
the inner-face point (a-1,q_y), the outer-face point (a,q_y)
with East normal, and the lower-right corner T=(a,b-1).
The other possible corner is the forbidden physical circle
corner. Vertical side lines cannot reach q_x<a-1, and the
remaining corner cones do not contain either sign of their
displacements to q. The East candidate is again excluded by
its height a. Therefore two distinct applications would require
the actual lower-right candidate T.

Its outward unit normal must have the form

    n=(cos eta_0,-sin eta_0),
    0<=tan eta_0=(b*tau-b+1)/(a*(1-tau))<(a-b)/a.        (20)

The strict upper comparison follows by substituting
tau<1-1/a; the fraction is increasing there. If a=b,
the displayed strip has no such candidate. For uniformity we
bound the supporting height on the whole closed enlarged
interval 0<=tan eta_0<=(a-b)/a.

Write e=a-b>=0 and

    f(eta_0)=a*cos eta_0-(b-1)*sin eta_0,
    N=a^2+e*(1-b), D^2=a^2+e^2.

The numerator N is positive: equivalently
N=(a^2-a*b+b^2)+(a-b)>0. On the entire closed interval the
factor a-(b-1)*tan eta_0 is positive, so f>0 and f''=-f<0.
Its minimum therefore occurs at an endpoint. At zero,
f=a>=R/sqrt(2). At the other endpoint f=N/D, and exact
expansion gives

    2*N^2-R^2*D^2
      =e*[2*b^2*(2-b)
           +e*(2+4*b-3*b^2)
           +e^2*(4-2*b)].                              (21)

All three coefficients are positive on the entire range
1/2<=b<B=1+1/sqrt(2). The first and third are positive because
b<2. The middle coefficient is a concave quadratic, and on
[1/2,B] its endpoint values are

    2+4*(1/2)-3*(1/2)^2=13/4>0,
    2+4*B-3*B^2=3/2-sqrt(2)>0.

Thus (21) is nonnegative, including e=0. As N,D are positive,
N/D>=R/sqrt(2). Both endpoints, hence the whole interval,
satisfy

    T.n=f(eta_0)>=R/sqrt(2).

This contradicts the actual group support bound (13)--(14).
It applies even when the group at T contains several original
nonparallel normals: (13) was proved for that exact group.

Every exterior tau has now been excluded. Therefore (18) holds,
q belongs to the actual K, and q is a positive multiple of F.
For each T=P,Q, its actual supporting inequality (12) gives
G_T.(q-T)<=0. Since q-T is parallel to G_T, this proves
T-q is a nonnegative multiple of G_T/|G_T|. Both full ray
conclusions (4), including a zero ray, follow.

## 8. Two physical circle corners: positive and exterior concurrence

Use the whole two-corner mask (5)--(9), including either zero
individual corner coefficient, and write

    q=tau*(a,eta).

We first prove

    tau>=d/a>0.                                        (22)

If tau<d/a, then q_x<d. When |q_y|<1/2, the complete
non-circle candidates are the inner-face point (d,q_y) and
the outer-face point with horizontal East normal. Both outer
corners are physical circle points and cannot be applications.
The East candidate has height a>=R/sqrt(2) and is forbidden
by (13)--(14). At q_y=+/-1/2 the inner-face candidate is
its endpoint and the same conclusion holds. If q_y>1/2,
only the upper inner corner and the opposite outer circle
corner can have a supporting normal line through q; if
q_y<-1/2, only the lower inner corner and its opposite
outer circle corner can do so. These assertions follow
from the four closed corner cones and the absence of side
lines at an exterior x or y coordinate. In every case
at most one permitted actual application remains. Since
P and Q are distinct, this proves (22).

If d/a<=tau<=1, then d<=q_x<=a and |q_y|<=1/2.
Thus q belongs to K. The supporting-half-plane argument
at the end of Section 7 immediately proves both proper
rays. Its radial coefficient is positive by (22).

It remains that tau>1, so q_x>a. If q_y>1/2, only
the lower inner corner and the upper outer circle corner
have possible normal lines through q. If q_y<-1/2,
the analogous pair is the upper inner corner and the
lower outer circle corner. In either case the actual
outer circle point is unavailable and two distinct
applications are impossible. Therefore every surviving
exterior concurrence satisfies exactly

    q_x>a, |q_y|<=1/2.                                 (23)

In this closed exterior strip, every possible non-circle
support point lies on the inner face x=d, including either
inner endpoint, except for a horizontal East support on
the outer face. The latter has forbidden height a. This
again exhausts all four corner cones and the side-interior
horizontal or vertical lines; a vertical side line cannot
reach q_x>a, and any remaining outer corner is physical.

For either actual T=P,Q on the inner face, T-q has strictly
negative x component. Its actual outward group normal also
has negative x component: at a side interior it is West;
at an inner corner a zero x component would give a vertical
line unable to pass through q_x>a. Since T-q and G_T are
parallel and their x components have the same sign,

    T-q=ell_T*G_T/|G_T|, ell_T>0.

Equation (22) still gives q a positive multiple of F.
This proves (4) for every exterior case (23), including
q_y=+/-1/2 and eta=+/-1/2. No assertion that this exterior
q belongs to K is made, and no equality of its original
two corner weights was imposed in the nonparallel case.

Sections 4, 5, 7 and 8 prove the complete exhaustive theorem.

## 9. Exact broad corollaries and limits at the original packing window

The original closed interval

    79/40<=R<=sqrt(1105)/16

lies strictly in (1). Its lower endpoint exceeds sqrt(2),
as 6241/1600>2. Its upper endpoint is less than 1+sqrt(2):
1105/256<5<3+2*sqrt(2). The theorem therefore applies
throughout that full original interval without dropping
either closed radius endpoint.

For a genuinely loaded two-force unit, no boundary-neighbor
premise is needed in any nonparallel feature. Distinct
nonparallel original lines satisfy (4); coincident actual
applications are retained by Section 4. The only distinct-
application parallel exception is exactly (5)--(6), with
both original pair forces pointing inward toward the
circle center from the radial inner face.

If the two original forces are owned by perpendicular
sides of the actual loaded unit, their intersection q
lies in that unit: each coordinate is the unchanged side
coordinate of one original application. Equation (16)
also gives its positive radial direction directly. This
is a useful special case of the general theorem, with
all original side positions and endpoints retained.

For a higher-degree loaded star, a caller may use this
theorem only if the full original applications actually
have at most two distinct values. It may group forces at
one common actual point by (3), but may not move a mean,
group distinct points by visual proximity, or delete an
unwanted original force to create the premise.

In a three-load four-spoke pentagon, genuine E2 has exactly
its two original pair forces toward A,D. Thus the theorem
applies even when both actual neighbors are physically
clear. It supplies the full positive-ray statement in
its nonparallel features and the exact remaining parallel
mask in its parallel features. It does not itself prove
which feature that original E has, nor close either
original H4_D0 load family. A whole-family caller must
retain that full alternative and its original masks.

## 10. Provenance, exact inputs and review boundary

The current full force/torque and actual-mean contract is

    PHYSICAL_CONTACT_STRESS.md
    SHA-256 d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5.

All physical facts needed beyond that explicitly stated
contract, including common-point support reach, the full
corner masks, unshareability and every normal-line cover,
were proved above.

The recovered predecessor is

    LOADED_TWO_APPLICATION_FULL_STAR_PROPER_CONCURRENCE.md
    SHA-256 942ed38a7452f35e95839cc79ea15ed97091114495e9a3ab9c232ae8255a0ea0,

at saved checkout HEAD

    312e0710d7cbe71cfa26f07d6db1ebae980e1c2f.

Its exact existing separate review is

    REVIEW_LOADED_TWO_APPLICATION_FULL_STAR_PROPER_CONCURRENCE_RECOVERY_AUDIT_2026_10_28.md
    SHA-256 b91f1283a238615a9a05fb849add9dd0823a9a60c4b95e3351d2512c214b6e4b.

These identify provenance; their boundary-neighbor theorem
is not invoked here to discard either of its previously
excluded alternatives. Its frozen source and old review
remain unchanged, and the old review is not claimed to
accept this new larger theorem.

This manuscript preserves every actual unit and original
degree, force, normal, application, shared mean, physical
circle corner and individual zero coefficient. It uses no
selection rule, circle translation, numerical pose search,
angle mesh or computational geometric exclusion. It changes
no source prerequisite, original flag, ledger or count.
No Lean or Lake invocation, checker replay, CI, workflow,
commit, remote operation or mutation of the saved recovery
checkout was performed. Full separate independent review
and current root adoption are required for these exact bytes.

