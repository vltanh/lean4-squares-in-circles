# Independent review: proper concurrence for a full loaded star at two actual applications

Date: October 28, 2026 UTC. Reviewer: recovery_audit continuation.

**Verdict: PASS for the exact newly frozen source below.** I independently
read the entire new proof and its three direct inputs, checked the original
force and torque conventions, and rederived the common-point group bound,
single-application exit, complete parallel cover, every rectangle
normal-line case, the continuous support inequality, and the full
two-circle exterior-concurrence ray conclusion. No source edit is needed.

Reviewed source:

`LOADED_TWO_APPLICATION_FULL_STAR_PROPER_CONCURRENCE.md`

* Length: 15,874 bytes.
* SHA256: `942ed38a7452f35e95839cc79ea15ed97091114495e9a3ab9c232ae8255a0ea0`.
* Git blob: `cf33907206c49db9ce95dfe279822bcdcf7bea25`.

This is a fresh review of an arbitrary-degree theorem permitting
nonparallel forces at the same actual point. It does not transfer a
true-degree-two concurrence theorem to a larger star. All original
physical squares, positive forces, support normals, application points,
shared-side means, physical circle masks and individual zero circle
coefficients are retained.

## 1. Exact statement and accounting scope

The actual unit K is contained in the original radius window

    79/40 <= R <= sqrt(1105)/16.

It has positive total circle load and an arbitrary nonempty full positive
pair-force star. All original positive pair applications occupy at most
two actual points of K. At least one original positive pair neighbor is
physically boundary; that neighbor need not have positive circle load.

The conclusion first excludes one application. At the resulting two
distinct actual points P,Q, their nonempty exact force sums G_P,G_Q are
nonzero. Their normal lines are nonparallel and intersect at q satisfying

    q=t F, t>0,
    P-q=ell_P G_P/|G_P|,
    Q-q=ell_Q G_Q/|G_Q|,
    ell_P,ell_Q>=0,

where F is the full original circle resultant. If K has one physical
circle corner then q belongs to K. If it has two physical circle corners,
the conclusion permits q outside K and asserts the two proper rays.

The theorem does not create a physical unit for either group. It neither
changes K's true degree nor changes a normal or a mean. It requires the
actual coincidence of the applications within each group. In particular
it does not move a third shared-side mean to an endpoint to create a
two-point premise.

The H4 example in the source is a legitimate conditional application:
when loaded C3 has its original CD and CH applications at one actual
vertex P and its remaining CB neighbor is physical boundary, the full
three-force star has at most two applications. Its exact sums are
f_CD+f_CH and f_CB. The theorem alone gives no H4 exclusion and no
original fine/coarse closure credit.

## 2. Exact direct identities and original equations

All three direct source pins match the current checkout bytes:

| Input | SHA256 | Independently checked use |
| --- | --- | --- |
| PHYSICAL_CONTACT_STRESS.md | `d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5` | Complete original physical support, circle, force and torque conventions; actual closed shared means. |
| LOADED_COINCIDENT_PORT_STAR_NO_BOUNDARY_NEIGHBOR.md | `18ad8dbde48a1c0ef6828ef199a321c54218e5ba3c39c4047025783ffb63bb83` | Complete arbitrary-degree single-application theorem, including both radial physical shapes and all coefficient endpoints. |
| C7_FORCE_POLYGON.md | `d50d8ca48ea19156175e651bfa74be30ef3e58065ec14d8d1834670a41559089` | Actual radial-inner-face boundary-neighbor exclusion in Lemma 2.1; normal-line and scalar calculations in Sections 4--5, independently rederived for the new group bound. |

No historical newline identity is needed for these pins. The C7 theorem
about an entire all-boundary cycle is not a premise of the new theorem.
In particular its two actual neighbors and its inside-q conclusion for
two physical circle corners are not imported.

The original physical stress gives, with outward pair forces at K,

    F + sum_i mu_i n_i = 0,
    sum_i mu_i det(P_i,n_i) = 0,
    F = 2 sum_j lambda_j Z_j.

Each original pair has mu_i>0, an actual common application P_i, and an
actual separating unit normal n_i. Circle atoms retain lambda_j>=0 and
their actual boundary corners. Taking the center torque together with
the force equation gives the printed origin torque: each individual
circle atom is radial and has zero origin torque. This remains true
for either zero individual circle coefficient.

## 3. The nonparallel group bound uses actual neighbor occupancy

Let T be one actual common application, W the sum of all original
magnitudes in a nonempty group there, and G their exact vector sum.
Every original n_i supports K outward at T. If T is a side-interior
point, all these normals equal its outward side axis. If it is a vertex,
all lie in that vertex's closed outward quadrant. Projection on the
unit quadrant bisector gives

    |G| >= G.w >= W/sqrt(2) > 0.

Thus a nonempty group cannot vanish. Positivity of the coefficients also
gives the actual support inequality

    G.(X-T)<=0 for every X in K.

This establishes a support of the unchanged K, not the existence of a
new neighbor in direction G.

For each original actual neighbor L_i, its original T is a minimum-n_i
support point. At a vertex, resolve n_i in that neighbor's inward
orthonormal axes. Its coefficients are nonnegative and at most one;
therefore the actual point T+n_i belongs to L_i. At a side-interior
point the same statement is its full inward unit normal segment.
The vertex proof includes both side endpoints. Thus every T+n_i belongs
to the containing disk, with no boundary status needed at L_i.

Disk convexity gives the actual averaged disk point

    T+G/W in D_R.

Projection on n=G/|G| yields the uniform group bound

    T.n + |G|/W <= R,
    T.n <= R-1/sqrt(2).

It is legitimate even when the original normals in the group are
nonparallel. No claim that the averaged point belongs to a single
neighbor is needed. The proof uses only that all averaged points belong
to the same convex disk. The bound comes from original neighbor points,
not an unsupported width-one assertion for an artificial aggregate unit.

Finally

    R/sqrt(2) > R-1/sqrt(2)

is equivalent to R<1+sqrt(2), which holds strictly throughout the given
window. Hence any group support of height at least R/sqrt(2) is
impossible. This is the exact substitute used in every later outside-q
case.

Since all applications in the group really equal T, its exact origin
torque is det(T,G). There is no relocation of an original mean in this
identity.

## 4. The full single-application input

I independently checked the complete one-application theorem. For an
actual physical circle corner Z of K and the common actual application
P, the unit diameter gives

    2 P.Z >= |P|^2+R^2-2 > 0.

Summing with the unchanged nonnegative circle coefficients gives P.F>0.
The full torque and force equations give det(P,F)=0, so P=p e with
p>0 and e=F/|F|. The full positive sum of outward support inequalities
then gives e.X>=p on all of K. Thus P is the actual minimum-e support.

If e is not an own side axis, P is a unique vertex. Both coordinates
of P in its inward axes are strictly positive, so the actual farthest
corner is unique. Its alignment with F forces it to be

    Z=P+sqrt(2)e=R e,
    P=(R-sqrt(2))e.

Any actual boundary neighbor W containing P has a circle point Z_W.
The triangle inequality and its unit diameter give

    R=|Z_W|<=|P|+|Z_W-P|<=R.

Equality forces Z_W=Z and opposite vertices P,Z in W. Those opposite
vertices determine the same actual unit K, contradicting distinctness
and disjoint open interiors.

If e is an own axis, write K=[p,p+1] times [b,b+1], with P=(p,0)
and b in [-1,0]. A nonzero own transverse center coordinate would give
a unique physical circle corner with a nonzero transverse resultant,
contradicting F parallel to e. Hence b=-1/2, the two physical circle
coefficients are equal as a consequence of the equations, and

    K=[d,d+1] times [-1/2,1/2],
    P=(d,0), R^2=(d+1)^2+1/4.

Any distinct actual unit containing this side-interior P lies in x<=d.
For its circle corner Z_W,

    |Z_W-P|^2>=R^2-d^2=2d+5/4>2,

since R>3/2 gives d>sqrt(2)-1>3/8. This contradicts its unit diameter.
All side endpoints were allowed initially; the full circle resultant
then forced the midpoint. They were not deleted by assumption.

The boundary-neighbor premise of the new theorem therefore excludes
one application at the exact arbitrary-degree scope needed. P,Q are
distinct and both groups are nonempty.

## 5. Complete physical circle masks and all parallel cases

Choose actual side coordinates at a farthest physical circle corner so

    K=[a-1,a] times [b-1,b],
    a>=b>=1/2, a^2+b^2=R^2.

Comparison with adjacent corners gives the two lower coordinate bounds.
Another physical circle corner occurs exactly at one coordinate 1/2;
both cannot equal 1/2 in this radius window. Thus the full alternatives
are one physical circle corner, or the actual two-corner rectangle

    K=[d,d+1] times [-1/2,1/2],
    a=d+1=sqrt(R^2-1/4), d>9/10.

Every physical circle point is unshareable. If Z is an actual circle
corner, its two inward axes v satisfy Z.v<=-1/2 from containment of
Z+v. Thus -Z is strictly inside the inward quadrant and the short radial
inward segment at Z lies in the open square. Two squares sharing Z
would overlap there.

If G_P,G_Q are parallel, their nonzero sum -F puts their common axis
along F. In the one-corner case F is a positive multiple of (a,b).
A group in the positive direction would support at the unshareable
outer circle vertex. With that direction excluded, both groups point
in the negative direction and have the same unique inner support
vertex, contradicting distinct P,Q.

In the two-corner case write the full resultant as

    F=k(a,eta), k>0, -1/2<=eta<=1/2.

This retains both possible zero individual circle coefficients. If
eta is nonzero, a positive group direction again exposes one outer
circle corner, while two negative groups expose the same inner corner.
Thus eta!=0 is impossible in the parallel case.

For eta=0, an East group has height a>=R/sqrt(2), contradicting the
proved group bound. Both groups must be West, with actual applications
on x=d. Every original normal in each group is then also West. At an
inner-face side interior this is immediate; at either inner vertex,
all allowed normal y components have one common weak sign, and positive
coefficients cannot cancel that sign unless every y component is zero.
Their x directions are then West.

In particular the actual boundary neighbor from the theorem has its
original minimum-West contact at some (d,h), |h|<=1/2. The horizontal
case of C7 Lemma 2.1 applies to that real neighbor. For clarity, its
complete bound can be checked directly. If this point is a vertex of
the neighbor, label its inward axes as

    (sin theta,cos theta), (-cos theta,sin theta),
    -pi/2<=theta<=0.

All its corner x coordinates lie in [d-sqrt(2),d], a subset of [-d,d]
because d>9/10>1/sqrt(2). Its y coordinates lie in [h-1,h+1], a subset
of [-3/2,3/2]. Every corner therefore has squared norm at most

    d^2+9/4 < d^2+2d+5/4=R^2.

If the point is in a side interior, varying its original location along
that side reduces to the two endpoint placements, and squared-norm
convexity gives the same strict bound for every intermediate mean.
This contradicts the actual neighbor's physical boundary status. It
uses no load or force equation at that neighbor.

This completes the entire parallel cover. The group lines are genuinely
nonparallel and have a unique intersection q.

## 6. Full torque gives the radial line of concurrence

The exact common-point torque is

    det(P,G_P)+det(Q,G_Q)=0.

Since q lies on both group lines, det(P-q,G_P)=det(Q-q,G_Q)=0.
Consequently

    0=det(q,G_P+G_Q)=-det(q,F).

Thus q lies on the line of F. This is a consequence of every original
force and torque term. It is not torque equilibrium at a substituted
two-force body. The sign of the radial scalar remains to be proved by
the physical normal-line cover below.

## 7. One physical circle corner: every outside-concurrence case

Use the rectangle above and write q=tau(a,b). We have a>1 and
b<3/2 throughout the radius window. If

    1-1/a <= tau <= 1,

then q belongs to K: its x coordinate is in [a-1,a] and
b*tau>=b-b/a>=b-1. The lower scalar endpoint is strictly positive.

I checked the complete complement using the closed normal cones of the
four rectangle vertices and side-interior normal lines. If tau>1, q is
strictly above and right of K. Only the outer and opposite inner vertices
can have supporting normal lines through q. The outer one cannot be an
application, so two distinct applications are impossible.

If tau<1-1/a, then q_x<a-1 and q_y<b. If q_y<b-1, only the same outer
and opposite inner vertices remain. At q_y=b-1, the additional lower
right vertex can have only horizontal East normal, of height a. That
height is at least R/sqrt(2), so the group bound excludes it.

The remaining domain is q_x<a-1 and b-1<q_y<b. Its non-circle
normal-line possibilities are exactly the left-side point (a-1,q_y),
the right-side horizontal-normal point, and the lower-right vertex
p=(a,b-1). The right-side point again has forbidden height a. Thus
two distinct applications would require the lower-right vertex.

At this vertex the actual group normal has the form

    n=(cos eta,-sin eta),
    0<=tan eta=(b*tau-b+1)/(a*(1-tau))<(a-b)/a.

The ratio increases in tau, with derivative 1/[a(1-tau)^2], and its
limit at tau=1-1/a is (a-b)/a. This proves the complete enlarged
closed comparison interval, including the empty strict case a=b.

The support function

    f(eta)=a cos eta-(b-1)sin eta

is positive on that interval. If b<=1 this is immediate; if b>1,
a>1, b-1<1/2 and tan eta<1 give the same strict positivity. Therefore
f''=-f<0, and the minimum is at an endpoint. At zero it is a>=R/sqrt(2).
At the other endpoint put e=a-b>=0 and

    N=a^2+e(1-b), D^2=a^2+e^2.

The endpoint is N/D, with N>0. Independent expansion gives

    2N^2-R^2 D^2
      =e[2b^2(2-b)+e(2+4b-3b^2)+e^2(4-2b)].

All bracket coefficients are positive on 1/2<=b<3/2. For the middle
coefficient, its concavity and its positive endpoint values 13/4 and
5/4 suffice. Thus N/D>=R/sqrt(2), including e=0. The actual group
height is at least that value, contradicting Section 3's bound.

No outside-q case survives. Hence q belongs to K and is a positive
multiple of F. At either original group application T, q lies on its
normal line and in K's supporting half-plane. The vector T-q is
therefore a nonnegative multiple of the actual group direction. This
includes q=T and ell_T=0 and proves the required two rays.

## 8. Two physical circle corners: positive scalar and every exterior ray

Use K=[d,a] times [-1/2,1/2], a=d+1, and
F=k(a,eta), |eta|<=1/2. Write q=tau(a,eta).

First suppose tau<d/a. Then q_x<d. For |q_y|<1/2 the normal-line
classification leaves exactly one non-circle inner-face point, apart
from outer circle vertices and an East outer-face normal. The circle
vertices are unshareable and the East height a is forbidden. At
q_y=+/-1/2 the surviving inner-face point is its endpoint; no second
application is created. For q_y above or below that interval, only
one corresponding inner vertex and an outer circle vertex can occur.
These cases all contradict the distinct application points. Therefore

    tau>=d/a>0.

For d/a<=tau<=1, q belongs to K and the supporting-half-plane argument
proves both proper rays directly. All coefficient endpoints are included.

If tau>1, then q_x>a. When |q_y|>1/2, only one non-circle inner vertex
can have a normal line through q: the lower inner one for q_y>1/2,
or the upper inner one for q_y<-1/2. The other possible vertex is a
physical circle corner. Thus two distinct applications are impossible.

The remaining exterior case has q_x>a and |q_y|<=1/2. Its possible
non-circle applications, after excluding the East outer-face height,
are all on the inner face x=d, including its two endpoints. For any
such actual T, the vector T-q points strictly left and lies on the
line of its group normal. The sign agrees with the actual outward
support cone: West at a side-interior point, Northwest at the upper
vertex, Southwest at the lower vertex. Hence

    T-q=ell_T G_T/|G_T|, ell_T>0.

This remains valid at q_y=+/-1/2, where an endpoint group can be
horizontal. Since tau>0 and k>0, q is still a positive multiple of
the complete original F. This proves exactly the exterior-q conclusion
claimed, without asserting q belongs to K in this case.

The proof has retained the entire physical two-corner mask, including
eta=0, eta=+/-1/2, unequal circle weights and either zero individual
weight. It has not imposed the equal-weight leaf condition.

## 9. Scope conclusions and preserved interfaces

The source proves the full arbitrary-degree two-application properness
statement. The new aggregate height bound supplies the geometric control
that an unsupported substitution of a higher-degree star by two physical
forces would lack. Every later scalar contradiction uses that weaker,
actually proved bound, and its strict reserve is sufficient.

At an H4 loaded C3 coincidence, the theorem is available only after the
caller proves literal CD/CH application equality. If HC is a positive
shared side with its original mean elsewhere, there can be three distinct
applications and this theorem alone says nothing about that feature.
All C3 forces, the actual CB boundary neighbor, other square forces,
circle masks, individual zero coefficients and all nine units remain.

This review approves the generic theorem and its printed conditional
interface only. It assigns no original fine/coarse closure credit and
does not edit the source, earlier reviews, metadata or original arrays.
No numerical pose search, angle mesh, normal selection, mean replacement,
Lean compilation, CI, workflow, commit or remote operation was used.
