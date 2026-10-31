# A radial opposite boundary tip supplies the last original cycle side owner

Date: October 27, 2026.

**Status: complete compatible necessary-domain selection theorem, submitted
for full root and separate independent review.** This is not an exclusion
of the remaining mixed mask by itself. Its conclusion is only that every
actual cycle edge has an actual side-axis owner in the common selected
certificate.

Keep the original high adjacent-S component

    AB,BC,CD,DA,AL,BM,
    A3,B3,C2,D2,L1,M1,
    d=1+epsilon, 0<epsilon<1/60,
    R^2=(d+1)^2+1/4<=1105/256.

All nine physical squares and every original force, circle weight and
application mean remain. Suppose the actual AB normal is owned by A
alone, C has one physical circle corner and D has two physical circle
corners. Thus D is the actual radial S square in its own direction,
and every actual point of D has norm at least d. Both its original
corner weights, including either individual zero, remain.

The complete necessary-domain source
ADJACENT_S_LEAF_C4_ONE_OWNER_ALL_MASK_LEAF_REDUCTION.md gives A's
strict outer lower genuine leaf, and the complete source
ADJACENT_S_C4_ONE_OWNER_OUTER_CONTACT_SIDE_OWNERS.md supplies actual
owners of AD and BC. The radial-boundary theorem already makes AD
A-owned North. We prove that CD also has a side-axis owner.

The new finite choices are made on the fixed physical pose before
multiplier extraction, simultaneously with those earlier compatible
choices. No normal or shared-side mean is reselected in an obtained
certificate.

## 1. A true clear root fixes its actual mean once its two normals are fixed

The actual AB point P is a fixed physical vertex of B, because B does
not own the AB normal. The AB unit normal E is a fixed A own axis.
Let e be the fixed direction of B's actual genuine S leaf.

The full one-owner leaf reduction gives det(e,E)!=0 in both surviving
B leaf types. In the chart E=East, the strict lower adjacent leaf has
vertical component -(U*c+w*s)<0, and the owned far-axis leaf has
vertical component -c<0. All of c,s,U are strictly positive.
No zero vertical endpoint is silently omitted.

Let m be any proposed actual BC normal which has a side owner at B
or C. At a fixed physical pose there are finitely many such axes.
Keep the full B3 equation, with its actual positive magnitudes:

    -mu*E+nu*m+beta*e=0,       mu,nu,beta>0.             (1)

If det(m,E)=0, equation (1) contradicts det(e,E)!=0, so this
candidate cannot occur in a positive certificate. Otherwise (1)
fixes both ratios nu/beta and mu/beta from the pose:

    nu/beta=-det(e,E)/det(m,E),
    mu/beta=(nu/beta)*(m.E)+e.E.                         (2)

A candidate with either ratio nonpositive is likewise impossible and
may be discarded from the necessary-domain list.

The genuine leaf has zero origin moment. The actual B3 moment equation
therefore gives

    nu*det(P_BC,m)=mu*det(P,E).                          (3)

The actual BC mean also lies on B's fixed supporting line

    m.P_BC=h_B(m).

Equations (2)--(3) determine that original mean uniquely:

    P_BC=h_B(m)*m-T*Jm,
    T=(mu/nu)*det(P,E).                                 (4)

Here J is positive quarter-turn; det(P_BC,m)=-P_BC.Jm.
If the point in (4) is outside the actual physical contact segment,
that candidate is impossible. Otherwise (4) is only a necessary
formula for its actual mean. It is not an imposed endpoint, midpoint
or new application.

This proof is valid for a shared side with an arbitrary original
weighted mean: the full equations themselves determine its value
once the two actual normal directions have been fixed. A singleton
contact is included as the corresponding fixed physical point.

## 2. The real unique-corner tip now has a fixed radial intersection

Let Z be C's one physical circle corner. Its actual full circle
resultant is a positive scalar multiple of the fixed vector Z.
Its other actual neighbor D is physical boundary, so the genuine
boundary-neighbor degree-two lemma applies.

The original BC normal line cannot be parallel to Z. Indeed, if m
were parallel to Z, the full C2 translation equation would also make
the CD normal parallel to m. That contradicts the same lemma's
nonparallel-pair conclusion. This argument retains the whole C2
equation and does not require either neighbor root to have degree two.

Consequently the line

    P_BC+R*m

and the radial line R*Z meet at one pose-fixed point q. Under the
actual positive certificate that point is the genuine C2 concurrence;
in particular q=lambda*Z with lambda>0. Its construction involves
only the fixed physical pose, the fixed AB point and axis, and the
proposed owned BC axis. It is independent of the original CD point
normal.

The original C2 torque equation requires the actual CD normal line
to pass through this same q. We next verify the only possible
zero-vector exception to using that restriction.

## 3. No actual radial-D vertex contact can equal the positive radial intersection

Suppose CD were free point-only vertex/vertex, at its fixed physical
point Q. Then Q is a non-circle vertex of C and belongs to the actual
radial square D. We claim that Q cannot be a positive multiple of Z.

Write the whole actual unique-corner square as

    C=Z+[0,1]u+[0,1]v,
    |u|=|v|=1, u.v=0.

Containment and the unique physical circle mask give

    Z.u<-1/2,       Z.v<-1/2.                           (5)

An adjacent vertex Z+u cannot be parallel to Z: that would make
Z parallel to u and hence Z.v=0, contrary to (5). The same argument
applies to Z+v.

If the opposite vertex Z+u+v were lambda*Z with lambda>0, then

    u+v=(lambda-1)*Z.

Taking the dot product with Z and using (5) gives lambda<1;
taking lengths gives

    |Q|=R-sqrt(2).

But every actual point of D has norm at least d>1, whereas

    R-sqrt(2)<25/12-7/5=41/60<1.

Thus this opposite-vertex alternative is impossible as well. The
circle corner Z itself is not an actual inter-body contact.

Therefore every physical free CD vertex in this mixed mask differs
from the positive radial point q of Section 2:

    q-Q!=0.                                             (6)

This uses the actual physical radial D mask, not a statement that
one of two circle weights is zero.

## 4. A finite pose-based prelist excludes a free CD normal

At the fixed original pose prelist every ordered candidate of the six
distinct actual bodies and genuine leaves, every actual own axis E of
A, every actual B vertex P compatible with sole-A ownership of AB,
and every proposed owned BC axis m of B or C.

For each candidate apply the explicit guards from Sections 1--2:

- det(e,E) must be nonzero;
- det(m,E) must be nonzero;
- both ratios in (2) must be positive;
- the point (4) must lie in the original physical BC contact;
- m must be nonparallel to the unique actual circle vector Z;
- the resulting q must be a positive multiple of Z.

A candidate failing a guard cannot be the stated actual positive
component. For every retained candidate and each possible physical
free CD vertex Q, Section 3 gives q-Q!=0. The necessary original
CD normal n would satisfy

    det(n,q-Q)=0.                                       (7)

This excludes at most two directions of its open admissible angular
interval. Require (7) to be nonzero in the original finite normal
preselection instead.

These requirements are compatible. Their coefficients are fixed
pose data after the finite owned-axis choices; no shared-side mean
parameter is being varied with n. The matched four-junction convention
couples only disjoint opposite free pairs. A candidate using both such
pairs positively is already excluded by the common uncrossed
certificate. Every other incident owned side axis is fixed. Thus the
CD free parameter can vary over its open permitted interval while
the data in (2)--(6) remain fixed. If an unused opposite pair at the
same junction shares the parameter, varying it too does not alter
those fixed data.

There are finitely many candidates and forbidden directions. Their
dense open complements can be chosen together with all preceding
strict, nonradial, singleton and cycle-owner conditions, before
extraction. Original uncrossing and subsequent thinning preserve
surviving point normals; any added shared-side endpoint atoms already
have the fixed owned axes present in the prelist. Minimum-positive-
original-atom selection can be made in this same compatible class.

If a component in the declared mixed domain survived with a free
CD normal, its actual BC owner, full positive ratios and actual mean
would occur in this prelist by Sections 1--2. Its original torque
equation would force (7) to vanish, contradicting the chosen condition.
Therefore CD has an actual side-axis owner.

## 5. Exact conclusion and retained cases

AB is the original sole-A-owned axis. AD and BC have their already
established actual owners, with AD North in the present radial-D
placement. Section 4 supplies an owner of CD. Thus every original
cycle edge has a side-axis owner in this entire necessary domain.

No particular owner of CD is chosen, and every possible owned-side
mean remains the one from the original certificate. The full radial
D2 circle resultant and both individual D weights remain unchanged.
No all-cycle fixed-external determinant is applied to this two-corner
mask. This theorem does not assert that the remaining geometric
interface is impossible; it gives the exact finite physical owner
cover for its subsequent proof.

No numerical pose, normal reselection after extraction, fixed false
mean, degree deletion, compilation, CI, remote mutation or shared
metadata edit is used.
