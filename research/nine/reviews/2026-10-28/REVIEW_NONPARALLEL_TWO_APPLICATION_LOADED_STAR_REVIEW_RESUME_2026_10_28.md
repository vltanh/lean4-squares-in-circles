# Independent full review of nonparallel two-application proper concurrence

Date: October 28, 2026 UTC. Reviewer: review_resume.

**Verdict: PASS for the complete arbitrary-degree theorem on
sqrt(2)<R<1+sqrt(2).** A loaded square with exactly two distinct actual
pair-force applications and nonparallel exact full group sums has the
stated positive proper concurrence. No physical boundary neighbor is
needed. Every real neighboring square, original force and mean, and full
physical circle mask remains. This is a uniform implication; it does not
exclude an entire original graph/load family.

## 1. Frozen identity and independent review boundary

Reviewed source:

    NONPARALLEL_TWO_APPLICATION_LOADED_STAR_HAS_PROPER_CONCURRENCE.md
    bytes: 14124
    SHA256: 4aeba77a0f964597a40ce290f4a0f9d6d7dc802f83a024f3497cfdb6bb97359d
    Git blob: 731ca21d9ef23953baf1e80f721b464a7e8d93fa

I read and rederived the entire frozen proof. I also read the entire
direct antecedent LOADED_TWO_APPLICATION_FULL_STAR_PROPER_CONCURRENCE.md
at its current 942ed38a identity. The original physical-stress source and
its conventions had been read in full during this continuation; their
exact current pin was checked again. Both direct source pins match.

This reviewer supplied no discovery to the theorem. In particular the
removal of the boundary-neighbor premise, the arbitrary-degree group
bound and the enlarged radius argument are the author's proposed scope,
which is audited here independently. I checked every rectangle position,
the full two-circle exterior case, the polynomial identity and all
strict/weak endpoint uses. Only this new independent review is written;
the source and all older records remain unchanged.

The conclusion is conditional on the printed complete original force,
torque and support equations. This review does not claim a new proof of
global multiplier existence. No generic normal selection is needed by
the local theorem itself, and no earlier one-application or parallel
exit is imported into it.

## 2. Exact original premise and the two full algebraic groups

The loaded square K and each real positive pair neighbor are actual
contained unit squares with disjoint open interiors in the same disk.
The original system is

    F + sum_i mu_i n_i = 0,
    sum_i mu_i det(P_i,n_i) = 0,
    F = 2 sum_j lambda_j Z_j,
    mu_i>0, lambda_j>=0, sum_j lambda_j>0, |Z_j|=R.

Every actual application P_i belongs to the two-point set {P,Q}, both
points occur, and P!=Q. Each original mean remains exactly its own
physical point. The exact full sums G_P,G_Q are assumed nonparallel.
They include all original forces at their respective points, even if
individual normals within a group are nonparallel.

These are essential entry hypotheses. The theorem does not infer them
from the mere existence of a loaded body, from its degree, or from two
convenient selected forces. It does not move a shared-side mean to make
applications coincide. No circle-boundary property of any neighbor is
assumed, either positively loaded or zero-weight physical boundary.

The grouping is only an exact algebraic identity. It neither changes
the true degree of K nor invents a neighboring unit for G_P or G_Q.
The proof supplies the support bound for those sums directly from all
the real neighbors, which is the key requirement for this export.

## 3. Complete real-neighbor reach bound for every group

At any one actual support point T of K, all its outward normals lie in
the same closed vertex quadrant, or coincide with the side normal when
T lies in a side's relative interior. For the group total weight W and
exact vector sum G, dotting with that quadrant's unit bisector gives

    |G| >= W/sqrt(2) > 0.

In the side-interior case the stronger equality |G|=W holds. Positive
linearity of the actual supporting inequalities also gives

    G.(X-T)<=0 for every X in K.

Thus the exact group is nonzero and is an actual supporting direction
of K at the original T. This argument includes the axis endpoints of
a vertex cone and all original positive coefficient ratios.

For each actual neighboring square L_i, T is a minimum-n_i support.
At its vertex, the unit n_i has two nonnegative components, each at
most one, in the two inward orthonormal axes. Therefore T+n_i lies in
that same real square. At a side-interior support, n_i is precisely the
inward side normal and the entire unit normal segment stays inside.
A side endpoint belongs to the vertex calculation. Hence every
unchanged real neighbor supplies T+n_i in the actual disk.

Disk convexity then gives T+G/W in D_R. Projection along the exact
unit group direction n=G/|G| yields

    T.n <= R-|G|/W <= R-1/sqrt(2).

No force equation at a neighbor, no boundary neighbor and no auxiliary
comparison square enters this step. It is valid for an arbitrary number
of original positive normals at the actual common point.

The strict upper-radius assumption is used exactly in

    R/sqrt(2) > R-1/sqrt(2),

which is equivalent to R<1+sqrt(2). Consequently any actual group with
support height at least R/sqrt(2) is impossible, including equality in
that lower bound. This strict reserve justifies later use of enlarged
closed angular intervals.

Because the original applications in a group literally coincide, its
moment is exactly det(T,G). The full original equations therefore give

    F+G_P+G_Q=0,
    det(P,G_P)+det(Q,G_Q)=0.

No original circle force or pair force is omitted in either identity.

## 4. Complete physical circle mask and radial concurrence line

Choose actual own axes at a physical farthest corner and order them so
Z=(a,b), a>=b. Comparing its norm with each adjacent corner gives
b>=1/2 and a>=1/2; containment and contact give a^2+b^2=R^2 and

    K=[a-1,a] times [b-1,b].

Since R>sqrt(2),

    a>=R/sqrt(2)>1,
    1/2<=b<=R/sqrt(2)<1+1/sqrt(2)<2.

Another corner has the same norm exactly when the corresponding
coordinate is 1/2. Since a>1, the complete masks are one physical
circle corner for b>1/2, and exactly two for b=1/2. The latter entire
pose is

    K=[d,a] times [-1/2,1/2],
    a=sqrt(R^2-1/4), d=a-1>0.

A physical circle point cannot be shared by two contained units. It
must be a vertex of any contained square containing it, by strict
convexity of the disk. Each actual inward unit side vector v satisfies
Z.v<=-1/2. Hence -Z is strictly inside the inward quadrant, and the
same short point Z-epsilon Z belongs to both proposed open interiors,
contrary to physical interior disjointness. This excludes such a point
as an actual pair application, independently of any multiplier at the
corner.

With one physical circle corner, F is a positive scalar multiple of
(a,b). With two, the full original nonnegative weights give

    F=k(a,eta), k>0, |eta|<=1/2.

Both endpoints eta=+/-1/2 and eta=0 are retained. The first component
is positive, so F is nonzero for every allowed circle coefficient split.

Nonparallel G_P,G_Q have one actual line intersection q. Translating
the exact moment equation to q gives det(q,F)=0, so q is a real scalar
multiple of the relevant displayed circle-resultant direction. The
positive sign of that scalar is still to be proved; it is not smuggled
into the definition of concurrence.

## 5. One physical circle corner: all exterior positions are impossible

Write q=tau(a,b). The interval

    1-1/a <= tau <= 1

places q in K. Its x coordinate is in the actual x interval and its
y coordinate is at least b-b/a>=b-1, because b<=a. Its lower endpoint
is strictly positive by a>1. I independently checked the complement
of this interval using the full closed normal cones.

### 5.1. Above/right and below/left diagonal positions

If tau>1, q is strictly above and right of K. Only the outer physical
circle corner and the opposite inner corner can have a supporting
normal line through q; neither side interior nor either mixed corner
can. The circle corner is not an application, leaving only one point,
contrary to P!=Q.

If tau<1-1/a, q_x<a-1 and q_y<b. When q_y<b-1, the same complete
normal-cone check leaves only those two opposite corners. If q_y=b-1,
the lower-right corner is additionally possible with its East normal.
That normal has actual height a>=R/sqrt(2), forbidden by the full
group reach bound. The actual left lower endpoint remains just one
other point. Thus both the strict and equality lower rows are excluded.

### 5.2. Left of the rectangle with intermediate height

The sole remaining exterior range is

    q_x<a-1, b-1<q_y<b.

The complete support-line possibilities other than the physical circle
corner are the actual left-side point (a-1,q_y), a right-side point
with East normal, and p=(a,b-1), the lower-right vertex. The right-side
axis has the forbidden height a. Therefore two distinct applications
require a group at p. Its outward unit group normal is southeast,

    n=(cos theta,-sin theta),
    0<=tan theta=(b tau-b+1)/(a(1-tau))<(a-b)/a.

The numerator is positive in this strict row; including zero only
enlarges the range. The upper bound follows by evaluating the increasing
fraction at tau=1-1/a, where it equals (a-b)/a. If a=b the proposed
strict interval is already empty; the enlarged endpoint proof below
also covers that equality.

### 5.3. Complete continuous support comparison and enlarged radius

Put e=a-b>=0. On the enlarged closed interval
0<=tan theta<=e/a, consider

    f(theta)=a cos theta-(b-1) sin theta.

This quantity is positive throughout. For b<=1 this is immediate; for
b>=1 its numerator after division by cos theta is bounded below by
a-(b-1)e/a>0. The latter follows from
a^2-(b-1)e=a^2-ab+b^2+e>0. Hence f''=-f<0: its minimum on the
whole interval is at an endpoint.

At zero the value a is at least R/sqrt(2). At the other endpoint put

    N=a^2+e(1-b), D^2=a^2+e^2.

The value is N/D and N>0. I independently expanded the exact identity

    2 N^2 - R^2 D^2
      = e [2 b^2(2-b)
             + e(2+4b-3b^2) + e^2(4-2b)].

For b in [1/2,1+1/sqrt(2)], the first and last displayed coefficients
are positive because this whole interval lies below 2. The middle
coefficient is a concave quadratic. Its endpoint values are exactly
13/4 and 3/2-sqrt(2), and the latter is strictly positive because
(3/2)^2-2=1/4>0. Thus every bracketed coefficient is positive on the
entire enlarged b range, including both closed endpoints.

The identity is nonnegative also at e=0. Squaring only positive
quantities gives N/D>=R/sqrt(2), and concavity gives this bound for
every actual theta. Consequently the actual full group at p would
have height at least R/sqrt(2), contradicting Section 3's strict reach
comparison. There is no angular sampling, omitted coefficient endpoint
or hidden old b<3/2 restriction in this argument.

All exterior tau ranges are now excluded. Therefore q lies in K and
is a positive scalar multiple of F. For either actual group point T,
q lies on its normal line and in K's original support half-plane at
T. The vector T-q is consequently a nonnegative multiple of G_T/|G_T|.
The possibility q=T gives the allowed zero length. This proves both
full proper-ray statements for the entire one-circle-corner mask.

## 6. Two physical circle corners: positive radial sign and every exterior ray

Use K=[d,a] times [-1/2,1/2] and q=tau(a,eta), |eta|<=1/2.
I checked the following full normal-cone classification, without
assuming eta is positive or either circle coefficient is nonzero.

### 6.1. All left-of-inner-face positions are impossible

Suppose tau<d/a, so q_x<d. If |q_y|<1/2, only the actual inner-face
point (d,q_y), outer circle corners, or an outer-face East normal can
have the required support line. The outer corners cannot be physical
pair applications and the East height a>=R/sqrt(2) is forbidden.
Thus only one actual application point remains.

At q_y=+/-1/2 the inner-face point is its endpoint; the same exclusions
leave only that one point. If q_y is strictly above or below the strip,
the closed vertex cones permit only one respective inner corner and
an outer physical circle corner. Those rows again have at most one
actual non-circle application. No top/bottom side-interior normal line
has x coordinate q_x<d. Every possibility contradicts the two distinct
original points.

Therefore tau>=d/a>0. This proves the required positive radial sign
before any interior/exterior properness conclusion.

### 6.2. Interior concurrence and the whole right exterior domain

For d/a<=tau<=1, q is in K because its first coordinate is in [d,a]
and |q_y|<=1/2. The same actual support half-plane argument as above
gives both nonnegative proper-ray coefficients, including zero length.

For tau>1, q_x>a. If q_y>1/2, the only non-circle supporting corner
available is the lower inner corner; if q_y<-1/2, it is the upper
inner corner. The other diagonal candidate is an unshareable outer
physical circle corner. These positions cannot supply the two distinct
actual applications.

The entire possible exterior domain is therefore

    q_x>a, |q_y|<=1/2.

Every remaining non-circle supporting contact is on the actual inner
face x=d, including either endpoint, except a forbidden outer-face
East-normal contact. At an inner-face application T, the vector T-q
points strictly left. At an interior point its line is horizontal and
it has the outward West sign. At the upper endpoint its vertical
component is nonnegative, so it belongs to the outward northwest cone;
at the lower endpoint it is nonpositive, so it belongs to the outward
southwest cone. Since it is already parallel to the actual group
normal, its sign is the proper one. Thus

    T-q=ell_T G_T/|G_T|, ell_T>0.

This explicitly includes q_y=+/-1/2, where an endpoint vector can be
horizontal. The previously proved tau>0 gives q=tF with t>0 because
the circle-resultant scale k is positive. The theorem correctly does
not assert q in K in this exterior two-corner domain.

These cases cover every eta and every original individual zero circle
weight. No symmetry of the two weights, chosen physical corner or
restricted mean is used to obtain properness.

## 7. Larger radius interval and exact caller obligations

The complete new radius range is justified within this proof:

* R>sqrt(2) makes a>1, so 1-1/a and d/a are strictly positive;
  it also gives the complete one/two physical circle-mask dichotomy.
* R<1+sqrt(2) is exactly the strict comparison between the group reach
  ceiling and R/sqrt(2).
* The same upper bound gives b<1+1/sqrt(2), which makes the expanded
  support polynomial nonnegative throughout its whole required range.

No radius-dependent lemma from the older boundary-neighbor theorem is
used. The usual original interval is strictly contained in this larger
one: (79/40)^2-2=3041/1600>0, while
(21/10)^2-1105/256=599/6400>0 and 21/10<1+sqrt(2).
These strict comparisons include both original interval endpoints.

For a genuine loaded E2, the theorem applies once the caller proves
that its two original applications differ and its two original normals
are nonparallel. Neither neighbor needs to be boundary. For higher
degree the caller must prove exactly two literal application groups
and nonparallelness of their full sums. Individual nonparallel normals
within a group are permitted and were retained in the actual-neighbor
reach argument.

The source does not close a one-application case or a parallel case.
Its antecedent needed a boundary neighbor for those additional exits;
this proof does not invoke them or claim they became unnecessary in
their own domains. In particular no entire H4_D0.L124 family follows
until a separate caller establishes all required entries and supplies
its actual geometric contradiction.

## 8. Exact pins, algebra verification and preservation

Both direct current mathematical sources match exactly:

| Direct source | SHA256 |
| --- | --- |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 |
| LOADED_TWO_APPLICATION_FULL_STAR_PROPER_CONCURRENCE.md | 942ed38a7452f35e95839cc79ea15ed97091114495e9a3ab9c232ae8255a0ea0 |

The polynomial expansion was checked by hand and by exact integer
coefficient arithmetic in the two indeterminates b,e: subtracting the
printed right-hand side from 2N^2-R^2D^2 gives the zero polynomial.
The two middle-coefficient endpoint values and radius reserves above
were also checked with exact rational arithmetic, including the exact
pair representation of 3/2-sqrt(2). These are algebraic identity checks,
not a sampled geometric exclusion or a computational certificate.

The frozen source's full identity at the end of review remains 14124
bytes, SHA256 4aeba77a0f964597a40ce290f4a0f9d6d7dc802f83a024f3497cfdb6bb97359d.
No original normal, application, mean, neighbor, circle mask, force or
true degree was changed. No source, older review, original gate, ledger,
Lean file, build, CI, workflow, commit or remote state was modified.
Root acceptance and any future original-family application remain
separate from this complete uniform-theorem PASS.
