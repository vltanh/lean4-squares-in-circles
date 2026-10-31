# Proper concurrence for a full loaded star with two force directions

Date: October 28, 2026 UTC. Author: frontier_audit continuation.

**Status: complete proposed general full-star hand theorem, with literal
higher-degree applications, frozen for full root and separate independent
review. No original gate or metadata is changed.**

This theorem groups parallel forces with the same orientation while keeping
their complete force and moment. It does not change a body's true degree,
discard any positive force, or assert that a grouped application is a
contact with a new unit. In particular its conclusions concern the two
grouped force lines, not every individual line in a group.

## 1. Full original hypotheses and exact export

Retain the original circle origin O=0, the actual interior-disjoint unit
squares in its disk, and

    79/40<=R<=sqrt(1105)/16.

Let K be an actual loaded unit. Keep its entire positive pair-force star:
for every original positive neighbor i, its force is mu_i*n_i at its actual
common application or shared-side mean P_i, with mu_i>0 and n_i the unit
outward normal from K into that actual neighbor. Let

    F=sum_j lambda_j*z_j, lambda_j>=0,

be the full nonzero outward circle force, with any common positive factor
absorbed into the coefficients. Every physical circle mask and zero
individual circle coefficient is retained. The full original equations are

    sum_i mu_i*n_i+F=0,
    sum_i mu_i*det(P_i,n_i)=0.                              (1)

Assume all positive pair normals belong to at most two oriented directions.
Also assume at least one of those actual positive neighbors physically
touches the containing circle. Its own load and degree are unrestricted.

**Theorem.** There must be exactly two nonparallel oriented directions
n_1,n_2. For each direction define its actual full group

    M_j=sum_{i:n_i=n_j} mu_i>0,
    Q_j=(1/M_j)*sum_{i:n_i=n_j} mu_i*P_i.                    (2)

The lines Q_j+R*n_j meet at a point q satisfying

    q=t*F for some t>0,
    Q_j-q=ell_j*n_j, ell_j>=0, j=1,2.                      (3)

If K has one physical circle corner, q belongs to K. If it has two
physical circle corners, no assertion q in K is made. Formula (3)
remains valid for the entire two-corner weight interval.

For every original individual application in group j, one also has the
scalar support relation

    n_j.(P_i-q)=ell_j>=0.                                  (4)

No vector identity P_i-q=ell_i*n_j is asserted unless it follows from
that individual point itself. Different original lines in one parallel
group may be distinct. Every original neighbor and every physical contact
remains; a grouped point Q_j need not belong to any single neighbor.

## 2. Exact aggregation and its retained physical witnesses

Every P_i in group j is on the same actual maximum-n_j support face of K.
Convexity therefore keeps Q_j on that face. The equalities

    sum_{i in j} mu_i*n_i=M_j*n_j,
    sum_{i in j} mu_i*det(P_i,n_i)=M_j*det(Q_j,n_j)           (5)

are exact. In particular the shared tangential positions are averaged
with their original positive magnitudes; none is selected or replaced in
an individual equation.

Two physical facts remain available for each group.

First, no Q_j is a containing-circle point. Such a point of a contained
unit square is an extreme corner. If a positive convex average of the
P_i equaled that corner, every P_i in the group would equal it. But a
circle point cannot be shared by two actual squares: at that point z,
each inward side axis r obeys z.r<=-1/2, so the same sufficiently short
segment in direction -z enters the open interiors of both squares.
That would contradict their physical interior disjointness.

Second, the actual support value satisfies

    h_K(n_j)<=R-1.                                        (6)

Indeed choose any original neighbor in group j. It is a real unit on
the far side of the common support line h_K(n_j), has width at least
one along n_j, and is contained in the same disk. Its maximum projection
is at least h_K(n_j)+1 and at most R. This proves (6) using an actual
neighbor, without manufacturing a unit at the averaged point Q_j.

The normal-line arguments below use only the actual support face of
Q_j, its non-circle property and (6). Thus these properties are exactly
the physical hypotheses that must be retained when the original degree
is greater than two.

## 3. All parallel alternatives are impossible

The normalized full circle-corner average has norm at least
T=sqrt(R^2-1/4)>sqrt(2). A physical circle mask is either one corner
or two adjacent corners, as follows by comparing all four own-frame
corner radii. In the latter case use the actual radial rectangle

    K=[d,d+1] times [-1/2,1/2],
    d=T-1>9/10,

and its normalized circle average is (d+1,b), |b|<=1/2.

### 3.1. Oppositely oriented parallel groups

If the two groups have opposite directions, (1) makes their common
axis parallel to F. The nonzero F implies that one positive group points
in the outward direction of F. In the unique-corner mask that direction
supports K at its circle corner, impossible by Section 2. In the radial
rectangle, a nonzero b selects one of its outer circle corners and is
equally impossible. If b=0, the outward horizontal support is d+1>R-1,
contrary to (6). Thus opposite directions cannot occur.

### 3.2. A single oriented direction

If all original pair forces have one common direction, group the whole
star in (5). The full force and torque make its average application a
positive radial point on the circle-resultant axis. Positivity follows
directly: it and the normalized circle average belong to K, whereas a
nonpositive radial multiple would be at least T>sqrt(2) away from that
average, exceeding the actual unit diameter.

The complete full-star radial calculation then gives exactly the S or D
geometry. To see this without a degree assumption, if only one circle
atom is positive, the opposite support is the opposite vertex. The two
vertices and the radiality force a radial diagonal square with

    Q=(R-sqrt(2))*e,

and its circle corner is R*e. If both adjacent circle atoms are positive,
the weighted tangent component of their average must vanish: otherwise
the opposite inner corner has the opposite tangent sign and cannot be
a positive radial multiple. The square is therefore radial S, its
average is (d,0), and every original contact is on its real inner face
x=d with common outward normal West. This is the full-star argument of
Lemma N.4 in the parallel-transmission source, not a leaf assumption.

In the D case every actual positive neighbor contains the same inner
vertex Q. A boundary neighbor with a circle corner z' would satisfy
sqrt(2)>=|z'-Q|>=R-|Q|=sqrt(2). Equality forces z'=R*e, which is already
K's circle corner and cannot be shared. Thus the required actual boundary
neighbor is impossible.

In the S case consider its actual positive boundary neighbor at any
P=(d,h), |h|<=1/2. This real unit lies in x<=d. Every point of it has
x in [d-sqrt(2),d] subset [-d,d]. Its vertical displacement from P
has absolute value at most one: at a vertex support its two orthogonal
inward axes lie in the left half-plane and have opposite vertical signs;
at a side support the original tangent interval has length one. Thus
all its corners have squared radius at most

    d^2+9/4 < d^2+2*d+5/4 = R^2,

since d>9/10. It cannot physically touch the circle. The whole original
inner-face mean interval is covered. This excludes the last parallel
alternative.

Consequently the original full star has exactly two nonparallel groups.

## 4. Their intersection is radial, and coincident means are harmless

Let q be the intersection of the two nonparallel lines through Q_1,Q_2.
Taking the full moment about q, or subtracting det(q,(1)'s force
equation) from (1)'s moment equation, gives det(q,F)=0. Thus q is
a real scalar multiple of the normalized circle-corner average.

If Q_1=Q_2, then q is that actual point of K. It is a positive multiple
of F by the diameter argument in Section 3.2, and (3) holds with both
lengths zero. This case does not require a prohibition on three-square
incidence, or a choice of a different contact point.

We may therefore assume Q_1,Q_2 distinct for the remaining rectangle
calculations. These calculations use the grouped means as two points
on the real K support faces, with precisely the properties in Section 2.

## 5. One physical circle corner: complete normal-line calculation

Choose the actual own axes, with the original circle origin fixed, so

    K=[a-1,a] times [b-1,b],
    a>=b>=1/2, a^2+b^2=R^2,
    q=tau*(a,b).

The unique physical corner is z=(a,b); in this mask b>1/2. The
following bounds also allow the closed enlargement b=1/2.
Here a>1 and b<=R/sqrt(2)<3/2.

If 1-1/a<=tau<=1, then q belongs to K. Indeed its first coordinate
lies in the horizontal interval, and
b*tau>=b-b/a>=b-1 while b*tau<=b. Its positive radial parameter
and the supporting-half-plane inequalities give (3).

Suppose tau>1. The point q is strictly above and right of K. The
rectangle normal cones permit only the outer circle corner and the
opposite inner corner as support points whose unoriented normal line
passes through q; no side-interior normal line does. The circle corner
is forbidden by Section 2, leaving only one point for two distinct
means. This is impossible.

Suppose tau<1-1/a, so q_x<a-1. If q_y<b-1, the same normal-cone
check again permits only the inner corner and the forbidden outer
circle corner. If q_y=b-1, the only extra candidate is the lower-right
corner with horizontal East normal; its support a>=R/sqrt(2)>R-1
contradicts (6).

The final range is q_x<a-1 and b-1<q_y<b. Its only non-circle
candidates are the left-side point (a-1,q_y), a right-side East contact,
and the lower-right corner P=(a,b-1). The East contact is again
forbidden by (6), so two distinct means require the lower-right corner.
Its actual outward normal has the form n=(cos(theta),-sin(theta)),
with

    0<=tan(theta)=[b*tau-(b-1)]/[a*(1-tau)]<(a-b)/a.

But throughout this complete angular interval,

    h_K(n)=a*cos(theta)-(b-1)*sin(theta)>=R/sqrt(2)>R-1.    (7)

Here is the full scalar verification. The expression is positive and
concave, so its minimum on the closed comparison interval occurs at an
endpoint. At zero it is a>=R/sqrt(2). At the other endpoint put
e=a-b>=0, N=a^2+e*(1-b)>0 and D^2=a^2+e^2. Its value is N/D, and

    2*N^2-R^2*D^2
      =e*[2*b^2*(2-b)+e*(2+4*b-3*b^2)+e^2*(4-2*b)]>=0.

All bracket coefficients are positive for 1/2<=b<3/2. Positivity
of the trigonometric expression also follows from tan(theta)<=1
and a-(b-1)>0. The last strict inequality in (7) uses
R<2+sqrt(2), which holds throughout the original window. Thus (7)
contradicts the real-neighbor support bound (6).

Every possible q outside K has now been excluded. Hence q belongs
to K, is a positive multiple of F, and each Q_j-q is its outward
support normal with nonnegative length. This proves (3) in the entire
unique physical mask.

## 6. Two physical circle corners: the full proper-ray conclusion

Use the actual rectangle

    K=[d,d+1] times [-1/2,1/2], a=d+1,
    normalized circle average=(a,b), |b|<=1/2,
    q=tau*(a,b).

The closed interval in b includes either individual circle weight zero.
If d/a<=tau<=1, then q belongs to K and is positive radial. Formula
(3) follows from its support half-planes exactly as before.

If tau<d/a, then q_x<d. When |q_y|<1/2, the rectangle normal-line
check permits only one inner-face point, the two forbidden outer circle
corners, and an outer horizontal face contact. That outer contact has
support a>R-1 and contradicts (6). When |q_y|>1/2, the same check
leaves only one non-circle inner vertex. At |q_y|=1/2 the only possible
additional outer horizontal contact is again forbidden by (6). Thus
throughout this range two distinct means are impossible.

If tau>1, then q_x>a. When |q_y|>1/2, only one non-circle inner
corner has an unoriented outward-normal line through q, so two distinct
means are impossible. It remains that |q_y|<=1/2. Exclude the outer
horizontal contact by (6). Every remaining possible non-circle support
point is on the inner face x=d or one of its two endpoints. Its actual
outward normal points in precisely the direction Q_j-q: for a face
interior it is West, and at the upper/lower inner corner the vector
has the corresponding outward Northwest/Southwest signs. Therefore
Q_j-q=ell_j*n_j with ell_j>0. The parameter tau is positive, so q
is also a positive multiple of F.

This last range is deliberately retained. A two-corner concurrence
may lie outside the actual unit, and nothing in the theorem substitutes
an interior point for it. All possible radial-mask parameters have been
covered, proving (3) completely.

Finally, Q_j and every original P_i in its group have the same n_j
support projection. Taking that projection in (3) proves the individual
scalar relation (4), without a false individual concurrence assertion.

## 7. Literal H4 application at the full loaded C3

In the complete H-owned end domain of
INNER_PENTAGON_OWNED_END_RETURN_HEIGHT_AND_OPPOSITE_END_OWNER_REDUCTION.md,
take its strict Northeast HC, Y_C>0 row. That theorem proves the actual
HC and DC forces have exactly the same C-owned side axis. The actual
points S=(1,1) and R=P+u are both interior points of that same C side.

Keep the full loaded C3 with positive neighbors H,D,B. Write n for
the common unit direction from H and D into C, and let mu_H,mu_D>0
be those original magnitudes. The actual group mean is

    Q_C=(mu_H*S+mu_D*R)/(mu_H+mu_D).

The remaining group is the complete original CB force at its actual
application or shared-side mean. In both original H4_D0.L124 and
H4_D0.L0124, B is loaded and hence physically on the circle. The
general theorem therefore applies to this unchanged full C3:

    q_C=t_C*F_C, t_C>0,
    q_C=Q_C+ell_C*n, ell_C>=0,
    P_CB-q_C=ell_B*n_CB, ell_B>=0.

In particular the original CB direction is not parallel to the grouped
CH/CD direction. The two original CH and CD forces, their distinct
actual applications and the true degree three are all preserved. The
mean Q_C is not asserted to be an actual C/H or C/D contact. Every
physical C mask and individual zero circle coefficient remains.

## 8. Conditional literal roof-ABC application at the full loaded A3

In the original roof ABC.S graph let X=T, H=D, and keep A's three
actual neighbors X,H,B. B is loaded and physically on the circle.
Suppose in a retained original row the actual vectors from X and H
into A have the same direction m; for example, both can be North
in an aligned actual A frame. This is an explicit condition, not a
new normal selection or a claimed feature reduction.

Group the entire original AX and AH forces with their positive
weights at their mean Q_A on the actual minimum-m A face. Retain
the original AB force and full A circle resultant. The theorem gives

    q_A=t_A*F_A=Q_A+ell*m, t_A>0, ell>=0,

and the original AB proper-line relation with a nonnegative length.
It proves the two grouped directions nonparallel while retaining every
original AX/AH side mean. The actual A3 is never relabeled as true A2,
and no H3 or X3 equation is imposed on a different body.

This conditional export does not alone close that roof row or any
original H4 load family. It is available whenever the exact two-direction
and real-boundary-neighbor hypotheses have independently been proved.

## 9. Exact source scope and preservation

| Source | SHA256 | Exact use |
| --- | --- | --- |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Complete original force/moment equations and real support-face means |
| PARALLEL_TRANSMISSION_AND_FOUR_CYCLES.md | ec8be96131806c998d8a768526d2deb644c28be72559d34e033c8d07d917ffab | Degree-free full-star radial S/D aggregation in Lemma N.4, reproduced in Section 3 |
| C7_FORCE_POLYGON.md | d50d8ca48ea19156175e651bfa74be30ef3e58065ec14d8d1834670a41559089 | Physical circle-point obstruction and complete rectangle normal-line calculations; their local proof inputs are explicitly retained above |
| TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | 29e38d3f641fe16c6db587e51245f92ad4c447f9536db7d14c221f56b5357e82 | Provenance of the weaker proper-ray export for radial masks with only one actual boundary neighbor |
| INNER_PENTAGON_OWNED_END_RETURN_HEIGHT_AND_OPPOSITE_END_OWNER_REDUCTION.md | 23bb6edea9c4988b64636070ebe53acca5ca6617ddf7f595054948fdb8453c4b | Literal full C3 same-owned-side row, with all original actual ports retained |
| FIVE_BODY_BLOCK_LEAF_GRAPH_LOAD_COVER.md | e5c84071363e8dc43b09f9033c7cb3a7684f1de19bcd169d53c9eab55d51963b | Literal original roof ABC loads and true degrees in the conditional A3 application |

The general theorem has no determinant or generic-selection premise.
Every force with a different direction must remain as a separate group;
this theorem cannot be used if the full original star has three distinct
directions. Oppositely oriented normals are never merged as a same-sign
group. No original degree, force, application, circle coefficient or
physical completion unit is deleted. No Lean compilation, CI, numerical
pose search, historical-source mutation or metadata edit is used.
