# A selected positive diamond cannot have an unloaded degree-three hub

**Status: complete hand selection and geometric theorem; root and separate
independent full hand audits passed, including all Section5--6 corollaries.** This is a radius-free statement. It uses the
same strict point-normal convention and compatible planar selection
as PHYSICAL_BODY_GRAPH_UNCROSSING.md.

Let U,A,B,C be four interior-disjoint closed unit squares with physical
contacts
\[
                         UA,\quad UB,\quad UC,\quad AB,\quad AC.
\tag{1}
\]
No BC contact is required. Suppose U has zero circle load and its
entire positive neighborhood is exactly A,B,C. The three pair
magnitudes at U are strictly positive.

**Theorem.** The necessary physical certificate can be selected so
that no such star occurs. The statement allows arbitrary circle
masks, loads and additional positive edges at A,B,C. It also allows
additional zero-weight physical contacts at U.

The selection is made before obtaining multipliers. It does not
assert impossibility for every arbitrary choice of free point
normals. In particular, a point-only normal is never changed to an
axis endpoint after a stress has been obtained.

## 1. A central edge owned by U is immediately impossible

Write n_0,n_B,n_C for the outward normals from U toward A,B,C,
and let their positive magnitudes be mu_0,mu_B,mu_C. The unloaded
force balance is
\[
                   \mu_0n_0+\mu_Bn_B+\mu_Cn_C=0.
\tag{2}
\]

If n_0 is a side axis of U, apply
UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md to the physical triangles
UAB and UAC. It gives
\[
                         n_0\cdot n_B\ge0,
                 \qquad n_0\cdot n_C\ge0.
\]
The dot product of (2) with n_0 is then strictly positive, a
contradiction. This includes every positive-length shared UA side,
with its arbitrary aggregate application mean.

Hence UA is a singleton at a U vertex, and n_0 strictly exposes
that vertex in U. By a rigid motion and choice of the side signs,
normalize
\[
 U=[0,1]^2,\qquad q_0=(1,1),\qquad
 n_0=(a,b),\quad a,b>0,\quad a^2+b^2=1.
\tag{3}
\]
Either A owns this normal, or UA is a free vertex/vertex contact.

## 2. The entire contact-location cover at U

First suppose one of the other normals is a side axis of U. Applying
the same triangle theorem with that normal as the owned edge gives
a nonnegative dot product with n_0. Thus only +e_x or +e_y can
occur; the negative axes are impossible.

A non-axis outward normal of U strictly exposes one of its four
vertices. At q_0 both of its coordinates are positive. At the
opposite vertex (0,0), both coordinates would be negative, and this
case is also impossible geometrically.

Indeed, suppose T is that opposite-vertex neighbor and m is its
outward normal from U. Then m dot n_0<0, and (0,0) is a minimum-m
support point of T. The support-span lemma from
UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md gives
\[
                          \max_{x\in T}n_0\cdot x<1.
\tag{4}
\]
Every point of A has n_0-projection at least
\[
                           n_0\cdot q_0=a+b>1.
\tag{5}
\]
Thus T cannot touch A, contrary to (1).

The only remaining sources of a negative x-component and a negative
y-component are, respectively, the two adjacent vertices (0,1)
and (1,0). Equation (2) requires both negative components, and
there are only two other edges. After interchanging B and C if
necessary, every possible star therefore has exactly
\[
 \begin{aligned}
 q_B&=(0,1),& n_B&=(-c,d),& c,d&>0,&c^2+d^2&=1,\\
 q_C&=(1,0),& n_C&=(e,-f),& e,f&>0,&e^2+f^2&=1.
 \end{aligned}
\tag{6}
\]

In particular all three applications are distinct fixed singleton
points. No shared-side mean has been fixed by assumption: every
U-owned or shared-side alternative was covered and excluded above.
The normals in (6) may still be owned by the tips or free.

## 3. A compatible finite selection removes a free central normal

Take the torque equation about q_0. Equations (3) and (6) give
\[
                       \mu_Bd=\mu_Ce.
\tag{7}
\]
Using (7) in the two coordinates of (2) gives
\[
                \mu_0a=\mu_B(c-d),\qquad
                \mu_0b=\mu_C(f-e).
\tag{8}
\]
In particular c>d and f>e in a positive star. Eliminating the
magnitudes gives the necessary direction identity
\[
                \det\bigl(n_0,V(n_B,n_C)\bigr)=0,
 \qquad V=\bigl(e(c-d),\ d(f-e)\bigr).
\tag{9}
\]

If V=0, (7)--(8) already make a positive star impossible. If V is
nonzero and n_B,n_C are fixed, equation (9) forbids at most two
directions for a free n_0 in its open strict interval.

If either of n_B,n_C is also free, its parameter belongs to q_B
or q_C, independently of the parameter at q_0. If V is not
identically zero on that product of normal intervals, fix a choice
with V nonzero and vary n_0. This proves that the left side of (9)
is not identically zero on the full product. Its zero set is a
proper real-analytic zero set, with empty interior. If V is
identically zero, the star is impossible throughout that product
and no exclusion is needed.

Before extracting a certificate, prelist the finitely many ordered
physical quadruples (U,A,B,C), central free edges and three-corner
patterns (3),(6). Impose these nontrivial exclusions together with
all the previously selected finite generic conditions. At a
four-square junction its matched parameter is coupled only with
the opposite pair at that same junction. The three points in (3),
(6) are distinct, so this matching does not identify any of the
three parameters used in (9). The exclusions remain open dense
inside the allowed strict, nonradial and matched-normal domain.

This selection uses no unknown multiplier, circle-weight split or
shared-side application mean. Subsequent planar uncrossing keeps
the surviving point normals and adds only actual shared-side
forces; thinning only removes atoms. A final positive star satisfying
the theorem's hypotheses must still satisfy the contact cover of
Section2 and was included in the prelist.

Consequently the central edge UA of a surviving star must be
**owned by A**. Its application q_0 is then in the relative
interior of an A side. A point-only vertex/vertex endpoint cannot
carry an A-axis normal under the retained strict convention.

## 4. The owned central edge requires more than A's tangential width

Continue with (3),(6). Let m_0=(-b,a). Since A owns the central
normal, every point of A has coordinates
\[
 x=q_0+u n_0+\lambda m_0,
 \qquad 0\le u\le1,\qquad
 \lambda_0\le\lambda\le\lambda_0+1.
\tag{10}
\]
Here -1<lambda_0<0, but only the tangential width1 will be used.

By (8), define
\[
                     t=\frac dc\in(0,1),\qquad
                     s=\frac ef\in(0,1).
\tag{11}
\]
Equations (7)--(8) give the exact ratio
\[
                       \frac ab=\frac{s(1-t)}{t(1-s)}.
\tag{12}
\]

Every point of B is on the outward side of its U-support line,
so an actual AB contact point in (10) must satisfy
\[
 -c(1+ua-\lambda b)+d(ub+\lambda a)\ge0.
\]
As b+at>0, this implies
\[
 \lambda\ge\frac{1+u(a-bt)}{b+at}
       \ge \frac{1+\min(0,a-bt)}{b+at}=:L_B.
\tag{13}
\]
Likewise every point of C satisfies its outward U-support
inequality. An actual AC contact point must satisfy
\[
 e(ua-\lambda b)-f(1+ub+\lambda a)\ge0,
\]
and hence
\[
 \lambda\le-\frac{1+u(b-as)}{a+bs}
       \le-\frac{1+\min(0,b-as)}{a+bs}=:-L_C.
\tag{14}
\]

The two actual contacts need not have the same u-coordinate. The
uniform bounds (13)--(14) nevertheless require A's tangential
interval to have length at least
\[
 F:=L_B+L_C
   =\frac{1+\min(0,a-bt)}{b+at}
       +\frac{1+\min(0,b-as)}{a+bs}.
\tag{15}
\]
We now prove F>1 throughout (3),(11),(12), contradicting the
unit width in (10).

If a-bt and b-as are both nonnegative, then t,s<1 gives
\[
             F=\frac1{b+at}+\frac1{a+bs}
                    >\frac2{a+b}\ge\sqrt2>1.
\tag{16}
\]

The two differences cannot both be negative: the first would imply
a<b and the second b<a. By symmetry it remains to consider
a<bt. Then b-as>0. Put
\[
                             D=b(1-t)+at>0.
\]
Equation (12) gives
\[
                  s=\frac{at}{D},\qquad
                  a+bs=\frac{a(b+at)}{D}.
\tag{17}
\]
Thus
\[
                       F=\frac{1+a-bt+D/a}{b+at}.
\tag{18}
\]
The numerator minus the denominator is exactly
\[
 \begin{aligned}
 1+a-bt+D/a-b-at
   &=(1-t)(1+a+b/a-b)+2t(1-b)\\
   &>0.
 \end{aligned}
\tag{19}
\]
Both endpoint coefficients are positive because 0<a,b<1 and
0<t<1. This proves F>1 in the remaining case. The case b<as is
the reflection exchanging a,b and t,s. Equalities in either
coefficient are already covered by (16).

The contradiction between (10) and (15)--(19) excludes every
A-owned central edge. Together with Sections1--3, this proves the
theorem for the entire unloaded three-edge diamond hub.

## 5. Complete diamond attachment consequences

### 5.1. Leaf at a hub: the entire S branch is closed

In C1.4.b1 with a diamond block, write A,U for its hubs, B,C for
its tips, and attach the radial leaf L to A. The five block edges
are exactly (1). U has positive degree3. The present theorem
excludes every zero-circle-weight U, whether physically clear or
physically circle-touching, for both S and D leaves.

For an S leaf, S_LEAF_CONNECTED_BOUNDARY_NEIGHBORS.md already
excludes every physically circle-touching U: B--U--C is a connected
graph of boundary neighbors of A containing all other possible
loads. That theorem retains zero-weight physical boundary vertices.
The remaining physically clear U has zero circle weight and is
excluded here. Therefore the **entire S-leaf, hub-attachment
diamond branch is closed**, with all four completion squares
retained. No completion capacity estimate is needed in this branch.

For a D leaf, any surviving hub-attachment diamond must have a
strictly positive circle load at U, and therefore U physically
touches the circle. This is a full load reduction, not its metric
exclusion.

### 5.2. Leaf at a tip: both leaf types are excluded

Now attach the leaf L to a diamond tip A. Write B,C for the two
hubs and U for the other tip. The positive diamond edges are
\[
                          BC,\quad BA,\quad BU,\quad CA,\quad CU.
\tag{20}
\]
The hubs B and C each have exact positive degree3. For hub B its
central neighbor C physically touches both other neighbors A,U;
the theorem therefore forces B to have a positive circle load.
The same argument with B,C interchanged forces C to be loaded.

The unattached tip U has positive degree2 and its neighbors B,C
physically touch. The existing two-force transmission obstruction
for a triangle tip therefore forces U to be loaded as well. Thus
B,C,U are three physically circle-touching squares, with all three
physical pair contacts. This contradicts the circle-touching graph
theorem in CIRCLE_CONTACT_ANGULAR_ORDER.md, Section5.

Consequently the **entire diamond tip-attachment branch is closed**.
The argument retains both S and D leaf types at A, every physical
corner mask and shared mean, and all four arbitrary completion
squares. No completion capacity estimate is needed.

After these corollaries, the only remaining diamond domain of
C1.4.b1 is a D leaf at a hub whose second hub carries positive
circle load. The all-three-loaded C4 is the other graph branch
still open in that coarse cell.

## 6. Global neighbor sparsity and the five-body fan masks

**Corollary 6.1.** The three physical neighbors of an unloaded
positive degree-three body induce at most one physical pair edge.

Indeed, two distinct edges among three vertices share one endpoint.
Call it A and the other two B,C. Those two physical edges together
with the body's three positive contacts satisfy (1), contradicting
the theorem. The physical edges used here need not have positive
multipliers.

For the five-body fan of FIVE_BODY_BICONNECTED_REDUCTION.md, write
the path as u1--u2--u3--u4 and the universal hub as H. Both inner
path vertices have positive degree3. The neighbors of u2 are
H,u1,u3, and H physically touches both u1 and u3. Thus u2 must
be loaded. The same argument makes u3 loaded. The endpoint tips
u1,u4 are already loaded by the degree-two triangle obstruction.

This excludes **both entire three-load fan masks** of the earlier
exhaustive graph reduction. Every surviving five-body fan has all
four path vertices loaded and the universal hub physically clear.
It does not yet exclude that four-load fan or complete C1.5.b0.

## 7. Scope

The radius-free theorem needs exact positive degree3 at U. It does
not apply to a hub with further positive neighbors, nor does it
claim nonobtuseness of two arbitrary normals in a contact triangle.
The U-side-owner premise of the cited triangle lemma was used
explicitly wherever that lemma was invoked.

No numerical pose sample, radius subdivision, secondary minimizer,
Lean compilation, CI or altered point-normal convention is used.
