# The mixed hub-owned / tip-owned four-load fan is excluded

**Status: complete hand mixed-owner exclusion; root and two separate
independent full hand audits passed.** Work in 79/40<=R<=sqrt(1105)/16 with the exact four-load
fan Hu_i (1<=i<=4), u_1u_2,u_2u_3,u_3u_4. H is clear and unloaded;
all four path bodies are loaded. The endpoints have degree2 and the
internal bodies retain degree3. All actual application means, physical
corner masks and four additional physical squares remain.

**Theorem.** The actual Hu_1 normal cannot be an H side axis while
H intersect u_4 is a singleton in the relative interior of a u_4 side.
Reflection covers the opposite endpoint assignment. This is the entire
mixed hub-owned / tip-owned family, including every shared Hu_1 mean.

## 1. Full coordinates and the relevant whole-path facts

FAN_ENDPOINT_OWNER_REDUCTION.md supplies, after a rigid coordinate
change for contact geometry,

\[
 H=[0,1]^2,\quad P_1=(p,1),\quad 0<p\le1,\quad n_1=e_y,
 \qquad Q_4=(0,0),\quad n_4=(-a,-b),
\]
\[
                    a,b>0,\qquad a^2+b^2=1.
\tag{1}
\]

Write the true circle origin as O=(X,Y). Actual circle forces are
weighted sums of z-O. P_1 is the true Hu_1 application mean; no midpoint
is prescribed. The entire physical first-endpoint contact lies on the
top side with strictly positive first coordinate. The other endpoint
contact is the tip-owned singleton Q_4.

The whole boundary-path theorem gives endpoint center minor angle
strictly greater than5pi/6, and each circle-resultant direction is
within pi/12 of its center direction. Thus their actual resultant
minor angle is strictly greater than2pi/3. The proof is the angular
triangle inequality in FAN_HUB_OWNED_ENDPOINT_EXCLUSION.md, Section1.

Normalize the actual circle-corner weights over the four path bodies
to sum to1. Every such corner is within3/sqrt(2) of c_H=(1/2,1/2),
using its actual H contact. Global force balance gives

\[
                   |O-c_H|^2\le\frac92-R^2<\frac35.
\tag{2}
\]

In particular

\[
                        Y<\frac12+\sqrt{3/5}<\frac{13}{10}.
\tag{3}
\]

The last comparison follows from3/5<16/25. This origin bound uses
all four genuine H neighbors and the original circle weights.

## 2. Coincident endpoint applications cannot support the boundary tip

We record a local fact to retain the side-mean corner limit below.
A loaded exact-degree-two body with a physical boundary neighbor
cannot have its two **actual force applications** equal.

Indeed the proper-concurrence lemma makes its pair normals nonparallel
and, if the applications equal P, makes P a positive multiple of its
circle resultant F. The sum of the two outward normals is opposite F
and lies in the normal cone of the body at P. Thus P is an inner radial
support point for the combined force, with zero moment about the true
origin. The radial-support calculation of
RADIAL_BRIDGE_AND_LEAF_REDUCTION.md, Section6, applies to this combined
force: it gives either radial S with P the midpoint of its inner face,
or radial D with |P-O|=R-sqrt(2).

In the S alternative the face-interior normal cone is one-dimensional,
contradicting the nonparallel pair normals. In the D alternative P
cannot belong to another boundary unit. The strict boundary-contact
radius is greater than R-sqrt(2): equality in the unit-diameter bound
would force that second body's circle corner to coincide with the
first body's circle corner, which cannot be shared. Both cases are
impossible. This argument retains shared-side means; it concerns their
actual values rather than their full intersection sets.

## 3. The actual path goes along the long hub arc

The tip-owned singleton Q_4 belongs to no third packing square.
The tangent-sector proof in FAN_TIP_OWNED_ENDPOINT_EXCLUSION.md,
Section2, applies there: H's quadrant and the tip's half-plane leave
no sector of angle90 degrees. In particular neither internal hub
application can equal Q_4.

The selected plane fan has exterior cycle H,u_1,u_2,u_3,u_4,H, so
the actual inner hub ports occur on the same H boundary arc between
P_1 and Q_4, with their physical cyclic order preserved at coincident
ports. The two possible arcs are the short top/left arc and the long
top/right/bottom arc.

On the short arc, every actual H normal has nonpositive first
coordinate, except for a possible normal at P_1 when p=1. For
0<p<1, even a coincident application at P_1 has the unique top-side
normal e_y. The same-side mean cannot create a positive horizontal
force. At Q_4 there is no internal application, as just proved.

Here is the full p=1 corner check. An H-owned force at its top-right
vertex cannot be a point-only vertex/vertex axis endpoint under the
retained strict convention. A tip-side-interior contact there with the
same vertical normal would also contain a shared top-side segment.
Thus Hu_1 has a positive-length shared horizontal segment and

\[
                   u_1=[s,s+1]\times[1,2],\qquad0\le s<1.
\tag{4}
\]

Any other path body containing P_1 must be u_2: u_1,u_3 are physically
disjoint by the loaded-noncontact theorem. If its actual H normal at
P_1 is horizontal to the right, its physical H contact extends down
the right side, so that port belongs to the long arc, not the short
one. If the normal has both components positive, consider its local
sector at P_1.

For s>0, u_1 occupies a full upper half-plane locally and H the
southwest quadrant. The only remaining90-degree sector is southeast;
it cannot have a minimum-support normal with both components positive.
Hence this case is impossible. For s=0, u_1 and H occupy the northwest
and southwest quadrants. The other body must have its whole tangent
sector in the right half-plane. A side-interior tangent half-plane
would force the horizontal H normal already handled. An oblique
vertex with both inward axes pointing strictly right gives a unique
leftmost point P_1, so its intersection with u_1 is just P_1. Then
both actual u_1 applications coincide, contrary to Section2. The only
remaining vertex possibility with an upward vertical side is

\[
                              u_2=[1,2]\times[1,2].
\tag{5}
\]

The downward vertical-side alternative has a negative-Y inward axis
and cannot admit the hypothesized strictly positive-Y normal.

In (5), the two aligned boundary squares have the same vertical interval
and consecutive horizontal intervals[0,1],[1,2]. Equality of their
maximum squared corner distances to O forces X=1. Their u_1 endpoint
torque equation then has Hu_1 origin moment proportional to1-X=0,
forcing the u_1u_2 boundary-edge moment to vanish. This contradicts
the nonradial boundary-contact theorem. The entire exceptional corner
case is therefore excluded or belongs to the long-arc port order.

On a genuine short-arc order, both internal hub normals consequently
have nonpositive X components. The first endpoint has zero X component
and n_4 has strictly negative X component. Positive hub force balance
is impossible. The actual path must therefore follow the long arc,
clockwise from P_1 through the right and bottom sides to Q_4.

The extended physical ports preserve this clockwise order at the circle,
as in the earlier endpoint theorem. The actual boundary-edge origin
moment in that direction is strictly negative, by its general sign
lemma. The true u_1 endpoint torque equation gives

\[
             \det(P_1-O,n_1)=p-X<0,
                     \qquad X>p>0.
\tag{6}
\]

No internal body was replaced by a degree-two tip in this argument.

## 4. The true endpoint forces point northwest and southwest

Proper endpoint concurrence, valid for every physical circle mask,
gives positively radial points with coordinates relative to O

\[
 q_1=(p-X,1-Y)+\ell_1 e_y,\qquad
 q_4=(-X,-Y)+\ell_4(-a,-b),\qquad\ell_1,\ell_4\ge0.
\tag{7}
\]

Both first coordinates are strictly negative by (6). If the first
resultant had nonpositive Y component, (7) would imply Y>=1 and
the fourth resultant would have negative Y component too. Both would
lie in one closed90-degree quadrant, contrary to their separation
greater than120 degrees. If the fourth had nonnegative Y component,
(7) would imply Y<=0 and the first would have positive Y component,
with the same contradiction. Thus

\[
                         (F_1)_y>0>(F_4)_y.
\tag{8}
\]

Their directions are more precisely in(90,150) degrees and(210,270)
degrees: both lie in the left half-plane and their separation exceeds
120 degrees. This retains radial concurrences outside their square;
no assertion that q_i belongs to its body has been used.

The clockwise endpoint torque at u_4 also gives

\[
                  \det(Q_4-O,n_4)=bX-aY=:K>0.
\tag{9}
\]

## 5. The endpoint centers occupy the corresponding left quadrants

The min-Y support of u_1 is y=1, so its absolute center height is
at least3/2. Equations(2)--(3) therefore put its center, relative to O,
strictly above the horizontal axis.

Its relative center X coordinate is nonpositive. For a square aligned
with H this follows immediately from (F_1)_x<0: a positive center X
coordinate would make every farthest corner's X coordinate positive.
For an oblique square its unique bottom vertex is P_1. Write

\[
 u_1=P_1+[0,1](-s,c)+[0,1](c,s),\qquad c,s>0,\quad c^2+s^2=1.
\tag{10}
\]

Put A=X-p>0. If its relative center X coordinate
-A+(c-s)/2 were nonnegative, then c>s. Its center Y coordinate is
positive, so its scalar product with the inward axis(c,s) is positive.
Every physical farthest corner would therefore include that axis.
The possible X coordinates of those corners are -A+c and -A+c-s.
Both are strictly positive because A<=(c-s)/2. This contradicts
(F_1)_x<0. Thus the oblique center actually has negative X coordinate;
the aligned zero case remains.

For u_4 put n=(-a,-b), k=Jn=(b,-a), and use its actual tip-owned chart

\[
        u_4=Q_4+[0,1]n+[-\rho,1-\rho]k,\qquad0<\rho<1.
\tag{11}
\]

By (8), F_4 dot n>0. By (7),(9), F_4 dot k<0. Consequently its
center's n-coordinate is nonnegative and its k-coordinate nonpositive:
a strict opposite sign of a center coordinate would force that sign
at every physical farthest corner and hence at the resultant.
The relative center's X coordinate is therefore strictly negative,
since n_x=-a<0,k_x=b>0 and the center is nonzero. Finally the direction
of F_4 is in(210,270) degrees, and its center deviates by less than
15 degrees. Its center Y coordinate is strictly negative.

Write the two centers relative to O as

\[
 c_1-O=(-r_1\sin\delta_1,r_1\cos\delta_1),\qquad
 c_4-O=(-r_4\sin\delta_4,-r_4\cos\delta_4),
\]
\[
                         0\le\delta_1,\delta_4<\pi/2.
\tag{12}
\]

The actual clockwise boundary path uses the complementary right arc
of length pi+delta_1+delta_4. Its three contacts each span less than
theta=acos(9/25). Hence, with alpha=3theta-pi,

\[
             \delta_1+\delta_4<\alpha<\pi/6,
 \qquad\cos\alpha>89/100,\qquad\sin\alpha<9/20.
\tag{13}
\]

## 6. One endpoint uses a general width bound, the other the tip metric

Put sigma=1/sqrt(2) and d=sqrt(R²-1/4)-1>9/10. Let h_1<=sigma
be u_1's coordinate halfwidth in the vertical direction. Its actual
min-Y support and boundary center radius r_1>=R-sigma give

\[
 1-Y=r_1\cos\delta_1-h_1
                  \ge (R-\sigma)\cos\delta_1-\sigma.
\tag{14}
\]

For the other endpoint write a=sin(phi), b=cos(phi). Its center signs
in the n,k basis give0<phi<=delta_4. Define

\[
 N=(Q_4-O)\cdot n=aX+bY,
 \qquad K=-(Q_4-O)\cdot k=bX-aY>0,
 \qquad Z=K+\rho.
\tag{15}
\]

From (11)--(13) its center components are

\[
 N+\tfrac12=r_4\cos(\delta_4-\phi),\qquad
 Z-\tfrac12=r_4\sin(\delta_4-\phi)\ge0.
\tag{16}
\]

Here N>0: r_4>5/4 and delta_4-phi<pi/6 give
N>(5sqrt(3))/8-1/2>0. Thus every farthest circle corner is on its
outer n-face, and the actual physical circle equation is

\[
                       R^2=(N+1)^2+Z^2.
\tag{17}
\]

The physical two-corner case Z=1/2 remains, with every corner-weight
split. Equation(15) also gives

\[
                           Y=bN-aK\ge bN-aZ.
\tag{18}
\]

These are exactly the scalar endpoint premises of
FAN_TIP_OWNED_ENDPOINT_EXCLUSION.md, Section6, with the horizontal
endpoint coordinate there replaced by Y here. That full calculation
uses (16)--(18),0<=phi<=delta_4<pi/6, and the actual circle equation;
it does not use the other endpoint's owner. It yields

\[
                           Y\ge d\cos\delta_4-\frac35\sin\delta_4.
\tag{19}
\]

## 7. The unit vertical separation is insufficient over the whole domain

Define

\[
 A(t)=(R-\sigma)\cos t-\sigma,
 \qquad B(t)=d\cos t-\frac35\sin t.
\tag{20}
\]

Both functions are concave and nonincreasing on[0,alpha]. For B,
positivity and B''=-B follow from d>9/10,alpha<pi/6; for A its
second derivative is-(R-sigma)cos t<0. For a fixed sum of arguments,
concavity places the minimum of A(s)+B(t) at one of the two endpoint
allocations. Monotonicity and (13) consequently give

\[
 A(\delta_1)+B(\delta_4)
 \ge\min\{A(\alpha)+B(0),\ A(0)+B(\alpha)\}.
\tag{21}
\]

Both right-hand alternatives are strictly greater than1. Using
R-sigma>5/4, sigma<5/7 and the exact bounds in (13),

\[
 A(\alpha)+B(0)>
 \frac54\frac{89}{100}-\frac57+\frac9{10}
                         =\frac{727}{560}>1.
\tag{22}
\]

Also R-sqrt(2)>11/20, since R>=79/40 and sqrt(2)<57/40. Hence

\[
 A(0)+B(\alpha)>
 \frac{11}{20}+\frac9{10}\frac{89}{100}
                    -\frac35\frac9{20}
                         =\frac{1081}{1000}>1.
\tag{23}
\]

But (14),(19) imply

\[
                     1=(1-Y)+Y\ge A(\delta_1)+B(\delta_4)>1.
\]

This contradiction excludes the entire mixed tip-owned family.

## 8. Exact scope

The entire Hu_1 shared-mean interval, including its corner endpoint,
is covered. No frame is imposed on u_1; its aligned and oblique
min-Y supports are both included. The other endpoint retains every
physical one-/two-circle-corner mask and its full relative side
coordinate. The proof keeps every internal degree-three force and
all four extras. It does not close either genuine free endpoint mask;
those require their separate physical routing and metric arguments.

No numerical pose premise, secondary packing motion, post-certificate
normal change, Lean compilation or CI is used.
