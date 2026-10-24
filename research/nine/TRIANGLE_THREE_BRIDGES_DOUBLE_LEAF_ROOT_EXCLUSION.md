# Two leaves at one triangle root exclude a third leaf at another root

**Status: complete hand whole-attachment exclusion; root and separate
independent full hand audits passed.** Work in
\[
                       79/40\le R\le\sqrt{1105}/16.
\tag{1}
\]
The exact positive graph has triangle A,B,C, two distinct pendant
leaves at A and one pendant leaf at B. Its six bodies leave three
additional arbitrary physical squares. All remain in place.

**Theorem.** This entire attachment is impossible. Every S/D leaf
choice, physical C circle mask, contact owner and actual side mean
is retained. The proof first gives a uniform geometric isolation
lemma for every two-leaf articulation, then handles its complete
exceptional-radius configuration.

## 1. Exact leaf geometry and the central-disk isolation lemma

Put
\[
 r=R-\sqrt2,\qquad s=1-r,\qquad
 d=\sqrt{R^2-\tfrac14}-1,\qquad \delta=d-1.
\tag{2}
\]
The useful bounds throughout the window are
\[
 \frac12<r<\frac7{10},\quad
 s>\frac3{10},\quad
 \frac9{10}<d<\frac{61}{60}.
\tag{3}
\]
Every true leaf is radial S or D. Its articulation has a radial
outward support point p=d e in type S, or p=r e in type D.
In type D the point is in a relative side interior, so that
articulation contains the origin in its open interior.

**Central-disk lemma.** Let A support two distinct radial leaves
in the selected convention.

* If d<1, the origin is in the open interior of A.
* If d>1, the closed disk D_delta is contained in the open interior
  of A.
* If d=1, either the origin is interior to A, or A has the origin
  at a vertex and its two leaves are radial S in the two side
  directions from that vertex.

These assertions are geometric. They do not require that A's other
neighbors be boundary squares, and they use none of their force
equations.

### 1.1. At least one D leaf

If a D leaf is present, rotate it east. Then
\[
            A=[-s,r]\times[t-\tfrac12,t+\tfrac12],
                      \qquad |t|<\tfrac12.
\tag{4}
\]
Origin-interior containment proves the first and third assertions.

For d>1, if the other leaf is D, its direction must be an adjacent
side direction: the opposite direction would require 2r=1, and
the same direction would repeat the physical leaf. After reflection,
\[
                             A=[-s,r]^2.
\tag{5}
\]
Its four side distances exceed 3/10, whereas delta<1/60.

If the other leaf is S, the complete radial support cover in (4)
has just a top-side application or a top vertex, after reflection.
The side case would put the top height at d>1, incompatible with
|t|<1/2. A vertex has coordinates
\[
                 (r,Y)\quad\hbox{or}\quad(-s,Y),
                 \qquad Y=\sqrt{d^2-x^2},\quad0<Y<1,
\]
and
\[
                             A=[-s,r]\times[Y-1,Y].
\tag{6}
\]
Here x is r or -s. Its magnitude is greater than3/10. Therefore
\[
                       4\delta<1/15<x^2.
\]
Equivalently, d^2-x^2<(2-d)^2, so
\[
                              Y<2-d=1-\delta.
\tag{7}
\]
Also Y>1/2: use d>9/10, |x|<7/10 and
Y^2>81/100-49/100>1/4. Both horizontal distances exceed3/10,
and both vertical distances exceed delta. Hence D_delta is
strictly inside A. This treats every side/vertex endpoint.

### 1.2. Both leaves are S

Their distinct applications p_i=d e_i are distinct radial outward
support points of the same unit square. The following side/vertex
classification is exhaustive; it is purely geometric.

If at least one application uses a side support face, rotate it
east:
\[
                  A=[d-1,d]\times[t-\tfrac12,t+\tfrac12],
                            \qquad |t|\le\tfrac12.
\tag{8}
\]
The second direction cannot be the same, and the opposite side
would require 2d=1. An adjacent side gives
A=[d-1,d]^2 after reflection, with d<=1. A distinct vertex must
be on the left face; equality of its norm with d gives
\[
 A=[d-1,d]\times[Y-1,Y],\qquad
 Y=\sqrt{2d-1},\qquad d\le1.
\tag{9}
\]
The radial sign of the left coordinate proves d<=1. For d<1 the
origin is interior. For d=1 both (8)--(9) become [0,1]^2, with
the two leaf directions equal to its two side directions from0.

If both applications are unique vertices and are adjacent, equal
norms give, after rotation and reflection,
\[
 A=[a-1,a]\times[-\tfrac12,\tfrac12],\qquad
 a=\sqrt{d^2-\tfrac14}.
\tag{10}
\]
Here 0<a<1 throughout (1), so the origin is interior. If d>1,
then a>delta and
\[
                   a<2-d=1-\delta,
\tag{11}
\]
because d<61/60<17/16 and
d^2-1/4<(2-d)^2 is equivalent to d<17/16.
The other two side distances are1/2>delta. Again D_delta is
strictly inside.

If the applications are opposite vertices, rotate their diagonal
horizontally. The full square and applications are
\[
 A=\{(X,Y):|X|+|Y-h|\le1/\sqrt2\},\qquad
 p_\pm=(\pm1/\sqrt2,h),
\]
\[
                  h=\sqrt{d^2-\tfrac12},\qquad
                  0<h\le1/\sqrt2.
\tag{12}
\]
The final inequality is exactly radial outward support at both
vertices, and gives d<=1. For d<1 the origin is interior.
For d=1 it is the lower vertex; p_+,p_- are the two adjacent
vertices reached by its unit side axes. Thus the two leaf directions
are again exactly those side directions. This completes the
central-disk lemma.

## 2. Every radius except d=1 is immediately impossible

Each leaf at A or B has a positive circle load. Its articulation
is physically circle-clear by the radial central-endpoint theorem.
The remaining triangle vertex C is loaded: if it were unloaded,
its opposite degree-two forces would place A and B beyond opposite
supports, contrary to their actual contact.

The single-leaf articulation B always contains the origin when
d<=1: this is immediate for a D leaf, and for S the inward unit
segment from d e contains0. When d>1 it meets D_delta, because
that segment contains (d-1)e. A D articulation still contains0.

For d<1, Section1 makes0 an interior point of A while it belongs
to B, contradicting interior disjointness. The same contradiction
works whenever d=1 and0 is interior to A. For d>1, Section1 puts
all of D_delta strictly inside A, while B meets that closed disk.
Again the two physical unit interiors must overlap. A point of B
inside the open interior of A is already enough, because interior
points of B approach every point of its closed square.

Thus the only remaining case is exactly
\[
 d=1,\quad R^2=17/4,\quad A=[0,1]^2,
\]
\[
 E=[1,2]\times[-\tfrac12,\tfrac12],\qquad
 N_0=[-\tfrac12,\tfrac12]\times[1,2].
\tag{13}
\]
Here E,N_0 are the two distinct radial S leaves of A. B contains0
on its boundary, and its own leaf must also be S: a D articulation
would contain0 in its interior and overlap A.

## 3. The complete exceptional contact at the loaded C

At R^2=17/4 every square center has norm at most3/2, by the
farthest-corner bound |c|^2+|c|+1/2<=R^2.
The physical boundary square C cannot meet A on either of its
outer side interiors. For example an east-side contact has the
actual supporting normal e_x and forces (c_C)_x>=3/2.
The center bound then gives c_C=(3/2,0), and equality in the
support width makes C exactly E. That is a different already
present body. The north side similarly repeats N_0.

Nor can C contain A's northeast vertex (1,1). Any common support
normal there has nonnegative coordinates, say n=(a,b).
If both are positive then
n dot c_C>=a+b+1/2>3/2, impossible. At an axis endpoint the
same center bound forces E or N_0, neither of which contains
(1,1). This includes every owner and free-normal possibility.

C cannot contain (1,0) or (0,1), either. Each is in the relative
interior of a radial S leaf's inner side. Any other square containing
that point and disjoint from the leaf has the corresponding inner
side common normal. C7_FORCE_POLYGON.md, Lemma2.1, puts that
entire neighboring square strictly inside the circle. It cannot be C.
Finally C cannot contain0, since R>sqrt(2).

Therefore, after exchanging the two coordinate axes if necessary,
the actual AC contact and normal are
\[
                  p_{AC}=(0,y),\quad0<y<1,\qquad n_{AC}=-e_x.
\tag{14}
\]
This is a side-interior contact of A, so its normal is fixed.
The actual C mask and every possible mean on C are still arbitrary.

Let n be the normal from A into B. The physical triangle A,B,C
and the A-owned axis n_AC imply
\[
                                  n_x\le0.
\tag{15}
\]
A's true force equation has the form
\[
                   \alpha e_x+\beta e_y+\mu n-\nu e_x=0,
                    \qquad\alpha,\beta,\mu,\nu>0.
\tag{16}
\]
Thus n_y<0. If n_x<0, the AB application is A's southwest
vertex0. But then its origin moment vanishes, whereas the AC
moment is nu y>0 and both radial leaf moments vanish. This
contradicts the actual A torque. Hence n=-e_y.

This actual normal and the bottom support line of A put the entire
body B in y<=0. No AB midpoint or B frame is inferred or needed.

## 4. The acute-point contradiction

Let q be the actual BC contact. The preceding support gives q_y<=0,
while (14) has p_AC=(0,y) with y>0. Both points belong to the
physical boundary square C, yet
\[
                             p_{AC}\cdot q\le0.
\tag{17}
\]
This is impossible by the strict45-degree point cone in
ACUTE_LOADED_CONTACT_GRAPH.md, Theorem A.1: every pair of points
of a circle-touching unit in (1) has strictly positive scalar
product. This geometric conclusion holds for every physical
circle mask and every actual shared-side mean. It also covers
coincident contacts, since C contains no origin.

The exceptional configuration (13) is therefore impossible.

## 5. Full attachment conclusion and reusable scope

The central-disk lemma covers every pair of genuine radial leaves
without a condition on the other neighbors of their articulation.
For the present exact component, B's own leaf forces its articulation
into that disk. Every noncritical radius is excluded directly.
At the only boundary exception, the complete physical C-contact,
normal and torque cover gives (17).

Thus two leaves at one triangle root and one at a distinct triangle
root are impossible throughout (1). All three additional units
remain fixed, and no secondary minimizer, capacity assumption,
numerical pose sample or new normal selection is used.

This closes that entire attachment of C1.3.b3. It does not silently
delete a force from another graph or declare the remaining rooted
layouts closed. No Lean compilation or CI is used.

