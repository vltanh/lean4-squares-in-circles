# A triangle with a three-edge pendant chain is impossible

**Status: complete hand whole-attachment exclusion; root and separate
independent full hand audits passed.** Work throughout
\[
                     79/40\le R\le\sqrt{1105}/16
\tag{1}
\]
with the common selected physical certificate. The exact positive
component considered here has the triangle A,B,C and pendant path
\[
                              A-U-V-L.
\tag{2}
\]
Its six bodies leave three arbitrary additional physical squares,
which remain in place throughout the proof.

**Theorem.** No selected positive component has (2). Every physical
circle mask, leaf type, transmitter width and actual application
mean is included. This closes the length-three-chain attachment
in C1.3.b3, independently of all three extra squares.

## 1. Local all-bridge vertices and the complete load cover

We use the following local consequence of the radial bridge law.
It does not require that the entire component be a tree.

If a loaded body has only bridges incident to it, it is the outer
body at every incident bridge: the inner endpoint of a bridge is
physically circle-clear. All its applications are consequently its
unique nearest point to the origin. Aggregating these collinear
forces gives exactly the radial-leaf calculation of
RADIAL_BRIDGE_AND_LEAF_REDUCTION.md, Section6. The body is radial S
or radial D. A radial D body has only one such neighbor in the
selected convention: its off-origin vertex must lie in the relative
interior of the neighbor's side, and two distinct side-interior
half-planes cannot fit there disjointly. A radial S body can have
at most two neighbors; its two circle weights and their aggregate
force are exactly those of the radial terminal law.

The genuine leaf L is loaded. The other endpoint V of its bridge
is physically circle-clear by the radial central-endpoint theorem,
so V is unloaded. The exact degree-two triangle vertices B,C are
loaded as well: an unloaded degree-two square transmits opposite
normals, putting its two neighbors beyond separated supports,
whereas B's and C's two neighbors touch. A is physically
circle-clear, since otherwise the triangle A,B,C would be three
pairwise touching boundary units.

It remains to check the full possible load at U; it is not
silently declared a transmitter. Suppose U were loaded. The local
all-bridge statement makes it radial S, because its positive
degree is two and radial D has degree one. Put
\[
 d=\sqrt{R^2-1/4}-1,\qquad r_D=R-\sqrt2.
\tag{3}
\]
Rotate so the common incoming application of U is d e_x.
Both A and V apply their forces there. The unloaded exact-degree-two
body V has opposite normals, so its contact to the loaded leaf L
is directed along -e_x. The leaf law then puts that application
at -r_L e_x, where r_L is d or r_D.

These are the two opposite supports of V, whose projected width
would therefore be d+r_L. But throughout (1),
\[
       d>9/10,\qquad r_D>11/20,\qquad
       d+r_L>29/20>\sqrt2.
\tag{4}
\]
For the D bound use sqrt(2)<57/40; the S alternative is still
larger. This exceeds the maximum width of a unit square. Thus U
cannot be loaded.

The entire load cover is now established: only B,C,L carry circle
load, while A,U,V are physically clear or unloaded as stated.
No degree-two equation was used before the corresponding zero
load had been proved.

## 2. Both actual transmitter widths put A in a narrow western cap

Rotate the actual radial leaf direction so L points east.
Since U and V are unloaded exact-degree-two bodies, their equal
opposite force lines are parallel to e_x. Their actual projected
widths satisfy
\[
                         w_U,w_V\in\{1,\sqrt2\}.
\tag{5}
\]
The radial cut-moment law places all three path applications on
the horizontal axis. In particular the actual A-U point is
\[
                 p_A=(r_L-w_V-w_U)e_x,
\tag{6}
\]
and A lies wholly to its left. These identities retain every
side-normal mean and every diagonal transmitter alternative.

Since r_D<d and
\[
                  d<61/60,\qquad w_U+w_V\ge2,
\]
the center of A obeys
\[
                         (c_A)_x<-89/60.
\tag{7}
\]
Here the supporting half-width of A in any direction is at
least1/2. The simple inequalities r_D<d and d<61/60 follow
from r_D<7/10<9/10<d and
\[
                    R^2-\tfrac14\le\frac{1041}{256}
                                      <(121/60)^2.
\]

Every contained unit has center norm strictly less than
\[
                                M=91/60.
\tag{8}
\]
Indeed in its own axes its farthest corner has squared radius
at least |c|^2+|c|+1/2. Hence
|c|<=sqrt(R^2-1/4)-1/2<91/60.
Every boundary unit has center norm greater than5/4, because
|c|>=R-1/sqrt(2)>5/4; the latter follows from
29/40>1/sqrt(2).

The actual circle-resultant vectors of B,C sum to a strictly
western vector:
\[
                             F_B+F_C=-F_L.
\tag{9}
\]
This is the sum of the true equations of all six bodies, and
F_L is a positive multiple of e_x. Internal forces and every
actual mean cancel. No other circle force has been omitted.

## 3. A uniform angular obstruction for a balanced boundary pair

We prove the obstruction at exactly the metric scope needed by
(7)--(9). Let a unit A have
\[
                    c_A\cdot e_x<-89/60,\qquad |c_A|<M,
\]
and let physically touching boundary units B,C each touch A.
Assume their actual positive circle-resultants sum west.
These conditions are impossible.

Put
\[
                 \gamma=\arccos(4/5),\qquad
                 \vartheta=\arccos(9/25).
\tag{10}
\]
Every one of the three center radii is between5/4 and M.
For two such radii r,s the function
\[
                         f(r,s)=\frac{r^2+s^2-1}{2rs}
\]
is increasing in both variables on this rectangle: each derivative
has numerator at least 25/16+1-M^2>0. Since disjoint units have
center distance at least1, their center angle is therefore greater
than gamma, because
\[
 \cos(\hbox{angle})\le f(r,s)<1-\frac1{2M^2}<\frac45.
\tag{11}
\]
The last inequality uses M^2<5/2.

For an actual touching pair A,B or A,C, the center distance is at
most sqrt(2). Their center angle is less than pi/2, since
r^2+s^2>25/8>2. Consequently B and C each have a unique angular
lift within90 degrees of the center ray of A.

The A ray is within15 degrees of west. Indeed
\[
 \frac{-(c_A)_x}{|c_A|}>\frac{89}{91}>\cos(\pi/12).
\tag{12}
\]
For an exact comparison, cos^2(pi/12)=(2+sqrt(3))/4<15/16,
whereas (89/91)^2>15/16.

The one-body theorem in Section1 of
FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md puts every actual
positive circle resultant less than15 degrees from its body's
center direction, including both physical corner weights.
Since gamma>30 degrees, (11)--(12) imply the following.
If a boundary center is on the positive angular side of the
A ray, its circle resultant has strictly positive angular
coordinate from west and that coordinate is less than120 degrees.
If it is on the negative side, the corresponding coordinate is
strictly negative and greater than -120 degrees.

Thus two centers on the same side of the A ray would give two
circle resultants with transverse components of the same strict
sign. Their sum could not point west. B and C must lie on
opposite sides. Their actual minor center angle is consequently
greater than2gamma; it is the sum of their two gaps from A,
each less than90 degrees.

But every touching pair of boundary units has center angle
strictly less than vartheta. For clarity this bound follows
directly here: their center distance is at most sqrt(2), and
\[
 \frac{r^2+s^2-2}{2rs}>\frac9{25}
 \quad(5/4<r,s<M).
\tag{13}
\]
The expression is increasing in each radius on this rectangle,
and its value at r=s=5/4 is 9/25.
Finally
\[
                   \cos(2\gamma)=7/25<9/25=\cos\vartheta,
\]
so 2gamma>vartheta. This contradicts the actual B-C contact
and proves the uniform angular obstruction.

## 4. Entire attachment conclusion

Section1 covered every possible loaded status of the two internal
path vertices. Section2 retained both leaf types, both complete
transmitter widths and every actual support mean. Its cap and
global force identities meet every hypothesis of Section3, since
A,B,C are the actual positive triangle.

The entire six-body component (2) is therefore impossible.
All three arbitrary additional squares remain in the packing;
no completion-region assumption or motion was used. The only
normal conventions invoked are the already compatible strict
off-origin bridge convention and the established physical
certificate; no new normal selection is required.

This is one whole attachment of C1.3.b3. The other rooted
attachment layouts in SIX_BODY_CYCLIC_FRONTIER.md retain their
own whole-family obligations. An exact smaller component theorem
was not applied by deleting a positive bridge or body.
No numerical pose sampling, Lean compilation or CI is used.

