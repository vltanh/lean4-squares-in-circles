# A free articulation contact opposite a shared boundary side

**Status: complete hand selection and pressure implication; root and
separate independent full hand audits passed.** In the declared radius window,
consider an actual triangle A--B--C--A with B,C positive degree-two
circle-loaded tips. Suppose BC is a positive-length shared side
and AC is a free point-only vertex/vertex contact. Then a compatible
certificate can be selected so that
\[
                             c_A\cdot(F_B+F_C)>0.
\tag{1}
\]
Every shared-side application remains its actual weighted mean.
The proof excludes the two-unique-tip mask by finite selection
and treats the remaining radial-tip mask by a direct pressure
bound. It does not replace a physical two-corner square by a
unique-corner square.

## 1. Two elementary contact facts

### 1.1. A free vertex application is within one unit of the other application

Let Q be the free AC application, a vertex of A, and let P be
the actual AB application. Then
\[
                                  |P-Q|\le1.
\tag{2}
\]
If A owns AB, the owned-normal triangle lemma makes its normal
have positive scalar product with the strict A vertex normal at
Q. Hence Q lies on that AB support side and P is on the same
unit side. This also handles an arbitrary shared-side mean.

Otherwise P is an A vertex. The same vertex gives distance0,
and an adjacent vertex gives distance1. Opposite vertices are
impossible by the support-span argument in
BOWTIE_TIP_OWNED_PRESSURE.md, Section1: the two strict A vertex
normals have negative scalar product, their normal separation
across A is at least1, and the other unit's strict support span
is below1. That would prevent the physical BC contact.
This proves (2) for every actual contact feature.

### 1.2. Two shared sides and one free point form an impossible aligned L

If AB is a shared side too, all three frames agree. Since AC
is a single vertex/vertex contact, their center displacement has
both own components of absolute value1. Requiring B to share
a side with each fixes it at one of the two intervening unit
positions. After rotation/reflection write the whole family as
\[
\begin{split}
 A&=[x-1,x]\times[y-1,y],\\
 B&=[x,x+1]\times[y-1,y],\\
 C&=[x,x+1]\times[y,y+1].
\end{split}
\tag{3}
\]
These are coordinates about the original circle origin; x,y
are not set to zero.

Both B,C touch the same circle. Their horizontal contributions
to the maximum squared corner norm agree. Their vertical maxima
agree only when y=0: for y>0 the C maximum is strictly larger,
and for y<0 the B maximum is strictly larger. Put
X=sqrt(R^2-1)>1. The common horizontal interval must therefore
be entirely positive or entirely negative, with far endpoint
of absolute value X.

The B force is F_B=mu e_x-gamma e_y. Its positive first
component forces the positive interval, so x=X-1>0. The free
AC normal n has both components positive. At C the origin
torque equation is
\[
                        \nu x n_y+\gamma\xi=0,
                 \qquad\xi\in[x,x+1],
\tag{4}
\]
where xi is the actual BC shared-side mean. Both terms are
positive, a contradiction. This excludes the entire aligned L,
independently of individual circle weights or the AB mean.

Henceforth AB is a singleton.

## 2. A radial free tip cannot be opposite a shared side

If C has two physical circle corners, Section1 of
BOWTIE_RADIAL_FREE_INTERFACE_PRESSURE.md applies directly.
Its free AC vertex must be an inner radial vertex. The origin
torque, the strict unit support span and the radial-inner-face
boundary-neighbor obstruction force BC to be a singleton at
the other inner vertex. This contradicts the present shared BC.

Thus C has one physical circle corner. If B is radial and AB
is also free, the same local statement applied to B gives the
same contradiction. This conclusion needs only the radial tip's
two positive forces and the actual triangle contacts; no
degree-two assumption is made about A.

## 3. Both tips unique: a compatible block selection removes the free edge

Assume B,C each have exactly one physical circle corner. Their
shared side gives a common orthonormal frame. Their two exterior
applications to A are fixed singleton points. We first dispose
of two degeneracies needed for the selection argument.

### 3.1. The two exterior applications are distinct

Suppose both equal p. The free AC contact makes A,C have
vertices at p. If p were in the relative interior of a B side,
the B half-plane and the A,C quadrants would fill the whole
turn. The A,C quadrants would then share a unit side, contrary
to free AC. Therefore p is a B vertex too. Since B,C are
parallel and share a positive segment with a common endpoint,
they share a full unit side.

As in Section1.2, equality of their two circle radii makes that
shared side lie on y=0. Reflect horizontally if necessary so
their horizontal interval is [X-1,X], X=sqrt(R^2-1)>1. Let B
be the lower square and C the upper one. The point p is one
of the two endpoints of their shared side.

If p is the outer endpoint (X,0), both inward normals from A
into the tips have negative x-component. Their sum cannot be
the tips' total circle-force vector, whose x-component is
positive. If p=(X-1,0), the inward B normal n has n_y<0.
B's torque would require
\[
                  \mu(X-1)n_y=\gamma\xi,
                    \qquad\xi\in[X-1,X],
\tag{5}
\]
with a negative left side and positive right side. Both
possibilities are impossible. Thus the exterior points are
distinct.

### 3.2. A free exterior vertex is not radial-collinear with its circle corner

Take either tip S, its unique circle corner z and a free
exterior vertex p. In its own square frame, the only non-circle
vertex collinear with z is the radial-D inner vertex:
\[
             z=(R/\sqrt2,R/\sqrt2),\qquad
             p=(R/\sqrt2-1,R/\sqrt2-1).
\tag{6}
\]
The shared BC contact cannot use an outer face of this square,
since its support R/sqrt(2) is greater than R-1. It therefore
uses an inner face containing p.

At S, take torque about p. Its circle force has zero moment
about p by collinearity, and its exterior pair force acts at p.
Thus the shared-side force at its actual mean r must satisfy
det(r-p,e)=0, where e is that side's normal. But r-p is
tangential to the side, so r=p. This makes two boundary
squares share a point of norm R-sqrt(2), impossible by the
strict boundary-contact inner-radius theorem. Consequently
\[
                              \det(p,z)\ne0
\tag{7}
\]
for every free exterior vertex in a positive candidate.

### 3.3. Two virtual-work identities with all means retained

Label the free exterior application p on tip1, and the other
application q on tip2. Write z_1,z_2 for their unique physical
circle corners, e for the unit shared-side normal, and n,m for
the outward normals from the two-tip block toward A. In the
common square frame every component of z_i has nonzero absolute
value, at least1/2. Define
\[
       w_1=Jz_1,\qquad
       \kappa=\frac{e\cdot Jz_1}{e\cdot Jz_2}\ne0,
                      \qquad w_2=\kappa Jz_2.
\tag{8}
\]
The pure translations w_1,w_2 do zero work on the two radial
circle forces and on the internal shared-side force, because
e dot(w_2-w_1)=0. The last equality is independent of the
actual shared-side mean. Rigid rotation of the whole block
about the origin also does zero internal and circle work.

For positive exterior magnitudes mu,nu, the two necessary
identities are therefore
\[
 \mu\det(p,n)+\nu\det(q,m)=0,\qquad
 \mu(n\cdot w_1)+\nu(m\cdot w_2)=0.
\tag{9}
\]
Eliminating their magnitudes gives
\[
 D(n,m)=\det(p,n)(m\cdot w_2)
                  -\det(q,m)(n\cdot w_1)=0.
\tag{10}
\]

If m is parallel to z_2, no positive candidate exists: the
tip2 circle force and its exterior force would be parallel to
z_2, while its remaining positive shared-side force is a side
axis and cannot be parallel to that circle corner. Otherwise
m dot w_2 is nonzero. As a linear function of the free n,
(10) has coefficient
\[
                       W=(m\cdot w_2)Jp-\det(q,m)Jz_1.
\tag{11}
\]
Equation(7) and m dot w_2!=0 make W nonzero. Thus at most two
unit directions in the free interval can satisfy (10).

If m is free too, choose it nonparallel to z_2 to see that the
two-parameter determinant is not identically zero. Section3.1
ensures p!=q, so their junction parameters are independent,
including the existing matched opposite-pair convention at a
four-square junction.

Prelist the finitely many physical triangles, shared pairs,
unique-corner masks and fixed exterior applications. Choose the
free normals outside these proper analytic zero sets, together
with all previously selected finite exclusions. The collinear
and parallel exceptions above have no positive candidates and
need no exclusion. Uncrossing preserves surviving free normals
and only adds actual shared-side forces; every possible final
shared pair was prelisted. Thinning only deletes atoms.

This is a simultaneous pre-certificate selection, not a change
to an extracted normal. It removes every surviving free AC in
the entire two-unique-tip shared-side mask, with its full
application interval retained.

## 4. The remaining radial B / unique C mask

By Section2, AB cannot be free here. By Section1.2 it cannot
be a shared side. Thus AB is owned. Rotate and reflect the
radial B square and its shared side so
\[
\begin{split}
 B&=[H,H+1]\times[-1/2,1/2],\\
 C&=[Z-1,Z]\times[-3/2,-1/2],\\
 Z&=\sqrt{R^2-9/4}=\sqrt{(H+1)^2-2},\\
 &\qquad H<Z<H+1,\quad 5/4<Z\le23/16,\quad H>9/10.
\end{split}
\tag{12}
\]
Indeed a radial inner side cannot face a boundary neighbor and
an outer side cannot face a contained unit, so BC uses a
tangential side. The radius equation forces C's far horizontal
coordinate to have magnitude Z. Its negative interval cannot
overlap the positive interval of B, giving exactly (12).
Write xi in [H,Z] for the actual BC application mean.

The unique C circle corner is
\[
                               z_C=(Z,-3/2).
\tag{13}
\]
Let gamma>0 be the BC magnitude, directed from B to C as
-e_y, and let nu m be the force into C from A. Since
F_C=nu m-gamma e_y has positive x-component, m_x>0.
Thus the free AC vertex is one of the two left vertices of C.
The lower-left one has distance strictly greater than1 from
every B point: its vertical separation is at least1 and its
horizontal separation at least H+1-Z>0. This contradicts
Section1.1. Consequently
\[
                              Q=(Z-1,-1/2).
\tag{14}
\]

### 4.1. The complete owned AB feature cover

The C tangent quadrant at Q points right and down. Since A
also reaches B strictly to the right of Q, its two inward
unit axes at Q have the form
\[
                  u=(a,b),\quad v=(-b,a),\qquad
                 a,b>0,\quad a^2+b^2=1.
\tag{15}
\]
To justify the full cover, any A tangent quadrant with a point
to the right of Q must meet the right half-plane; avoiding
C's open right/down quadrant then puts it in the upper
half-plane with the axes displayed. At a=0 A never reaches B;
at b=0 it shares a positive segment with C. Both endpoints
are incompatible with the hypotheses.

The B lower-inner vertex (H,-1/2) is not in A, since every A
point except Q has y>-1/2. The upper-inner vertex (H,1/2) is
more than1 from Q, so cannot be an A-owned AB application by
(2). The two outer vertices are circle points and cannot be
shared. This excludes an A-owned AB axis.

A B-owned contact cannot use the outer radial face, by width.
The lower tangential face would put all of A below -1/2,
contrary to (15). The upper tangential face would put all of
A above1/2, contrary to (14). Thus the only possible owned
AB contact is a relative interior point of B's inner radial
face, with normal e_x from A into B. Let its magnitude be
mu>0. The exact B force is
\[
                                F_B=(\mu,\gamma).
\tag{16}
\]
Both circle weights on B are retained. Their radial-S
coordinates give
\[
                              \mu\ge2(H+1)\gamma.
\tag{17}
\]

### 4.2. Uniform center and force bounds

Write c_A=(x,y). Contact with B and the square half-diagonal
give
\[
 x\ge H-1/\sqrt2>19/100.
\tag{18}
\]
Here use 1/sqrt(2)<71/100. Equation(15) gives
\[
          y=-1/2+(a+b)/2>0,\qquad
          y\le(\sqrt2-1)/2<5/24.
\tag{19}
\]
Write F_C=kappa z_C, kappa>0. Taking torque about Q in
C's force equation, with its actual shared-side mean xi,
gives the exact identity
\[
                 \kappa(3/2-Z)=\gamma(\xi-Z+1),
             \qquad\kappa\le\frac{\gamma}{3/2-Z}.
\tag{20}
\]
The denominator is positive by Z<=23/16. Put
\[
                      G=c_A\cdot z_C=Zx-3y/2.
\tag{21}
\]
Using (18)--(19) and Z>5/4 gives the uniform lower bound
G>-3/40. The pressure is exactly
\[
                  c_A\cdot(F_B+F_C)=\mu x+\gamma y+\kappa G.
\tag{22}
\]

If Z<=4/3, then kappa<=6gamma by (20). Also (17)--(18)
give mu x>(361/500)gamma. Thus, whether G is negative or
positive,
\[
 c_A\cdot(F_B+F_C)
       >\left(\frac{361}{500}-\frac9{20}\right)\gamma
        =\frac{34}{125}\gamma>0.
\tag{23}
\]

If Z>=4/3, then H>=sqrt(34)/3-1. The monotonicity of
Z(H-1/sqrt(2)), together with (18)--(19), gives
\[
 G\ge\frac43\left(\frac{\sqrt{34}}3-1-\frac1{\sqrt2}\right)
          -\frac34(\sqrt2-1)
       =\frac{16\sqrt{34}-21-51\sqrt2}{36}>0.
\tag{24}
\]
For the last exact comparison, square the positive quantities:
16sqrt(34)>21+51sqrt(2) follows from
3061>2142sqrt(2), and
3061^2-2(2142)^2=193393>0. Every term in (22) is now
positive. This completes the whole radial B mask, with the
full interval H<=xi<=Z and every B circle-weight split.

## 5. Exhaustion

A free AC at a radial C is incompatible with shared BC.
For a unique C, a unique B is excluded by the compatible
two-tip block selection, with aligned and coincident exterior
degeneracies handled separately. If B is radial, AB cannot
be free or shared, its complete owned-feature cover leaves
exactly the geometry of Section4, and the pressure is positive
throughout its full radius and mean domain.

This proves (1) for the entire shared-BC/free-AC interface.
Together with the radial-free and side-owner pressure sources,
it supplies the final free-interface input for the end-triangle
pressure theorem. It does not itself change any coarse-cell
count. All completion squares are retained. No numerical pose,
Lean compilation, CI or post-extraction normal change is used.
