# An exact positive six-body control in the adjacent-root C4/S-S family

**Status: exact algebraic control; independent review pending.**
This is an actual six-square packing with a positive selected-compatible
C4/two-leaf stress at a squared radius strictly below \(1105/256\).
It is not a nine-square packing, and no three-square completion is
asserted. Its purpose is to show that the remaining original gate
M6.B4L2.C4.ADJACENT.LCD.SS cannot be closed by a core-only contradiction
that uses just its stated six-body geometry, forces and generic normal
conventions. A complete capacity argument for its three additional
physical units, or another hypothesis supplied by a whole minimizer,
is still necessary.

## 1. Exact radius and coordinates

Put
\[
 w=\sqrt{313},\qquad
 d=\frac{2w-11}{24},\qquad
 b=\frac{22-w}{24},\qquad
 q=1+(2-b)^2=\frac{1565+52w}{576}.
 \tag{1}
\]
Direct expansion gives
\[
 d^2=1+b^2,\qquad
 2d+4b=\frac{11}{4},\qquad
 q=(d+1)^2+\frac14.
 \tag{2}
\]
Also
\[
 1<d,\qquad 1/6<b<3/16,\qquad
                  \frac{17}{4}<q<\frac{1105}{256}.
 \tag{3}
\]
For the lower radius comparison,
\[
 q-\frac{17}{4}=\frac{52\sqrt{313}-883}{576}>0
\]
because \(\sqrt{313}>17\).
For the upper comparison,
\[
 \frac{1105}{256}-q
      =\frac{3685-208\sqrt{313}}{2304}>0,
\]
since both terms in the numerator comparison are positive and
\[
                    3685^2-208^2\cdot313=37593>0.
\]
The harmless decimal orientation is
\(b\approx0.17950808\) and \(q\approx4.31419082\);
none of the proofs below uses those decimals.

Take four axis-aligned unit squares
\[
 \begin{aligned}
 A&=[-1,0]\times[-b,1-b],&
 B&=[0,1]\times[-b,1-b],\\
 D&=[-1,0]\times[1-b,2-b],&
 C&=[0,1]\times[1-b,2-b].
 \end{aligned}
 \tag{4}
\]
Their chosen positive cycle is \(A-B-C-D-A\).
Let
\[
 p_- =(-1,-b),\quad p_+=(1,-b),\qquad
 e_\pm=p_\pm/d.
\]
These are unit directions by (2). Attach the two genuine radial S
leaves
\[
 L_\pm=p_\pm+[0,1]e_\pm+[-1/2,1/2]Je_\pm,
 \tag{5}
\]
with \(L_-\) attached to \(A\), and \(L_+\) to \(B\).

## 2. Full physical verification

The four units in (4) form a solid aligned \(2\times2\) rectangle
with disjoint open interiors. The roots \(A,B\) are strictly
circle-clear. Each upper unit has exactly one circle corner:
\[
                         z_D=(-1,2-b),\qquad z_C=(1,2-b).
 \tag{6}
\]
Their squared norms are \(q\); every other corner of either unit
has smaller squared norm.

The two outer corners of each leaf in (5) are
\[
                       z_{\pm,\tau}
                =(d+1)e_\pm+\frac{\tau}{2}Je_\pm,
                  \qquad \tau\in\{-1,1\}.
 \tag{7}
\]
Their squared norms are \(q\) by (2), while the two inner corners
have squared norm \(d^2+1/4<q\). Convexity of the disk proves full
containment for every square.

The vector \(e_-\) strictly exposes \(A\)'s southwest corner
\(p_-\); the vector \(e_+\) strictly exposes \(B\)'s southeast
corner \(p_+\). Each leaf lies beyond its corresponding support
line and intersects its own root exactly at that corner, which
is the relative interior point of the leaf's inner side.

The right leaf has first coordinate at least
\[
                         1-\frac{b}{2d}>0,
\]
so avoids the left root; the reflected statement handles the left
leaf. The two leaves lie in disjoint strict horizontal half-planes.
Every point of either leaf has vertical coordinate at most
\[
                         -b+\frac1{2d}<1-b,
\]
so both avoid the upper squares. These statements verify every
remaining pairwise nonoverlap. The diagonal point contacts at
\((0,1-b)\) are physical but have zero chosen stress.

## 3. All genuine positive forces and their actual means

Set
\[
                         \lambda=\frac{2-b}{b}>0.
 \tag{8}
\]
Use circle-force coefficients: a coefficient `k` denotes the actual
vector `k z`, and corresponds to the multiplier `k/2` in the
`2 lambda z` convention of PHYSICAL_CONTACT_STRESS.md.
Give each upper circle corner in (6) coefficient one. Its actual
circle force is therefore \(z_D\) or \(z_C\).
Give each of the two circle corners of either leaf the coefficient
\[
                         \eta=\frac{\lambda d}{2(d+1)}>0.
 \tag{9}
\]
The resulting leaf force is exactly
\[
                        F_{L_\pm}=\lambda p_\pm.
 \tag{10}
\]

Choose the following actual contact applications and positive
magnitudes. Normals are directed from the first listed square to
the second.

| Positive pair | Unit normal | Magnitude | Actual application |
| --- | --- | ---: | --- |
| \(A,B\) | \(e_x\) | \(\lambda\) | \((0,-b/2)\) |
| \(D,C\) | \(e_x\) | \(1\) | \((0,1-b/2)\) |
| \(A,D\) | \(e_y\) | \(2-b\) | \((-1/2,1-b)\) |
| \(B,C\) | \(e_y\) | \(2-b\) | \((1/2,1-b)\) |
| \(A,L_-\) | \(e_-\) | \(\lambda d\) | \(p_-\) |
| \(B,L_+\) | \(e_+\) | \(\lambda d\) | \(p_+\) |

All four shared-side means are in the relative interiors of their
actual common segments. They can be expressed as positive
convex combinations of the segment's two endpoint atoms. The two
leaf applications are the actual vertex/side singleton contacts.

For a direct check, use the outward-normal convention
\[
                 F_i+\sum_{j}\mu_{ij}n_{i\to j}=0.
 \tag{11}
\]
At \(A\), the three pair vectors sum to
\[
              \lambda(-1,-b)+\lambda(1,0)+(0,2-b)=0.
\]
At \(B\), reflect this identity horizontally. At \(D\), the
circle vector and pair vectors sum to
\[
                   (-1,2-b)+(1,0)+(0,-(2-b))=0.
\]
Again reflect for \(C\). At each leaf, the actual pair force is
the negative of (10), so (11) holds there as well.

Every circle force has zero origin torque. The two nonradial
pair torques at \(A\) cancel as
\[
             \lambda b/2-(2-b)/2=0,
\]
and those at \(D\) cancel as
\[
                 (2-b)/2-(1-b/2)=0.
\]
Horizontal reflection gives the two other root/upper equations.
The leaf pair forces are radial at \(p_\pm\), so have zero
origin torque. Thus all six exact force and torque equations hold.
Force balance also makes the torque about each body center zero.

All circle and contact magnitudes are strictly positive. Dividing
the entire certificate by its total circle weight normalizes it.
There are sixteen positive scalar atoms if the four interior shared
means are expanded to their endpoint atoms: eight shared-contact
atoms, two leaf-contact atoms, two upper circle atoms and four leaf
circle atoms. This is within the usual eighteen-atom six-body bound.

## 4. Selected-certificate compatibility and proper conclusion

The four positive block edges are actual shared sides, and the
leaf edges are vertex/side contacts whose side-owned normals strictly
expose the corresponding root vertex. No positive point-only
vertex/vertex edge is used. The free diagonal normals at the
four-square junction can satisfy every prelisted generic avoidance
while both diagonal multipliers remain zero. There is no crossing
positive pair to uncross.

Thus no contradiction follows from this core's exact positive
degrees, physical masks, shared means, force equations, torque
equations, normal selection, or sparsity bound. The positive
component is precisely the original adjacent-root C4 with both
upper block vertices loaded and both genuine leaves S.

The construction does not establish a stationary whole nine-square
packing, a least-radius minimizer, a canonical secondary minimum,
or even the existence of three further disjoint units. It leaves
the original nine-square completion gate open. It rules out
discarding those three physical completion units and attempting to
close this remaining family by a universal six-body core exclusion.
No numerical search, computational certificate, Lean build or CI
is used.

