# A tilted S articulation cannot meet a nonparallel hub through its own side

**Status: complete whole-interface hand exclusion; root and separate
independent full audits passed.** Use the exact graph, radius window,
common preselection and notation of
TIP_LEAF_BOWTIE_S_TILTED_DOMAIN.md. In particular
\[
 A=R_0+[0,1]u+[0,1]v,\quad R_0=D e_x,\quad
 u=(-a,-b),\ v=(-b,a),\quad a>b>0,
\]
\[
 \frac{91}{100}<D<\frac{61}{60},\qquad
 q_A=q e_x,\quad q>0,\qquad \sigma=D-q\ge0.
\tag{1}
\]
Assume the actual AH normal is the A-owned axis u, but H is not
parallel to A. The full domain theorem leaves both possible B
applications: its strict far A vertex and an A-owned v contact.
All B circle masks, all BH owners and every original mean remain.

**Theorem.** This entire interface is impossible. H is never treated
as loaded or as a degree-two body. The whole opposite C,E petal and
all three arbitrary completion squares are retained.

## 1. The actual hub vertex and incoming radial line

The AH support of H is a strict minimum-u vertex Q. The A-owned
normal line through the A concurrence fixes the actual point, in
A coordinates based at R_0, as (1,sigma b). In vector components
along u,v measured from the original circle origin this is
\[
                 Q=xu+yv,\qquad x=1-Da,\quad y=-bq<0.
\tag{2}
\]
Because H is not parallel to A, its two inward side vectors at Q
can be written
\[
 r=(\sin\psi)u+(\cos\psi)v,\qquad
 s=(\cos\psi)u-(\sin\psi)v,qquad0<\psi<\pi/2,
\]
\[
                              H=Q+[0,1]r+[0,1]s.
\tag{3}
\]
No angle relative to B is prescribed.

The parallel-input alternative at H is impossible at a strict
minimum-u vertex, by Section 2.1 of the domain source. Thus its
actual incoming concurrence exists and satisfies
\[
                       q_H=Q+t u\in(0,\infty)M,\qquad t\ge0,
                  \qquad M=F_C+F_E.
\tag{4}
\]
Put e=M/|M|. Equations (2),(4) give
\[
                              e\cdot v<0.
\tag{5}
\]
The conclusion (4) was proved there for both nonparallel and
parallel B forces; no physical radial B mask is being dropped.

For the genuine C,E petal write its root concurrence, when the two
root normals are nonparallel, as
\[
                         q_*=-\lambda M,\qquad\lambda>0.
\tag{6}
\]
Its actual root ports lie forward from q_* along their outward
normals. These are the full arbitrary-root-degree end-triangle
conclusions. We also use its complete common-face threshold39/40
and the two face-direction bounds in
END_TRIANGLE_FACE_RESULTANT_ANGLE.md.

## 2. A nonnegative inner s-height is already impossible

Write Q_s=Q·s and Q_r=Q·r. Suppose first Q_s>=0. Equation (4)
gives e·s>=0. If e·s>0, then q_*·s<0. Every point of H has
s-coordinate at least Q_s>=0. The behind-port equation therefore
gives a strictly positive s-component for every actual petal root
normal. Each such normal exposes the maximum-s side or one of its
endpoints. Both actual ports belong to that one side, whose height
Q_s+1>=1 contradicts END_TRIANGLE_HIGH_FACE_EXCLUSION.md.
For parallel petal normals the same conclusion follows immediately
from their common direction e and e·s>0.

If e·s=0, (4) forces Q_s=0 and t=0. Equation (5) then gives
e=-r and Q_r<0. Since x=Q_r sin(psi)<0, we have Da>1. The exact
bounds needed below already follow:
\[
 -\frac1{60}<x<0,\qquad
 b<\frac{11}{61}<\frac3{16},\qquad
 |y|<\frac{61}{320},\qquad |Q|<\frac15.
\tag{7}
\]
Indeed a>1/D>60/61 gives b<11/61, while q<D. The last inequality
follows by squaring the two displayed coordinate bounds.

The axis-resultant theorem puts both petal applications on the
minimum-r side. If the root normals are nonparallel, they are its
two strict endpoint normals; one application is Q. If they are
parallel, they both equal -r and origin torque makes the positive
weighted mean of their s-coordinates zero. Since Q_s=0 and all
those coordinates are nonnegative, both actual applications have
s-coordinate0 and equal Q. In either case a loaded tip contains Q,
contrary to |Q|<1/5<R-sqrt(2).

Consequently every remaining case has
\[
                              Q_s<0.
\tag{8}
\]

## 3. The only remaining petal face is the upper r-side

Since y<0, the identity Q_s=x cos(psi)-y sin(psi) and (8) imply
x<0. Thus all of (7) holds throughout the remaining domain. Also
\[
            Q_s\ge x>-\frac1{60},\qquad
            Q_r<0,\qquad |Q_r|<\frac15.
\tag{9}
\]
The maximum-s side has height1+Q_s>59/60>39/40 and therefore
cannot contain both actual petal applications.

We first rule out e·s<0. Equation (5) then forces e·r<0: otherwise
e·v=(e·r)cos(psi)-(e·s)sin(psi) would be positive. The functional
e is strictly maximized on H at Q. The complete maximizing-port
statement in END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md, Section 4,
therefore makes Q an actual petal application, contrary to (7).
That statement's sole perpendicular-root-axis exception is already
excluded for two loaded tips by the full perpendicular-contact
theorem. Parallel root normals expose Q directly.

Hence e·s>=0. The following full root-feature cover is useful here.
An H-owned -s normal is impossible by the unit-triangle nonobtuse
lemma and M·s>=0. An H-owned +s normal puts the other application
on the same maximum-s side, except for the already excluded
perpendicular pair. If an H-owned normal is instead ±r, both
applications lie on that ±r side. In the nonparallel case its
actual ±r application has s-coordinate q_*·s<=0. In the parallel
case, which requires e=±r, origin torque makes at least one actual
application have nonpositive s-coordinate.

If neither root normal is H-owned, their applications are strict
vertices. Opposite vertices are impossible for a physical unit
triangle. A common vertex with M·s>=0 is on the maximum-s side
unless M·s<0; the latter has just been excluded. Distinct adjacent
vertices either lie on the maximum-s side, on the minimum-s side
(whose strict normal signs would force M·s<0), or on one ±r side.
In the last case one of them has s-coordinate Q_s<0.

After the maximum-s exclusion, this exhausts every root owner and
free normal: both actual ports lie on one ±r side, and at least one
such port has s-coordinate in [Q_s,0]. The minimum-r side is
impossible, because that particular port would have
\[
                        |p|^2\le Q_s^2+Q_r^2=|Q|^2<\frac1{25}.
\tag{10}
\]
A loaded tip cannot contain it. Thus the common face must be the
maximum-r side. Its height is
\[
                         P=1+Q_r=1-w,\qquad
                          0<w=-Q_r<\frac15.
\tag{11}
\]
Both root normals have nonnegative r-component, and the surviving
face cover has already removed both +s and -s axes. At least one
r-component is therefore strictly positive, so M·r>0.
If e·s=0, this would give e=r, contrary to (5). We have therefore
also proved
\[
                              e\cdot r>0,\qquad e\cdot s>0.
\tag{12}
\]
This routing preserves every side-mean endpoint and every free
point-contact normal; it is not a choice of a convenient root side.

## 4. Two quantitative angle steps contradict the high face

Put delta=Da-1=-x, so 0<delta<1/60. Rewriting (2) in the r,s
frame gives
\[
            -\delta=Q_r\sin\psi+Q_s\cos\psi
                       =-w\sin\psi+Q_s\cos\psi.
\]
Since Q_s<0,
\[
                          \sin\psi<\frac{\delta}{w}.
\tag{13}
\]
On the other hand (5),(12) give
\[
                    e\cdot r<\sin\psi.
\tag{14}
\]
Indeed the direction e lies strictly on the negative-v side of u,
whereas r makes angle pi/2-psi with u.

Equation (11) has P>4/5. The first whole common-face direction
theorem therefore gives e·r>1/2. Equations (13)--(14) imply
\[
                           w<2\delta<\frac1{30},
                    \qquad P>\frac{29}{30}.
\tag{15}
\]
Apply the second direction theorem on that same actual face. It
gives e·r>4/5, whence
\[
                           w<\frac54\delta<\frac1{48},
                    \qquad P>\frac{47}{48}>\frac{39}{40}.
\tag{16}
\]
Both actual petal applications are on this side, so (16) contradicts
the complete high-face exclusion.

This proves the whole AH-A-owned/H-nonparallel alternative. All
original H forces, B physical masks, circle-weight endpoints and
shared means remained throughout. There is no additional normal
selection, completion motion or sampled-angle premise.
