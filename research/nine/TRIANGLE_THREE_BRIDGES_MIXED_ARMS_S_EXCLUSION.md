# A direct S leaf and a two-edge arm cannot share a triangle root

**Status: complete whole-leaf-type hand exclusion; root and separate
independent full hand audits passed.** Work in
\[
                       79/40\le R\le\sqrt{1105}/16.
\tag{1}
\]
The exact positive graph is the triangle A,B,C, a direct S leaf
\(L_S\) at A, and the arm \(A-U-L\). B,C have exact positive
degree two. A has degree four; both additional forces remain in
every equation. The other three physical squares remain present.

**Theorem.** This entire direct-S-leaf alternative cannot occur in
a nine-square minimizer. Every original arm leaf type and width,
physical B/C circle mask, contact owner and actual side mean is
retained. The critical-radius case uses the completed physical
P capacity theorem where it is needed; all other cases exclude
the core itself.

## 1. The full arm and root geometry

Put
\[
        d=\sqrt{R^2-\tfrac14}-1,\qquad
        r=R-\sqrt2,\qquad \varepsilon=\max(d-1,0)<1/60.
\tag{2}
\]
U is physically circle-clear as the neighbor of its genuine leaf.
Its exact degree two gives width \(w\in\{1,\sqrt2\}\).
Rotate that leaf direction east. Its actual applications are
\(r_Le_x\) and
\[
                p_{AU}=xe_x,\qquad x=r_L-w,\qquad
                A\subset\{x_1\le x\},\qquad r_L\in\{r,d\}.
\tag{3}
\]
The direct S leaf makes A meet \(D_\varepsilon\), by the
unit inward segment from its radial support \(d e_S\).
Consequently \(x\ge-\varepsilon\).

If \(d<1\), then \(\varepsilon=0\) and every alternative in
(3) has x<0, impossible. At \(d=1\), only S/width1 gives
x=0. At \(d>1\), every alternative except S/width1 has
\(x< -\varepsilon\): the D/width1 value is below \(-3/10\),
the S/diagonal value is below \(-1/3\), and the D/diagonal
value is still smaller. Thus the whole arm cover is
\[
                  d\ge1,\quad L\text{ is S},\quad w=1,
                    \quad x=\delta:=d-1\in[0,1/60).
\tag{4}
\]
U is aligned with the arm, and its vertical interval contains0.
No actual mean is fixed beyond the radial applications (3).

For the moment take \(\delta>0\). A must be aligned with the
arm as well. If its right support \((\delta,0)\) were a vertex
of a tilted frame, the origin would be interior. In its own
coordinates the near vertex has norm \(\delta\), its two
adjacent vertices have squared norms below \(1+\delta^2<d^2\),
and its opposite vertex has squared norm at least
\(2+\delta^2-2\sqrt2\delta>d^2\).
All four side distances from0 are below1, whereas d>1.
There is no radial support point of norm d for the direct
S leaf. This excludes the entire tilted alternative.

Write the aligned root as
\([\,\delta-1,\delta\,]\times[l,l+1]\), with \(l\le0\le l+1\).
No side-interior radial support has radius d>1. A right-hand
vertex would require \(y^2=d^2-\delta^2=1+2\delta>1\), also
impossible. A left-hand vertex must have
\[
                             y^2=d^2-(1-\delta)^2=4\delta.
\]
The two signs cannot both be vertices, since \(4\sqrt\delta<1\).
After reflection the complete high-radius root is
\[
 \begin{gathered}
 X=1-\delta,\qquad Y=2\sqrt\delta,\qquad h=1-Y,\\
             A=[-X,\delta]\times[-h,Y],\qquad
                   e_S=(-X,Y)/d .
 \end{gathered}
\tag{5}
\]
In particular
\[
  X>59/60,\qquad 0<Y<13/50,\qquad h>37/50>11/15,
                   \qquad \delta^2+h^2<1.
\tag{6}
\]
The last inequality follows from
\(\delta^2+h^2=1-4\sqrt\delta+4\delta+\delta^2<1\)
throughout \(0<\delta<1/60\).

B,C are loaded, since each has exact degree two and its two
neighbors physically touch. A is physically circle-clear,
as otherwise A,B,C would be a boundary triangle. Let M be
the sum of their two true circle resultants. Exact bridge
cuts and the full A equation give
\[
                 M=-\alpha e_S-\beta e_x,
                        \qquad \alpha,\beta>0.
\tag{7}
\]
Its vertical component is strictly negative.

Whenever A's two triangle normals are nonparallel,
END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md gives
\[
                        q_A=-t e,\qquad t>0,\qquad
                          e=M/|M|,\qquad(q_A)_y>0.
\tag{8}
\]
Every actual root port lies in its outward-normal direction
from \(q_A\), and one such port maximizes the M support.
All these are whole end-triangle implications allowing
A's two additional positive forces.

## 2. A uniform small-transverse boundary-tip screen

We record the complete single-tip estimate needed below.
It is used only when \(R^2>17/4\), so d>1.

Suppose a boundary unit T has a proper radial concurrence of
its two nonparallel positive pair forces: in particular its unique-circle
case has \(q=\tau z\), \(\tau>0\), at its physical circle
corner z, and an actual inward contact normal n and point p
obey
\[
                             q=p+\ell n,\qquad\ell\ge0.
\tag{9}
\]
Assume, in the orthonormal coordinates \((n,Jn)\),
\[
 p=(H,V),\qquad
       11/15<H<1,\quad 0\le V\le1/60,\quad |p|<1.
\tag{10}
\]
Then no such boundary T exists. A negative transverse
coordinate is handled by reflection.

First, a physical two-circle-corner square is radial S and
every one of its points has norm at least d>1. It cannot
contain p. Thus the physical mask is unique, regardless
of individual positive-weight descriptions. By (9),
\[
                 z_n>0,\qquad z_t\ge0,\qquad
                         \frac{z_t}{z_n}\le\frac VH.
\tag{11}
\]

If n is a T side axis, the farthest corner lies on its
opposite n face, since H>0. Hence \(z_n=H+1<2\).
Equation (11) gives \(z_t<1/22\), so
\[
                         |z|^2<4+1/484<17/4<R^2.
\]
This includes every actual relative-side-interior or endpoint mean.

Otherwise p is the strictly exposed minimum-n vertex of T.
Its inward side vectors can be written
\[
                   u=(a,b),\qquad v=(b,-a),
                   \qquad a,b>0,\quad a^2+b^2=1.
\]
The corner p itself is not on the circle by (10).
For \(z=p+u\), (11) gives \(Hb\le Va\), so
\(b<1/44\), \(z_n<2\), and \(z_t<1/60+1/44=13/330\).
This again makes \(|z|^2<17/4\).
For \(z=p+v\), nonnegativity in (11) gives \(a\le V\);
then \(z_n<2\), \(0\le z_t\le1/60\), with the same contradiction.

For the opposite corner put \(S=a+b\), \(K=b-a\).
Equation (11) gives
\[
                      -V\le K\le(V/H)S,\qquad |K|<3/88.
\]
Thus \(S=\sqrt{2-K^2}>7/5\), and
\[
                            z_n=H+S>32/15>R.
\]
Every corner and every contact feature has been exhausted.
This proves the screen. It has not assumed a frame at T
or replaced its actual mean.

The proper concurrence hypothesis (9) is available at both
B,C because each has the other as a boundary neighbor.
It is the all-mask lemma of
TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md, Lemma 2.1.

## 3. Three entire root-owned sides are impossible

Continue in the high-radius chart (5) and assume nonparallel
root forces.

An A-owned top normal has positive dot product with M by
the unit-triangle nonobtuse-normal lemma. This contradicts
\(M_y<0\).

An A-owned left normal puts its boundary tip center in
\[
                  c_x<-89/60,\qquad |c|<91/60.
\]
Consequently \(|c_y|<\sqrt{10}/10<1/3\), and its center
direction is less than15 degrees from west:
\[
             |c_y/c_x|<20/89<1/4<2-\sqrt3.
\]
The actual direct-S leaf center is also less than15 degrees
from west. Indeed
\[
                 Y/X<78/295<4/15<2-\sqrt3,
\]
using (6), and \(\sqrt3<26/15\) proves the last strict
comparison. These two distinct boundary centers would be
less than30 degrees apart, contrary to the strict
40-degree center separation. Thus the whole left side,
with every possible actual mean, is excluded.

For an A-owned right normal, its horizontal line through
(8) puts the actual port at
\[
                         p=(\delta,(q_A)_y),\qquad
                              0<(q_A)_y\le Y.
\]
The tip's proper radial concurrence is
\(q_T=p+\ell e_x\), \(\ell\ge0\), so both its coordinates
are positive and \((q_T)_y\le Y\).
Moreover
\[
                                  |q_T|\ge r.
\tag{12}
\]
For a unique physical circle corner the proper concurrence
lies inside the tip. For a physical radial S mask the
normal-line calculation in the cited proper-concurrence lemma
gives concurrence radius at least d. Both prove (12).

Here \(R>\sqrt{17}/2>103/50\) and
\(\sqrt2<71/50\), so \(r>16/25\).
The angle \(\eta\) of \(q_T\), hence of the actual circle
resultant, from east satisfies
\[
                        \sin\eta<Y/r<13/32.
\]
It is less than25 degrees. One elementary exact comparison is
\[
 \sin25^\circ
   >\sin30^\circ-\pi/36
   >\frac12-\frac{11}{126}
   =\frac{26}{63}>\frac{13}{32},
\]
using the derivative bound \(|(\sin)'|\le1\) and \(\pi<22/7\).
Every boundary resultant is less than15 degrees from its
body center. This tip center would therefore lie less than
40 degrees from the actual east S-leaf center, again
contradicting the strict center-separation theorem.

Thus top, left and right A-owned normals are all excluded,
including every shared-side mean.

## 4. The complete remaining point and bottom-side cover

The upper-right vertex \((\delta,Y)\) has norm below r,
so no boundary tip can contain it. In fact
\(\delta^2+Y^2<1/3600+1/15<1/4<r^2\).

The upper-left vertex \((-X,Y)=d e_S\) is the inner-face
midpoint of the actual direct S leaf. No other boundary
unit can contain it: at that relative-side-interior point
of the leaf its supporting normal is forced to be the
inward radial side normal, and the shallow inner-face
boundary-neighbor screen of C7_FORCE_POLYGON.md, Lemma 2.1,
makes the other unit circle-clear.

Every surviving non-A-owned root normal therefore strictly
exposes one of the two bottom vertices
\[
                          P_L=(-X,-h),\qquad
                          P_R=(\delta,-h).
\tag{13}
\]
Two nonparallel ports cannot both be the same vertex:
their concurrence would be that vertex with negative height,
contrary to (8). The remaining entire root interface consists
of these vertices and possible A-owned bottom-side means.

We prove that any surviving strict southeast port at \(P_R\)
satisfies the screen in Section 2. Write
\[
 \begin{split}
 e&=(\sin\theta,-\cos\theta),
                      &&-\pi/2<\theta<\pi/2,\\
 n_R&=(\sin\phi,-\cos\phi),
                      &&0<\phi<\pi/2,\\
 \beta_0&=\arctan(\delta/h).
 \end{split}
\]
The actual proper root line says
\[
                              P_R+t e=\ell n_R,\qquad\ell>0.
\tag{14}
\]
Hence \(\phi\) lies between \(\beta_0\) and \(\theta\).

If \(M_x\le0\), then \(\theta\le0\), and (14) immediately
gives \(0<\phi\le\beta_0\).
If \(M_x>0\), \(P_R\) is the unique maximizing point for M
and hence is an actual root port. By Sections 3--4 the
other normal is a bottom axis or a strict southwest normal.
Its positive combination with \(n_R\) is e, so
\(0<\theta<\phi\). Combining this strict order with (14)
again gives
\[
                              0<\phi\le\beta_0.
\tag{15}
\]
This argument preserves the actual normal and does not
replace it by the vertical axis.

In the \((n_R,Jn_R)\) frame the coordinates of \(P_R\) are
\[
              H=\delta\sin\phi+h\cos\phi,\qquad
              V=\delta\cos\phi-h\sin\phi.
\]
On (15), the first expression increases from h and the
second decreases from \(\delta\) to0. Thus
\[
           h\le H\le|P_R|<1,\qquad 0\le V\le\delta<1/60.
\tag{16}
\]
Equation (6) supplies \(H>11/15\). Section 2 excludes the tip
at this entire strict southeast port.

If an A-owned bottom port exists and \(M_x\le0\), its actual
point is \(((q_A)_x,-h)\) with
\(0\le(q_A)_x\le\delta\). Its inward-tip normal is vertical
down, so Section 2 applies directly. If instead \(M_x>0\),
the maximizing-port statement already forces the excluded
southeast port at \(P_R\). Thus every bottom-side mean is
excluded as well.

With no bottom-side mean, the only possible two nonparallel
ports would be the two distinct vertices in (13); their
right-hand port has just been excluded. This closes the
entire nonparallel root interface.

## 5. Parallel root forces, including coincident endpoint means

Opposite root normals are impossible because B,C touch.
If their common direction is not an A side axis, it exposes
one bottom vertex. Both actual root applications coincide
there. Their proper boundary-tip concurrences lie on the
same line in that direction; their connecting BC force is
then parallel too (or their radial resultant directions
coincide). This contradicts the full proper boundary-tip
lemma, exactly as in the parallel branch of
TRIANGLE_THREE_BRIDGES_MIXED_ARMS_D_EXCLUSION.md.

The only side-axis direction compatible with \(M_y<0\)
and the preceding left/right exclusions is vertical down.
Let the two actual bottom-side means have coordinates
\((x_B,-h),(x_C,-h)\). The zero sum of their origin moments
gives a positive weighted sum of \(x_B,x_C\) equal to0.
If both coordinates are0, the two proper tip concurrences
have the same radial direction, impossible for distinct
boundary bodies. Otherwise one coordinate is strictly
positive and at most \(\delta\). Section 2 excludes that
tip at the actual mean. This covers the entire parallel
domain, including all endpoint values.

Thus every \(\delta>0\) candidate is excluded.

## 6. The entire critical-radius endpoint

Now let \(d=1\), so \(R^2=17/4\). Section 1 forces the east
S leaf and width-one U, with bridge application0. Hence
\(A\subset\{x\le0\}\), \(0\in A\), and U is an aligned
unit in \(0\le x\le1\), whose vertical interval contains0.

If the direct S leaf points west, its support point is
\((-1,0)\). Width in the horizontal direction is then at
most1, so A is aligned:
\[
                         A=[-1,0]\times[l,l+1],
                              \qquad -1\le l\le0.
\]
Together with U and the actual east and west S terminals
this is precisely the full four-square P skeleton, with
both slider heights in \([-1/2,1/2]\).
P_ALL_COMPLETION.md excludes its completion to nine.
All five other physical units, including B,C, are retained
in that theorem's premise.

Otherwise A has0 at a vertex, and its direct S leaf points
along one of its inward unit side vectors u. To verify this
cover, a relative-side-interior zero point with right support
normal east makes A aligned; its sole radial support of
radius1 is then west. At a zero vertex the only norm-one
radial supports are the two adjacent vertices, in their side
directions; the opposite vertex has norm \(\sqrt2\).

Write
\[
                      A=[0,1]u+[0,1]v,\qquad
                 (u)_x=-a,\quad(v)_x=-b,
                    \quad a\ge0,\quad b>0.
\tag{17}
\]
The strict sign b>0 is exactly the non-west alternative.
The actual external forces are \(\alpha e_x+\beta u\),
so in this own frame the two-tip resultant satisfies
\[
                                M_v=\alpha b>0.
\tag{18}
\]

If the root forces are nonparallel, their genuine concurrence
has \(v\)-coordinate strictly negative by (8).
An A-owned u-axis normal has a force line at that negative
v coordinate, outside A. An A-owned \(-v\) normal has
negative dot product with M, forbidden by the unit-triangle
nonobtuse lemma.

The vertex0 cannot meet a boundary tip. The vertex u is the
actual direct leaf's inner-face midpoint and is excluded
by the same inner-face boundary-neighbor screen as before.
A strictly exposed contact at \(u+v\) has normal with two
positive own components, giving support strictly greater
than1=d, impossible for any contained unit.

Only the vertex v and the A-owned \(+v\) side remain.
A tip beyond the latter side has support height1=d and
must be the unique radial S square \(S(v)\), by the sharp
support equality theorem. Any other nonparallel tip would
then have its root port at v, the inner-face midpoint of
that actual \(S(v)\), again impossible for a boundary unit.
Two vertex-v applications would have concurrence v, contrary
to its negative v coordinate. Thus the whole nonparallel
critical domain is excluded.

If the root forces are parallel, their common direction has
positive v component by (18). A strict vertex direction
again gives coincident root ports, excluded by the proper
boundary-tip argument of Section 5. The only remaining
axis is \(+v\), whose support height1 makes both tips the
same radial S square. This is impossible.

The non-west critical alternative is therefore excluded
as a core. Along with the P completion exit for the west
alternative, this handles the full \(d=1\) endpoint.

The proof now covers every radius, arm type, root frame,
B/C mask, contact owner and actual mean of the direct-S
leaf alternative. Together with the D companion it closes
the entire same-root direct-leaf plus two-edge-arm attachment.
No numerical pose sampling, secondary minimizer, Lean or CI
is used.

