# A direct D leaf and a two-edge arm cannot share a triangle root

**Status: complete whole-leaf-type hand exclusion; root and separate
independent full hand audits passed.** Work in the declared
window \(79/40\le R\le\sqrt{1105}/16\), with the common selected
physical certificate.

The exact graph is the triangle A,B,C together with a direct leaf
\(L_D\) at A and the two-edge arm \(A-U-L\). The direct leaf
\(L_D\) is type D. B,C retain exact positive degree two; A has
positive degree four, and its two extra forces are never discarded.
The six core bodies leave three arbitrary physical squares, all of
which remain present.

**Theorem.** This entire direct-D-leaf alternative is impossible,
for both original arm leaf types, both transmitter widths, every
physical B/C circle mask, all owners and all actual side means.
The companion direct-S-leaf alternative is not asserted here.

## 1. The full arm and articulation geometry

Put
\[
 d=\sqrt{R^2-\tfrac14}-1,\qquad
 r=R-\sqrt2,\qquad
 \delta=d-1.
\tag{1}
\]
The actual D leaf makes A contain the origin in its open interior.
The true leaf L makes U physically circle-clear. U has exact
positive degree two and therefore transmits opposite forces with
width \(w\in\{1,\sqrt2\}\). Rotate its leaf direction east.
Its leaf application is at radius \(r_L\in\{r,d\}\), and the
other actual bridge application is
\[
                           (r_L-w)e_x.
\tag{2}
\]
Since A contains0 in its interior, U cannot contain0. Equation (2)
and the actual radial channel therefore require \(r_L-w>0\).
But \(r<1\), \(d<61/60<\sqrt2\), and \(w\ge1\).
Consequently the complete arm alternative is forced to be
\[
       L\text{ is S},\qquad w=1,\qquad d>1,\qquad
       p_{AU}=(\delta,0),\quad 0<\delta<1/60.
\tag{3}
\]
U is aligned to the channel, and A lies in \(x\le\delta\).

A is aligned to this channel too. Otherwise its rightmost point
\((\delta,0)\) is a vertex. In A's own inward side frame the
two coordinates of the origin are positive and less than
\(\delta\), because the origin is interior to A. Its four side
distances from0 are therefore two numbers below \(\delta\) and
two numbers above \(1-\delta\). None equals
\[
                          \tfrac12<r<\tfrac23.
\tag{4}
\]
A radial D leaf requires a side-interior radial support at distance
r. Thus the tilted frame is impossible.

In the aligned frame, the vertical side distances are
\(\delta\) and \(1-\delta\), again different from r.
The direct D leaf is therefore north or south. Reflect to north.
The full root pose is
\[
                 A=[\delta-1,\delta]\times[r-1,r].
\tag{5}
\]
No arm mean or vertical placement of U is fixed by (5).

For later use set
\[
                         X=1-\delta,\qquad Y=1-r.
\]
The exact bounds are
\[
 \frac{59}{60}<X<1,\qquad
 \frac13<Y<\frac9{20},\qquad r>\frac{11}{20}.
\tag{6}
\]
The upper bound \(r<2/3\) follows, for example, from
\(R<52/25\) and \(\sqrt2>106/75\), both verified by squaring.
The standard bound \(r>11/20\) follows from
\(R\ge79/40\) and \(\sqrt2<57/40\).

## 2. The full triangle resultant and its actual root concurrence

B,C are loaded: an unloaded degree-two square cannot have
physically touching neighbors. They are the two exact-degree-two
tips of an end triangle, even though A has degree four.

Let \(F_B,F_C\) be their true circle resultants and put
\(M=F_B+F_C\). Sum the two actual bridge cuts and the body
equations. The arm's total circle load points east, and the
direct D leaf's load points north. Therefore
\[
                        M=-\beta e_x-\alpha e_y,
                             \qquad\alpha,\beta>0.
\tag{7}
\]
In particular M lies strictly southwest.

The full geometric and force implications in
END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md apply without changing
A's other equations. If its two triangle force lines are
nonparallel, they meet at
\[
                       q_A=-t\,\frac M{|M|}=(q_x,q_y),
                        \qquad t>0,\quad q_x,q_y>0.
\tag{8}
\]
Each actual port lies in its corresponding outward-normal
direction from \(q_A\). Also, some actual root port maximizes
the M support functional. Since M is strictly southwest,
that maximizing point is uniquely
\[
                                 P=(-X,-Y).
\tag{9}
\]
The normal at this port is strictly southwest. A left-axis
normal through P would put \(q_y=-Y<0\); a bottom-axis normal
would put \(q_x=-X<0\). Both contradict (8).

All these assertions concern the complete two-tip aggregate.
A is not assigned a degree-two equation, and no radial-leaf
formula is substituted for B,C.

## 3. Every actual root contact belongs to one left-wall family

Suppose the two root triangle normals are nonparallel.
One port is P from (9). We now exhaust its other actual port.

If the other normal is owned by A, the unit-triangle side-normal
lemma makes its dot product with the other normal nonnegative.
Its dot product with their positive sum M is consequently
strictly positive. Thus an A-owned top or right normal is
impossible by (7).

For an A-owned bottom normal, its vertical force line through
\(q_A\) gives actual application \((q_x,-Y)\), where
\(0<q_x\le\delta\). This point has norm less than \(1/2<r\):
indeed
\[
               \delta^2+Y^2
                   <\frac1{3600}+\frac{81}{400}<\frac14.
\tag{10}
\]
Every point of a boundary unit has norm at least \(R-\sqrt2=r\).
Hence no loaded tip can contain this application. The only
remaining A-owned alternative is the left normal \(-e_x\),
with its actual side mean retained.

If the other normal is not A-owned, it strictly exposes a
vertex of A. It cannot use P again, since the nonparallel
intersection would then be \(q_A=P\), contrary to (8).
It cannot use the opposite top-right vertex: opposite strictly
exposed root vertices in a physical unit triangle are excluded
by the support-span argument of
END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md, Section 2.
The bottom-right vertex \((\delta,-Y)\) is too central by (10).
Only the upper-left vertex
\[
                                  P'=(-X,r)
\tag{11}
\]
remains.

Thus the complete nonparallel cover consists of the southwest
normal at P and either a left-axis normal at an arbitrary actual
left-side mean, or a strict northwest normal at P'. This includes
tip-owned and genuinely free point contacts; neither is silently
replaced by a root axis.

The parallel-force alternative is already impossible. Opposite
normals would separate B,C beyond opposite A supports. Equal
normals must point along M, strictly southwest, and hence both
applications would be the unique vertex P. The proper radial
concurrences of the two boundary tips then lie on the same
line through P in this common direction. If they coincide,
their nonzero circle-resultant directions coincide, which is
impossible. Otherwise their connecting BC force line has that
same direction. This makes the two pair forces of each tip
parallel, contrary to the proper boundary-tip concurrence
theorem, since the tips physically touch each other.

## 4. Both surviving normals have slope strictly below1/8

Write the southwest normal and the root resultant direction as
\[
        n=(-\cos\phi,-\sin\phi),\qquad
        \frac M{|M|}=(-\cos\theta,-\sin\theta).
\tag{12}
\]
The other normal is horizontal left or northwest. Its positive
combination with n is strictly southwest, so
\[
                               0<\theta<\phi<\pi/2.
\]
From (8)--(9),
\[
          \tan\phi=\frac{Y+q_y}{X+q_x},
                     \qquad \tan\theta=\frac{q_y}{q_x}.
\]
The first is a strict weighted average of \(Y/X\) and
\(\tan\theta\). Therefore
\[
                         0<\phi<\arctan(Y/X).
\tag{13}
\]
The support height at P is
\[
                              h=X\cos\phi+Y\sin\phi.
\tag{14}
\]
It increases strictly over the interval in (13), starting at X.

Every contained unit on the other side of an actual support line
has support height at most d; see Section 1 of
OUTER_BRIDGED_TRIANGLE_EXCLUSION.md. But at
\(\phi=\arctan(1/8)\), equations (6) give
\[
 \frac{8X+Y}{\sqrt{65}}
       >\frac{41}{5\sqrt{65}}>\frac{61}{60}>d.
\tag{15}
\]
The middle comparison is exact: its squared cross-product
difference is
\(2460^2-65\cdot305^2=4975>0\).
Consequently
\[
                              \tan\phi<1/8.
\tag{16}
\]

If the other port is the upper-left vertex, write its normal
as \((-\cos\psi,\sin\psi)\). Equation (8) gives
\[
                 \tan\psi=\frac{r-q_y}{X+q_x},
                          \qquad 0<\psi<\arctan(r/X).
\]
The support \(X\cos\psi+r\sin\psi\) increases on this interval.
Since \(r>1/3\), the identical comparison (15) proves
\(\tan\psi<1/8\). For a root-owned left normal the slope is
zero. In every surviving case, each support height is at least X.

This proves the entire two-tip statement
\[
 \begin{gathered}
 n_i=(-\cos\omega_i,\ \pm\sin\omega_i),\qquad
       0\le\omega_i<\arctan(1/8),\\
                         n_i\cdot p_i\ge X>59/60 .
 \end{gathered}
\tag{17}
\]

## 5. A strict common center cap finishes the whole leaf type

For either tip center c, (17) and its half-width give
\[
                         n_i\cdot c>89/60.
\tag{18}
\]
The universal contained-unit center bound is
\[
                              |c|<91/60.
\]
Its transverse coordinate relative to \(n_i\) consequently has
absolute value less than
\[
                  \sqrt{(91/60)^2-(89/60)^2}
                             =\frac{\sqrt{10}}{10}.
\]
Equation (17) now gives
\[
 -c_x>
   \frac{178/15-\sqrt{10}/10}{\sqrt{65}}
       >\frac{308}{215}>\frac{573}{400}.
\tag{19}
\]
For the first rational comparison use
\(\sqrt{10}<19/6\) and \(\sqrt{65}<129/16\).
For the last, the exact cross-product margin is
\(308\cdot400-573\cdot215=5>0\).

Both tip centers therefore lie in
\[
                x<-573/400,\qquad |c|<91/60.
\]
This cap is contained in the disk centered at
\((-573/400,0)\) with squared radius
\((91/60)^2-(573/400)^2\). Its squared diameter is
\[
                 4\left((91/60)^2-(573/400)^2\right)
                        =\frac{357439}{360000}<1.
\tag{20}
\]
Two unit squares with disjoint open interiors have center distance
at least1, since their open inscribed disks of radius1/2 must be
disjoint. Equation (20) contradicts that necessary separation.

This excludes the entire direct-D-leaf / length-two-arm alternative,
with every true root force, circle mask and actual mean retained.
It does not assume any placement of the three additional units,
nor use a secondary minimizer, numerical pose sampling, Lean or CI.

